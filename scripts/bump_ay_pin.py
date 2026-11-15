#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Adopt a published same-version AY revision without changing the package graph.

This owns the four direct selectors and tracked locks. It does not qualify
solver behavior: the ordinary affected consumer checks remain required.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import time
import tomllib

from bump_trust_ir_pin import atomic
from pin_git import ObjectStore, environment

AY = 'https://github.com/alabsystems/ay.git'
CRATES = ('ay-core', 'ay-dpll', 'ay-frontend', 'ay-sys')
SHA = re.compile('[0-9a-f]{40}\\Z')


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def selectors(document):
    deps = document['workspace']['dependencies']
    chosen = [deps[name] for name in CRATES]
    require(all(d.get('git') == AY and not any(k in d for k in ('path', 'branch', 'tag', 'package'))
                for d in chosen), 'AY selectors must use the canonical immutable source')
    revisions = {d.get('rev') for d in chosen}
    versions = {d.get('version') for d in chosen}
    require(len(revisions) == len(versions) == 1, 'AY selectors disagree')
    revision, version = next(iter(revisions)), next(iter(versions))
    require(isinstance(revision, str) and SHA.fullmatch(revision), 'full immutable AY revision required')
    require(isinstance(version, str) and version, 'explicit AY package version required')
    return revision, version


def graph(data, old, new):
    packages = copy.deepcopy(tomllib.loads(data.decode())['package'])
    before, after = (f'git+{AY}?rev={r}#{r}' for r in (old, new))
    old_edge, new_edge = (f' (git+{AY}?rev={r})' for r in (old, new))
    for package in packages:
        if package.get('source') == before:
            package['source'] = after
        if 'dependencies' in package:
            package['dependencies'] = [d[:-len(old_edge)] + new_edge if d.endswith(old_edge) else d
                                       for d in package['dependencies']]
    return sorted(json.dumps(p, sort_keys=True) for p in packages)


def inventory(root, names, excluded):
    result = {}
    for name in names:
        if Path(name) in excluded:
            continue
        path = root / name
        try:
            mode = path.lstat().st_mode
        except FileNotFoundError:
            result[name] = {'missing': True}
            continue
        require(stat.S_ISREG(mode) or stat.S_ISLNK(mode), f'unsupported source file: {name}')
        data = os.fsencode(os.readlink(path)) if stat.S_ISLNK(mode) else path.read_bytes()
        result[name] = dict(mode=mode, sha256=hashlib.sha256(data).hexdigest())
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('revision')
    parser.add_argument('--ay-git-dir', required=True, type=Path)
    parser.add_argument('--ay-source-root', type=Path,
                        help='owned AY repository view for the normal native main source binding')
    parser.add_argument('--targo', required=True, type=Path)
    parser.add_argument('--agh', required=True, type=Path)
    parser.add_argument('--evidence-dir', required=True, type=Path)
    args = parser.parse_args()
    require(SHA.fullmatch(args.revision), 'full immutable AY revision required')
    require(args.targo.is_absolute() and os.access(args.targo, os.X_OK), 'explicit operational Targo required')
    require(args.agh.is_absolute() and os.access(args.agh, os.X_OK), 'explicit native Agh required')
    root = Path(__file__).resolve().parent.parent
    out = args.evidence_dir.resolve()
    require(not out.is_relative_to(root), 'keep transaction evidence outside the source checkout')
    out.mkdir(parents=True, exist_ok=False)
    record = dict(revision=args.revision, started=time.time(), scope='same-version source transaction only', runs=[])

    def save():
        (out / 'record.json').write_text(json.dumps(record, indent=2) + '\n')

    def git(*a):
        return subprocess.check_output(['git', *a], cwd=root, env=environment()).decode().rstrip('\n')

    def run(a, cwd=root, expected=(0,)):
        index = len(record['runs']);started = time.monotonic()
        row = dict(argv=list(map(str, a)), cwd=str(cwd), expected_exit=list(expected));record['runs'].append(row);save()
        with (out / f'{index:02d}.stdout').open('wb') as stdout, (out / f'{index:02d}.stderr').open('wb') as stderr:
            result = subprocess.run(a, cwd=cwd, env=environment(), stdout=stdout, stderr=stderr)
        row.update(exit=result.returncode, seconds=time.monotonic()-started);save()
        require(result.returncode in expected, f'command failed; see {out}/{index:02d}.stderr')
        return (out / f'{index:02d}.stdout').read_bytes()

    before = {}
    try:
        require(run([args.targo, '--unverified', '--version']).startswith(b'targo '), 'wrong Targo frontend')
        manifest = (root / 'Cargo.toml').read_bytes()
        old, version = selectors(tomllib.loads(manifest.decode()))
        store = ObjectStore(args.ay_git_dir, args.revision)
        target = tomllib.loads(store.read('Cargo.toml').decode())['workspace']['package']['version']
        require(target == version, 'AY package-version migrations require a separate reviewed change')
        source_root = args.ay_source_root or args.ay_git_dir
        source_common = Path(run(['git', '-C', str(source_root), 'rev-parse',
                                 '--path-format=absolute', '--git-common-dir']).decode().strip())
        require(os.path.samefile(source_common, args.ay_git_dir), 'AY source view and immutable object store disagree')
        # This is the same guarded authenticated source binding used by the
        # native lander. A refusal is terminal; never consume a stale local ref.
        run([args.agh, 'repo', 'fetch-main', 'alabsystems/ay', source_root])
        run(['git', '--git-dir', str(args.ay_git_dir), 'symbolic-ref', '--quiet',
             'refs/agh/fetched-main'], expected=(1,))
        tip = run(['git', '--git-dir', str(args.ay_git_dir), 'rev-parse', '--verify',
                   'refs/agh/fetched-main']).decode().strip()
        require(SHA.fullmatch(tip), 'invalid canonical AY main identity')
        # The authenticated main identity supplies publication authority. Exact
        # original local objects supply the parent-edge proof; a second REST
        # representation adds no ancestry authority and needlessly spends quota.
        # Missing/corrupt objects refuse before any selector is changed.
        record.update(public_main=tip, main_binding='native Agh repo fetch-main',
                      source_common=str(source_common));save()
        record['local_ancestry'] = [dict(base=base, head=head, path=store.ancestry_path(base, head))
                                    for base, head in [(old, args.revision), (args.revision, tip)]]
        record['selected_source'] = store.verify_selected_tree();save()
        locks = [Path(p) for p in git('ls-files', '*Cargo.lock').splitlines()]
        require(Path('Cargo.lock') in locks, 'tracked root lock required')
        controlled = [Path('Cargo.toml'), *locks]
        before = {}
        for relative in controlled:
            p = root / relative;st = p.lstat()
            require(p.is_file() and not p.is_symlink() and st.st_nlink == 1, f'unsafe controlled file: {relative}')
            before[relative] = (p.read_bytes(), st.st_mode & 0o777)
        def source_inventory():
            names = set(git('ls-files', '-z', '--cached', '--others', '--exclude-standard').split('\0')) - {''}
            return inventory(root, names, before)

        source = source_inventory()
        head, index = git('rev-parse', 'HEAD'), git('diff', '--cached', '--binary')
        record.update(old=old, version=version, public_main=tip, head=head, source_inventory=source)
        save()
        require(manifest.count(old.encode()) == len(CRATES), 'unexpected AY selector occurrences')
        atomic(root / 'Cargo.toml', manifest.replace(old.encode(), args.revision.encode()), before[Path('Cargo.toml')][1])
        for lock in locks:
            cwd = root / lock.parent
            raw = run([args.targo, 'metadata', '--offline', '--format-version', '1'], cwd)
            require(b'was not used' not in (out / f'{len(record["runs"])-1:02d}.stderr').read_bytes(), 'unused dependency patch')
            metadata = json.loads(raw)
            ay = [p for p in metadata['packages'] if p['name'] == 'ay' or p['name'].startswith('ay-')]
            if lock == Path('Cargo.lock'):
                require(set(CRATES) <= {p['name'] for p in ay}, 'root metadata omitted a direct AY package')
            require(all(p['source'] == f'git+{AY}?rev={args.revision}#{args.revision}' and p['version'] == version
                        for p in ay), 'mixed, redirected or wrong-version AY source')
            require(graph(before[lock][0], old, args.revision) == graph((root / lock).read_bytes(), args.revision, args.revision),
                    f'unrelated package node, edge or checksum changed: {lock}')
            run([args.targo, 'metadata', '--offline', '--locked', '--format-version', '1'], cwd)
        require(source_inventory() == source and git('rev-parse', 'HEAD') == head
                and git('diff', '--cached', '--binary') == index, 'source or index changed during adoption')
        record.update(exit=0, terminal=True, finished=time.time());save()
    except BaseException as error:
        for relative, (data, mode) in before.items():atomic(root / relative, data, mode)
        record.update(exit=1, terminal=True, restored=True, error=repr(error), finished=time.time());save()
        raise


if __name__ == '__main__':
    main()
