#!/usr/bin/env python3
"""Exercise ordinary unverified path intake using only synthetic missing Git blobs.

This deliberately does not run preflight, a compiler build, a whole-tree retainer,
or a verifier. Each Targo child uses the maintained build-slot/process owner.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import runpy
import subprocess
import sys
import time

sys.dont_write_bytecode = True


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--toolchain', type=Path, required=True)
    ap.add_argument('--git', required=True)
    ap.add_argument('--python', required=True)
    ap.add_argument('--build-slot', type=Path, required=True)
    ap.add_argument('--resource-helper', type=Path, required=True)
    ap.add_argument('--process-helpers', type=Path, required=True)
    ap.add_argument('--protected-metadata', type=Path, required=True)
    args = ap.parse_args()
    out = args.output.resolve()
    assert not out.exists(), 'Output must be a new isolated directory'
    out.mkdir(parents=True)
    crate = out / 'crate'
    crate.mkdir()
    target = out / 'target.noindex'
    cargo_home = out / 'cargo-home'
    cargo_home.mkdir()
    protected_record = json.loads(args.protected_metadata.read_text())
    protected = set(protected_record.get('protected_OID_union', protected_record.get('protected_OIDs', [])))
    assert len(protected) == 19
    sys.path.insert(0, str(args.process_helpers))
    import owned_processes as owned
    resource = runpy.run_path(str(args.resource_helper))
    git_env = dict(os.environ, GIT_CONFIG_NOSYSTEM='1', GIT_CONFIG_GLOBAL=os.devnull,
                   GIT_NO_REPLACE_OBJECTS='1', GIT_GRAFT_FILE=os.devnull,
                   GIT_NO_LAZY_FETCH='1', GIT_TERMINAL_PROMPT='0')
    git_calls = []
    sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()

    def save(path, value):
        path.write_text(json.dumps(value, indent=2) + '\n')

    setup_launch_pins = {str(p): sha(p) for p in [Path(__file__), Path(args.python), Path(args.git)]}
    save(out / 'setup-launch-pins.json', setup_launch_pins)

    def git(*argv, check=True):
        assert all(sha(p) == digest for p, digest in setup_launch_pins.items())
        r = subprocess.run([args.git, '-C', str(crate), *argv], env=git_env, capture_output=True)
        assert all(sha(p) == digest for p, digest in setup_launch_pins.items())
        git_calls.append(dict(argv=list(argv), returncode=r.returncode,
                              stdout=r.stdout.decode(errors='replace'), stderr=r.stderr.decode(errors='replace')))
        save(out / 'git-commands.json', git_calls)
        if check:
            assert r.returncode == 0, git_calls[-1]
        return r

    files = {
        '.gitignore': b'/target.noindex/\n',
        'Cargo.toml': b'[package]\nname = "synthetic-path-intake"\nversion = "0.0.0"\nedition = "2021"\n\n[lib]\npath = "src/lib.rs"\n',
        'Cargo.lock': b'version = 4\n\n[[package]]\nname = "synthetic-path-intake"\nversion = "0.0.0"\n',
        'src/lib.rs': b'pub fn answer() -> u8 { include_bytes!("required.bin")[0] }\n',
        'src/required.bin': b'A',
        'fixtures/omitted-a.dat': b'Synthetic missing non-source fixture for path-intake controls.\n',
        'fixtures/omitted-b.dat': b'Synthetic missing non-source fixture for path-intake controls.\n',
    }
    for name, body in files.items():
        oid = hashlib.sha1(b'blob ' + str(len(body)).encode() + b'\0' + body).hexdigest()
        assert oid not in protected
        p = crate / name
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(body)
    git('init', '-q')
    git('config', 'user.name', 'Synthetic path intake')
    git('config', 'user.email', 'synthetic-intake@invalid.example')
    git('add', '--', *files)
    git('commit', '-qm', 'Synthetic path-source fixture')
    head = git('rev-parse', 'HEAD').stdout.decode().strip()
    all_oids = {row.split(b'\t', 1)[0].split()[2].decode()
                for row in git('ls-tree', '-r', '-z', 'HEAD').stdout.split(b'\0') if row}
    assert not (all_oids & protected)
    aliases = ['fixtures/omitted-a.dat', 'fixtures/omitted-b.dat']
    oid = git('rev-parse', 'HEAD:' + aliases[0]).stdout.decode().strip()
    assert git('rev-parse', 'HEAD:' + aliases[1]).stdout.decode().strip() == oid
    assert git('remote').stdout == b''
    assert not (crate / '.git/objects/info/alternates').exists()
    assert not list((crate / '.git/objects/pack').iterdir())
    git('update-index', '--skip-worktree', '--', *aliases)
    for name in aliases:
        (crate / name).unlink()
    loose = crate / '.git/objects' / oid[:2] / oid[2:]
    assert loose.is_file()
    loose.unlink()

    def absence():
        assert not loose.exists()
        assert not (crate / '.git/objects/info/alternates').exists()
        assert not list((crate / '.git/objects/pack').iterdir())
        assert git('remote').stdout == b''
        assert all(not (crate / p).exists() for p in aliases)
        assert git('cat-file', '-e', oid, check=False).returncode != 0
        flags = git('ls-files', '-v', '--', *aliases).stdout.decode().splitlines()
        assert len(flags) == 2 and all(x.startswith('S ') for x in flags)
        return dict(synthetic_oid=oid, paths=aliases, body_unavailable_in_worktree_and_ODB=True,
                    no_remotes_or_alternates_or_packs=True, skip_worktree=flags)

    save(out / 'synthetic-setup.json', dict(head=head, protected_OIDs=sorted(protected),
         synthetic_tree_OIDs_disjoint=True, aliases=absence(), fixture_files=sorted(files)))
    toolchain = args.toolchain.resolve()
    pinned = {str(p): sha(p) for p in [Path(__file__), toolchain / 'bin/targo', toolchain / 'bin/trustc',
              toolchain / 'PROVENANCE', toolchain / 'tool-provenance.json', toolchain / 'SEED-MINT',
              toolchain / 'LINEAGE', Path(args.python), Path(args.git),
              args.build_slot, args.resource_helper,
              *(args.process_helpers / n for n in ['owned_processes.py', 'session_owner.py', 'native_request_channel.py'])]}
    for p in (toolchain / 'lib').rglob('*'):
        if p.is_file() and not p.is_symlink() and p.suffix in ['.rlib', '.rmeta', '.dylib', '.a', '.json']:
            pinned[str(p)] = sha(p)
    save(out / 'pinned-inputs.json', pinned)
    env = dict(git_env, CARGO_HOME=str(cargo_home), CARGO_TARGET_DIR=str(target), CARGO_BUILD_JOBS='1',
               RUSTC=str(toolchain / 'bin/trustc'), DEVELOPER_DIR='/Library/Developer/CommandLineTools',
               CARGO_LOG='targo_core::sources::path=trace,targo_core::core::compiler::fingerprint=trace,cargo::sources::path=trace,cargo::core::compiler::fingerprint=trace')
    assert 'RUSTFLAGS' not in env and 'CARGO_ENCODED_RUSTFLAGS' not in env
    results = []

    def phase(name, operation='compile'):
        directory = out / name
        directory.mkdir()
        before = {p: sha(crate / p) for p in files if (crate / p).exists()}
        a = absence()
        command = [str(toolchain / 'bin/targo'), '--unverified']
        if operation == 'package':
            command += ['package', '--list', '--offline', '--frozen']
        else:
            command += ['rustc', '--lib', '--offline', '--frozen', '--jobs=1', '--message-format=json']
        command += ['--manifest-path', str(crate / 'Cargo.toml')]
        argv = [args.python, str(args.build_slot), '--cpus', '1', '--wait-timeout', '3600', '--', *command]
        state = dict(name=name, argv=argv, cwd=str(crate), sources=before, aliases_before=a,
                     source_HEAD=head, complete=False, started=time.time(), controller_pid=os.getpid())
        save(directory / 'command.json', state)
        t = time.monotonic()
        with owned.scope() as scope:
            scope.record_path = directory / 'lifetimes.json'
            with (directory / 'stdout').open('wb') as stdout, (directory / 'stderr').open('wb') as stderr:
                r = owned.run(argv, cwd=crate, env=env, stdout=stdout, stderr=stderr,
                              pass_fds=resource['resource_fds'](env))
        assert before == {p: sha(crate / p) for p in before}
        assert all(sha(p) == expected for p, expected in pinned.items())
        state.update(complete=True, returncode=r.returncode, seconds=time.monotonic()-t,
                     aliases_after=absence(), pins_unchanged=True, actual_direct_wait=True,
                     finished=time.time(), artifacts=[], compiler_diagnostics=[], cargo_diagnostics=[])
        for line in (directory / 'stdout').read_text(errors='replace').splitlines():
            try:
                row = json.loads(line)
            except ValueError:
                continue
            if row.get('reason') == 'compiler-message':
                state['compiler_diagnostics'].append(row)
            if row.get('reason') == 'compiler-artifact':
                state['artifacts'].append(dict(row=row, files={p:sha(p) for p in row['filenames']}))
        stderr_lines = (directory / 'stderr').read_text(errors='replace').splitlines()
        for index, line in enumerate(stderr_lines):
            if line.startswith('error: '):
                following = stderr_lines[index + 1] if index + 1 < len(stderr_lines) else ''
                state['cargo_diagnostics'].append(dict(
                    message=line.removeprefix('error: '),
                    manifest=following.removeprefix(' --> ') if following.startswith(' --> ') else None))
        save(directory / 'command.json', state)
        results.append(state)
        save(out / 'progress.json', results)
        print(json.dumps(dict(phase=name, returncode=r.returncode, artifacts=len(state['artifacts']), seconds=state['seconds'])), flush=True)
        return state

    package = phase('package-list', 'package')
    assert package['returncode'] == 0, 'package --list must actually succeed'
    baseline = phase('baseline')
    assert baseline['returncode'] == 0 and len(baseline['artifacts']) == 1
    again = phase('unchanged')
    assert again['returncode'] == 0 and again['artifacts'][0]['row']['fresh']
    assert again['artifacts'][0]['files'] == baseline['artifacts'][0]['files']
    # Make a native required-input edit, and then a source edit, only after closure.
    (crate / 'src/required.bin').write_bytes(b'B')
    include_edit = phase('required-input-edit')
    assert include_edit['returncode'] == 0 and not include_edit['artifacts'][0]['row']['fresh']
    assert include_edit['artifacts'][0]['files'] != baseline['artifacts'][0]['files']
    (crate / 'src/lib.rs').write_bytes(b'pub fn answer() -> u8 { include_bytes!("required.bin")[0] + 1 }\n')
    source_edit = phase('source-edit')
    assert source_edit['returncode'] == 0 and not source_edit['artifacts'][0]['row']['fresh']
    assert source_edit['artifacts'][0]['files'] != include_edit['artifacts'][0]['files']
    (crate / 'src/required.bin').unlink()
    missing_include = phase('missing-required-input')
    assert missing_include['returncode'] == 101 and not missing_include['artifacts']
    errors = [row for row in missing_include['compiler_diagnostics']
              if row.get('message', {}).get('level') == 'error']
    assert len(errors) == 1, 'the missing input must produce exactly its native compiler error'
    error = errors[0]
    assert error['manifest_path'] == str(crate / 'Cargo.toml')
    assert error['target']['src_path'] == str(crate / 'src/lib.rs')
    assert error['message']['$message_type'] == 'diagnostic'
    assert error['message']['message'] == "couldn't read `src/required.bin`: No such file or directory (os error 2)"
    primary = [s for s in error['message']['spans'] if s['is_primary']]
    assert len(primary) == 1 and primary[0]['file_name'] == 'src/lib.rs'
    assert primary[0]['line_start'] == primary[0]['line_end'] == 1
    assert 0 <= primary[0]['byte_start'] < primary[0]['byte_end'] <= (crate / 'src/lib.rs').stat().st_size
    (crate / 'src/lib.rs').unlink()
    missing_source = phase('missing-required-source')
    assert missing_source['returncode'] == 101 and not missing_source['artifacts']
    assert not missing_source['compiler_diagnostics']
    assert missing_source['cargo_diagnostics'] == [
        dict(message=f"can't find lib `synthetic_path_intake` at path `{crate / 'src/lib.rs'}`",
             manifest=str(crate / 'Cargo.toml')),
        dict(message='could not compile due to 1 previous target resolution error', manifest=None),
    ], 'require the actual missing-library target-resolution diagnostic, not arbitrary failure'
    final = dict(scope='Only actual synthetic ordinary path intake; no whole-source/build-script/readiness or proof claim',
                 passed=True, phases=len(results), package_list_returncode=package['returncode'],
                 explicit_package_success_and_native_missing_reasons_checked=True,
                 protected_OIDs_disjoint=True, real_held_bodies_read_or_copied=False,
                 final_aliases=absence(), pins_unchanged=True, source_restoration=False,
                 all_commands_closed=True, results=[dict(name=r['name'], returncode=r['returncode']) for r in results])
    save(out / 'RESULT.json', final)
    print(json.dumps(final), flush=True)


if __name__ == '__main__':
    main()
