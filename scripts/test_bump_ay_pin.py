#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
import json
from pathlib import Path
import shutil
import shlex
import stat
import subprocess
import sys
import tempfile
import tomllib
import unittest
from bump_ay_pin import AY, CRATES, graph, inventory, selectors
from pin_git import environment


class SourceGraphTests(unittest.TestCase):
    def manifest(self):
        return {'workspace': {'dependencies': {name: dict(git=AY, rev='a'*40, version='0.28.0') for name in CRATES}}}

    def test_all_selectors_must_name_one_immutable_source(self):
        self.assertEqual(selectors(self.manifest()), ('a'*40, '0.28.0'))
        for key, value in [('path', '../ay'), ('branch', 'main'), ('git', 'https://elsewhere.invalid/ay'), ('rev', 'main'), ('version', '0.27.0')]:
            m = self.manifest();m['workspace']['dependencies']['ay-core'][key] = value
            with self.assertRaises(RuntimeError):selectors(m)

    def test_graph_moves_exact_source_and_source_qualified_edges_only(self):
        old, new = 'a'*40, 'b'*40
        def lock(rev, checksum='fixed', edge='ay-core'):
            return ('[[package]]\nname="ay-core"\nversion="0.28.0"\nsource="git+'+AY+'?rev='+rev+'#'+rev+'"\n'
                    '[[package]]\nname="consumer"\nversion="1.0.0"\ndependencies=["'+edge+' 0.28.0 (git+'+AY+'?rev='+rev+')"]\n'
                    '[[package]]\nname="registry"\nversion="1.0.0"\nsource="registry+https://github.com/rust-lang/crates.io-index"\nchecksum="'+checksum+'"\n').encode()
        self.assertEqual(graph(lock(old), old, new), graph(lock(new), new, new))
        self.assertNotEqual(graph(lock(old), old, new), graph(lock(new, 'changed'), new, new))
        self.assertNotEqual(graph(lock(old), old, new), graph(lock(new, edge='ay-sys'), new, new))
        self.assertNotEqual(graph(lock(old), old, new), graph(lock(new).replace(b'0.28.0', b'0.29.0'), new, new))


class SourceInventoryTests(unittest.TestCase):
    def test_inventory_detects_contents_modes_new_files_and_deletions(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'source.rs'
            source.write_bytes(b'original source\n')
            source.chmod(0o640)
            names = {'source.rs'}
            before = inventory(root, names, set())
            source.write_bytes(b'changed source\n')
            self.assertNotEqual(before, inventory(root, names, set()))
            source.write_bytes(b'original source\n')
            self.assertEqual(before, inventory(root, names, set()))
            source.chmod(0o600)
            self.assertNotEqual(before, inventory(root, names, set()))
            source.chmod(0o640)
            added = root / 'added.rs'
            added.write_bytes(b'new source\n')
            self.assertNotEqual(before, inventory(root, names | {'added.rs'}, set()))
            self.assertEqual(before, inventory(root, names | {'added.rs'}, {Path('added.rs')}))
            source.unlink()
            missing = inventory(root, names, set())
            self.assertEqual(missing['source.rs'], {'missing': True})
            self.assertNotEqual(before, missing)

    def test_inventory_hashes_symlink_identity_without_following_it(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ('first.rs', 'second.rs'):
                (root / name).write_bytes(b'identical target bytes\n')
            link = root / 'source.rs'
            link.symlink_to('first.rs')
            before = inventory(root, {'source.rs'}, set())
            self.assertTrue(stat.S_ISLNK(before['source.rs']['mode']))
            (root / 'first.rs').write_bytes(b'target changes are separate source entries\n')
            self.assertEqual(before, inventory(root, {'source.rs'}, set()))
            link.unlink()
            link.symlink_to('second.rs')
            self.assertNotEqual(before, inventory(root, {'source.rs'}, set()))
            link.unlink()
            link.symlink_to('missing.rs')
            self.assertNotEqual(before, inventory(root, {'source.rs'}, set()))


class TransactionFailureTests(unittest.TestCase):
    """Synthetic CLI doubles exercise the source transaction, never a proof."""

    def fixture(self, root, target_version='0.28.0'):
        ay = root / 'immutable-ay'
        vc = root / 'vc'
        ay.mkdir()
        vc.mkdir()

        def git(repository, *arguments):
            return subprocess.check_output(
                ['git', '-C', str(repository), *arguments], env=environment(), stderr=subprocess.PIPE
            ).decode().strip()

        def commit(repository, message):
            git(repository, 'add', '.')
            git(repository, '-c', 'user.name=AY owner test',
                '-c', 'user.email=ay-owner-test@invalid.example', 'commit', '-qm', message)
            return git(repository, 'rev-parse', 'HEAD')

        git(ay, 'init', '-q')
        manifest = ay / 'Cargo.toml'
        manifest.write_text('[workspace.package]\nversion = "0.28.0"\n')
        old = commit(ay, 'Initial synthetic source')
        manifest.write_text(f'[workspace.package]\nversion = "{target_version}"\n')
        (ay / 'source-marker').write_text('Distinct immutable target source\n')
        new = commit(ay, 'Synthetic target source')

        scripts = vc / 'scripts'
        scripts.mkdir()
        source_scripts = Path(__file__).resolve().parent
        for name in ('bump_ay_pin.py', 'bump_trust_ir_pin.py', 'pin_git.py'):
            shutil.copy2(source_scripts / name, scripts / name)
        vc_manifest = vc / 'Cargo.toml'
        vc_manifest.write_text('[workspace]\nmembers = []\n[workspace.dependencies]\n' + ''.join(
            f'{name} = {{ git = "{AY}", rev = "{old}", version = "0.28.0" }}\n'
            for name in CRATES
        ))
        lock = vc / 'Cargo.lock'
        lock.write_bytes(b'version = 4\n[[package]]\nname = "consumer"\nversion = "0.1.0"\n')
        vc_manifest.chmod(0o640)
        lock.chmod(0o604)
        git(vc, 'init', '-q')
        commit(vc, 'Synthetic consumer transaction fixture')

        tools = root / 'synthetic-tools'
        tools.mkdir()
        targo = tools / 'targo'
        # This deliberately cannot compile or solve anything. Metadata proves
        # that the manifest moved before corrupting the lock and failing.
        targo_body = (
            'import pathlib,sys\n' +
            'if sys.argv[1:] == ["--unverified", "--version"]:\n'
            ' print("targo synthetic transaction test");sys.exit(0)\n' +
            'if sys.argv[1:2] == ["metadata"]:\n' +
            f' assert pathlib.Path("Cargo.toml").read_text().count({new!r}) == 4\n' +
            ' lock=pathlib.Path("Cargo.lock")\n'
            ' lock.write_bytes(b"deliberately changed by synthetic metadata\\n")\n'
            ' lock.chmod(0o600)\n'
            ' print("synthetic metadata changed lock bytes and mode",flush=True)\n'
            ' sys.exit(42)\n'
            'sys.exit("unexpected synthetic Targo invocation")\n')
        agh = tools / 'agh'
        agh_body = (
            'import subprocess,sys\n'
            'assert sys.argv[1:4] == ["repo", "fetch-main", "alabsystems/ay"]\n' +
            f'tip={new!r}\n' +
            'subprocess.run(["git", "-C", sys.argv[4], "update-ref", "refs/agh/fetched-main", tip], check=True)\n')
        # A managed Python can itself live under Application Support. Keep
        # that exact interpreter without an invalid space-containing shebang.
        for executable, body in ((targo, targo_body), (agh, agh_body)):
            payload = executable.with_suffix('.py')
            payload.write_text(body)
            executable.write_text('#!/bin/sh\nexec '+shlex.quote(sys.executable)+' '
                                  +shlex.quote(str(payload))+' "$@"\n')
            executable.chmod(0o700)
        command = [sys.executable, str(scripts / 'bump_ay_pin.py'), new,
                   '--ay-git-dir', str(ay / '.git'), '--ay-source-root', str(ay), '--targo', str(targo),
                   '--agh', str(agh), '--evidence-dir', str(root / 'evidence')]
        controlled = {path: (path.read_bytes(), stat.S_IMODE(path.stat().st_mode))
                      for path in (vc_manifest, lock)}
        return command, vc, controlled

    def assert_restored(self, controlled):
        for path, (contents, mode) in controlled.items():
            with self.subTest(path=path.name):
                self.assertEqual(path.read_bytes(), contents)
                self.assertEqual(stat.S_IMODE(path.stat().st_mode), mode)

    def test_failed_metadata_restores_all_controlled_bytes_and_modes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            command, vc, controlled = self.fixture(root)
            result = subprocess.run(command, cwd=vc, env=environment(), capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0, result.stdout)
            record = json.loads((root / 'evidence' / 'record.json').read_text())
            self.assertTrue(record['terminal'])
            self.assertEqual(record['exit'], 1)
            self.assertTrue(record['restored'])
            metadata = [(index, row) for index, row in enumerate(record['runs'])
                        if row['argv'][1:2] == ['metadata']]
            self.assertEqual(len(metadata), 1, result.stderr)
            index, row = metadata[0]
            self.assertEqual(row['exit'], 42)
            self.assertIn('changed lock bytes and mode',
                          (root / 'evidence' / f'{index:02d}.stdout').read_text())
            self.assert_restored(controlled)

    def test_wrong_version_refusal_records_terminal_preflight_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            command, vc, controlled = self.fixture(root, target_version='0.29.0')
            result = subprocess.run(command, cwd=vc, env=environment(), capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0, result.stdout)
            record = json.loads((root / 'evidence' / 'record.json').read_text())
            self.assertTrue(record['terminal'])
            self.assertEqual(record['exit'], 1)
            self.assertTrue(record['restored'])
            self.assertIn('package-version migrations require a separate reviewed change', record['error'])
            self.assertFalse(any(row['argv'][1:2] == ['metadata'] for row in record['runs']))
            self.assert_restored(controlled)

    def test_exact_local_ancestry_uses_only_the_fresh_public_main_binding(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            command, vc, controlled = self.fixture(root)
            # The main identity is the only external authority input. Local
            # exact parent objects must supply both ancestry relations.
            result = subprocess.run(command, cwd=vc, env=environment(), capture_output=True, text=True)
            record = json.loads((root / 'evidence/record.json').read_text())
            self.assertNotEqual(result.returncode, 0)  # synthetic metadata deliberately refuses
            self.assertEqual(len(record['local_ancestry']), 2)
            self.assertEqual(record['local_ancestry'][1]['path'], [record['revision']])
            self.assertEqual(record['selected_source']['blobs'], 2)
            self.assertEqual(record['main_binding'], 'native Agh repo fetch-main')
            self.assertFalse(any(r['argv'][1:2] == ['api'] for r in record['runs']))
            self.assertTrue(any(r['exit'] == 42 for r in record['runs']))
            self.assert_restored(controlled)

    def test_local_refs_cannot_select_a_revision_outside_authenticated_main(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            command, vc, controlled = self.fixture(root)
            old = selectors(tomllib.loads((vc / 'Cargo.toml').read_text()))[0]
            agh = Path(command[command.index('--agh') + 1]).with_suffix('.py')
            agh.write_text(agh.read_text().replace(f'tip={command[2]!r}', f'tip={old!r}'))
            result = subprocess.run(command, cwd=vc, env=environment(), capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            record = json.loads((root / 'evidence/record.json').read_text())
            self.assertIn('does not advance', record['error'])
            self.assertFalse(any(r['argv'][1:2] == ['metadata'] for r in record['runs']))
            self.assert_restored(controlled)

    def test_native_source_refusal_cannot_reuse_a_stale_main_ref(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            command, vc, controlled = self.fixture(root)
            source = root / 'immutable-ay'
            subprocess.run(['git', '-C', str(source), 'update-ref', 'refs/agh/fetched-main', command[2]],
                           env=environment(), check=True)
            agh = Path(command[command.index('--agh') + 1]).with_suffix('.py')
            agh.write_text('import sys\nsys.exit(11)\n')
            result = subprocess.run(command, cwd=vc, env=environment(), capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            record = json.loads((root / 'evidence/record.json').read_text())
            self.assertEqual(record['runs'][-1]['exit'], 11)
            self.assertNotIn('public_main', record)
            self.assertFalse(any(r['argv'][1:2] == ['metadata'] for r in record['runs']))
            self.assert_restored(controlled)


if __name__ == '__main__':unittest.main()
