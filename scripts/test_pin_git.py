#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Actual local Git integrity controls, no network/compiler/proof doubles."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
import zlib
from unittest.mock import patch
import pin_git


class ObjectStoreTests(unittest.TestCase):
    def setUp(self):
        base = Path(tempfile.gettempdir()) / ".ubd"
        base.mkdir(exist_ok=True)
        self.tmp = tempfile.TemporaryDirectory(dir=base, prefix="vc-pin-git-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.repo = self.root / "repo"
        subprocess.run(["git", "init", "--bare", "--template=", "--object-format=sha1", str(self.repo)],
                       env=pin_git.environment(), check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.env = {**pin_git.environment(), "GIT_AUTHOR_NAME": "Fixture", "GIT_AUTHOR_EMAIL": "fixture@example.invalid",
                    "GIT_COMMITTER_NAME": "Fixture", "GIT_COMMITTER_EMAIL": "fixture@example.invalid"}
        self.good = self.commit(b'[workspace.package]\r\nversion="1"\r\n')
        self.bad = self.commit(b'[workspace.package]\nversion="wrong"\n')

    def git(self, *args, data=None):
        return subprocess.check_output(["git", "--git-dir", str(self.repo), *args], input=data, env=self.env).strip()

    def commit(self, contents, name=b"Cargo.toml", mode=b"100644", parent=None):
        blob = self.git("hash-object", "-w", "--stdin", data=contents)
        tree = self.git("mktree", data=mode+b" blob "+blob+b"\t"+name+b"\n")
        parents = ["-p", parent] if parent else []
        return self.git("commit-tree", tree.decode(), *parents, "-m", contents.decode()).decode()

    def object_path(self, identity):
        return self.repo / "objects" / identity[:2] / identity[2:]

    def test_original_parent_path_and_complete_selected_source_are_checked(self):
        child = self.commit(b"published source", parent=self.good)
        tip = self.commit(b"current public main", parent=child)
        store = pin_git.ObjectStore(self.repo, child)
        self.assertEqual(store.ancestry_path(self.good, tip), [self.good, child, tip])
        self.assertEqual(store.ancestry_path(child, child), [child])
        closure = store.verify_selected_tree()
        self.assertEqual((closure['trees'], closure['blobs']), (1, 1))
        self.assertEqual(closure['tree'], store.tree)
        with self.assertRaisesRegex(RuntimeError, "does not advance"):
            store.ancestry_path(self.bad, child)

    def test_cold_or_incomplete_metadata_is_unjudged(self):
        child = self.commit(b"published source", parent=self.good)
        store = pin_git.ObjectStore(self.repo, child)
        with self.assertRaisesRegex(RuntimeError, "not judged"):
            store.ancestry_path('f'*40, 'f'*40)
        self.object_path(self.good).unlink()
        with self.assertRaisesRegex(RuntimeError, "not judged"):
            store.ancestry_path(self.good, child)

    def test_unrelated_historical_blobs_are_not_required(self):
        child = self.commit(b"published source", parent=self.good)
        historical = self.git('rev-parse', self.good+':Cargo.toml').decode()
        self.object_path(historical).unlink()
        store = pin_git.ObjectStore(self.repo, child)
        self.assertEqual(store.ancestry_path(self.good, child), [self.good, child])
        self.assertEqual(store.verify_selected_tree()['blobs'], 1)

    def test_missing_selected_blob_or_tree_is_unjudged(self):
        for kind in ('blob', 'tree'):
            with self.subTest(kind=kind):
                child = self.commit(('selected '+kind).encode(), parent=self.good)
                identity = self.git('rev-parse', child+(':Cargo.toml' if kind == 'blob' else '^{tree}')).decode()
                store = pin_git.ObjectStore(self.repo, child)
                self.object_path(identity).unlink()
                with self.assertRaisesRegex(RuntimeError, "not judged"):
                    store.verify_selected_tree()

    def test_actual_corrupt_selected_object_is_refused(self):
        child = self.commit(b"original source", parent=self.good)
        blob = self.git('rev-parse', child+':Cargo.toml').decode()
        self.object_path(blob).chmod(0o600)
        self.object_path(blob).write_bytes(zlib.compress(b'blob 15\0corrupted bytes'))
        with self.assertRaisesRegex(RuntimeError, "Git identity"):
            pin_git.ObjectStore(self.repo, child).verify_selected_tree()

    def test_replacement_cannot_invent_or_remove_parent_edges(self):
        child = self.commit(b"published source", parent=self.good)
        forged = self.commit(b"forged history", parent=self.bad)
        self.git('replace', child, forged)
        store = pin_git.ObjectStore(self.repo, child)
        self.assertEqual(store.ancestry_path(self.good, child), [self.good, child])
        with self.assertRaisesRegex(RuntimeError, "does not advance"):
            store.ancestry_path(self.bad, child)
        self.assertEqual(store.verify_selected_tree()['blobs'], 1)

    def test_parent_header_after_author_cannot_invent_an_edge(self):
        tree = self.git('rev-parse', self.good+'^{tree}')
        raw = b'tree '+tree+b'\nauthor Fixture <fixture@example.invalid> 1 +0000\nparent '+self.bad.encode()+b'\n\nmalformed\n'
        malformed = self.git('hash-object', '--literally', '-w', '-t', 'commit', '--stdin', data=raw).decode()
        with self.assertRaisesRegex(RuntimeError, "noncanonical"):
            pin_git.ObjectStore(self.repo, malformed).ancestry_path(self.bad, malformed)

    def test_carriage_return_cannot_split_a_parent_line(self):
        tree = self.git('rev-parse', self.good+'^{tree}')
        raw = (b'tree '+tree+b'\nparent '+self.good.encode()+b'\rparent '+self.bad.encode()
               +b'\nauthor Fixture <fixture@example.invalid> 1 +0000\n'
                b'committer Fixture <fixture@example.invalid> 1 +0000\n\nmalformed\n')
        malformed = self.git('hash-object', '--literally', '-w', '-t', 'commit', '--stdin', data=raw).decode()
        with self.assertRaisesRegex(RuntimeError, "malformed immutable parent"):
            pin_git.ObjectStore(self.repo, malformed).ancestry_path(self.bad, malformed)

    def test_regular_bytes_are_exact_and_absence_is_distinct(self):
        store = pin_git.ObjectStore(self.repo, self.good)
        self.assertEqual(store.read("Cargo.toml"), b'[workspace.package]\r\nversion="1"\r\n')
        self.assertIsNone(store.optional("missing"))
        with self.assertRaisesRegex(RuntimeError, "missing"):
            store.read("missing")

    def test_actual_replacement_cannot_change_selected_commit_content(self):
        self.git("replace", self.good, self.bad)
        unprotected = subprocess.check_output(["git", "--git-dir", str(self.repo), "show", self.good+":Cargo.toml"],
                                             env={key: value for key, value in self.env.items() if key != "GIT_NO_REPLACE_OBJECTS"})
        self.assertIn(b"wrong", unprotected)
        self.assertNotIn(b"wrong", pin_git.ObjectStore(self.repo, self.good).read("Cargo.toml"))

    def test_object_byte_corruption_is_not_an_identity(self):
        with patch.object(pin_git.subprocess, "check_output", return_value=b"forged"):
            with self.assertRaisesRegex(RuntimeError, "Git identity"):
                pin_git.ObjectStore(self.repo, self.good)

    def test_symlink_and_unsafe_path_refuse(self):
        link = self.commit(b"Cargo.toml", name=b"link", mode=b"120000")
        with self.assertRaisesRegex(RuntimeError, "regular blob"):
            pin_git.ObjectStore(self.repo, link).read("link")
        store = pin_git.ObjectStore(self.repo, self.good)
        for path in ["../Cargo.toml", "/Cargo.toml", "a/../b", ""]:
            with self.subTest(path=path), self.assertRaisesRegex(RuntimeError, "unsafe"):
                store.read(path)

    def test_targo_precedence_and_non_tree_ancestors_refuse(self):
        blob = self.git("hash-object", "-w", "--stdin", data=b"manifest")
        tree = self.git("mktree", data=b"100644 blob "+blob+b"\tCargo.toml\n100644 blob "+blob+b"\tTargo.toml\n")
        commit = self.git("commit-tree", tree.decode(), "-m", "precedence").decode()
        with self.assertRaisesRegex(RuntimeError, "precedence"):
            pin_git.ObjectStore(self.repo, commit).read("Cargo.toml")
        with self.assertRaisesRegex(RuntimeError, "non-tree"):
            pin_git.ObjectStore(self.repo, self.good).read("Cargo.toml/child")

    def test_cached_grafts_and_every_ambient_indirection_are_neutral(self):
        (self.repo / "info").mkdir(exist_ok=True)
        (self.repo / "info/grafts").write_text(self.good+" "+self.bad+"\n")
        poison = {name: "poison" for name in ["GIT_DIR", "GIT_OBJECT_DIRECTORY", "GIT_NAMESPACE",
                                             "GIT_CONFIG_GLOBAL", "GIT_GRAFT_FILE", "GIT_SHALLOW_FILE",
                                             "GIT_TEMPLATE_DIR", "GIT_DEFAULT_HASH", "GIT_DEFAULT_REF_FORMAT"]}
        with patch.dict(os.environ, poison):
            env = pin_git.environment()
            self.assertEqual(env["GIT_GRAFT_FILE"], os.devnull)
            self.assertEqual(env["GIT_CONFIG_GLOBAL"], os.devnull)
            self.assertEqual(env["GIT_CONFIG_NOSYSTEM"], "1")
            self.assertFalse((set(poison) - {"GIT_CONFIG_GLOBAL", "GIT_GRAFT_FILE"}) & set(env))
            self.assertNotIn(b"wrong", pin_git.ObjectStore(self.repo, self.good).read("Cargo.toml"))


if __name__ == "__main__":
    unittest.main()
