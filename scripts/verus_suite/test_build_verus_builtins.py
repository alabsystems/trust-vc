#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Builtins source-resolution failures, before any compiler invocation."""

from __future__ import annotations

import os
import subprocess
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).resolve().with_name("build_verus_builtins.sh")


class BuiltinSources(unittest.TestCase):
    def run_builder(self, root: Path, packages: str) -> subprocess.CompletedProcess:
        upstream = root / "upstream"
        (upstream / "source" / "builtin").mkdir(parents=True)
        (upstream / "source" / "Cargo.lock").write_text(packages)
        env = dict(os.environ, CARGO_HOME=str(root / "cargo-home"))
        return subprocess.run(
            ["bash", str(SCRIPT), str(root / "out"), str(upstream)],
            env=env, text=True, capture_output=True,
        )

    def test_missing_locked_source_does_not_select_another_version(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            available = root / "cargo-home/registry/src/test/unicode-ident-1.0.24/src"
            available.mkdir(parents=True)
            (available / "lib.rs").write_text("")
            run = self.run_builder(root, '''
[[package]]
name = "unicode-ident"
version = "1.0.18"
checksum = "0000000000000000000000000000000000000000000000000000000000000000"
''')
            self.assertNotEqual(run.returncode, 0)
            self.assertIn("missing locked registry source unicode-ident 1.0.18", run.stderr)
            self.assertFalse((root / "out/build.log").exists())

    def test_bad_archive_checksum_is_refused(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            archive = root / "out/src/unicode-ident-1.0.18.crate"
            archive.parent.mkdir(parents=True)
            archive.write_bytes(b"unauthenticated archive")
            run = self.run_builder(root, '''
[[package]]
name = "unicode-ident"
version = "1.0.18"
checksum = "0000000000000000000000000000000000000000000000000000000000000000"
''')
            self.assertNotEqual(run.returncode, 0)
            self.assertIn("checksum mismatch", run.stderr)
            self.assertFalse((root / "out/build.log").exists())

    def test_ambiguous_locked_version_is_refused(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            run = self.run_builder(root, '''
[[package]]
name = "unicode-ident"
version = "1.0.18"
checksum = "a"
[[package]]
name = "unicode-ident"
version = "1.0.19"
checksum = "b"
''')
            self.assertNotEqual(run.returncode, 0)
            self.assertIn("expected exactly one registry unicode-ident 1.x", run.stderr)
            self.assertFalse((root / "out/build.log").exists())


if __name__ == "__main__":
    unittest.main()
