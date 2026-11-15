#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""A no-op pin update must not invalidate Cargo's watched source inputs."""
import os
from pathlib import Path
import stat
import tempfile
import unittest

from bump_trust_ir_pin import atomic


class AtomicWriteTests(unittest.TestCase):
    def setUp(self):
        parent = Path(tempfile.gettempdir()) / ".ubd"
        parent.mkdir(exist_ok=True)
        self.directory = tempfile.TemporaryDirectory(dir=parent, prefix="vc-pin-write-")
        self.addCleanup(self.directory.cleanup)
        self.path = Path(self.directory.name) / "Cargo.toml"

    def test_identical_bytes_and_mode_preserve_inode_and_timestamp(self):
        self.path.write_bytes(b"original\n")
        self.path.chmod(0o640)
        os.utime(self.path, ns=(1_000_000_000, 1_000_000_000))
        before = self.path.stat()
        atomic(self.path, b"original\n", 0o640)
        after = self.path.stat()
        self.assertEqual((after.st_ino, after.st_mtime_ns),
                         (before.st_ino, before.st_mtime_ns))

    def test_changed_bytes_are_written_with_requested_mode(self):
        self.path.write_bytes(b"old")
        atomic(self.path, b"new", 0o600)
        self.assertEqual(self.path.read_bytes(), b"new")
        self.assertEqual(stat.S_IMODE(self.path.stat().st_mode), 0o600)

    def test_mode_change_is_not_a_noop(self):
        self.path.write_bytes(b"original")
        self.path.chmod(0o644)
        atomic(self.path, b"original", 0o600)
        self.assertEqual(stat.S_IMODE(self.path.stat().st_mode), 0o600)

    def test_missing_file_is_created(self):
        atomic(self.path, b"created", 0o600)
        self.assertEqual(self.path.read_bytes(), b"created")

    def test_equal_symlink_is_replaced_without_changing_its_target(self):
        target = self.path.with_name("target")
        target.write_bytes(b"original")
        target.chmod(0o600)
        self.path.symlink_to(target)
        atomic(self.path, b"original", 0o600)
        self.assertFalse(self.path.is_symlink())
        self.assertEqual(target.read_bytes(), b"original")

    def test_equal_hardlink_is_replaced_with_an_independent_file(self):
        target = self.path.with_name("target")
        target.write_bytes(b"original")
        target.chmod(0o600)
        os.link(target, self.path)
        atomic(self.path, b"original", 0o600)
        self.assertNotEqual(target.stat().st_ino, self.path.stat().st_ino)


if __name__ == "__main__":
    unittest.main()
