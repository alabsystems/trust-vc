# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Real filesystem controls, not native-verifier/producer permission fixtures.

Prepared source only until explicitly run. Synthetic row-shaped DATA here tests
accounting; no executable, compiler, verifier, solver or fake verdict is run.
"""

import copy
import hashlib
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
import unittest

import held_inputs
import native_runtime


class HeldInputContractTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="suite-held-inputs-")
        self.root = Path(self.temp.name)
        self.files, self.bindings, self.selected = {}, {}, {}
        for role in held_inputs.FRONTEND_FLAGS:
            original = self.root / (role + ".published")
            frozen = self.root / (role + ".frozen")
            original.write_bytes((role + " bytes").encode())
            shutil.copyfile(original, frozen)
            original.chmod(0o755)
            frozen.chmod(0o555)
            digest = hashlib.sha256(original.read_bytes()).hexdigest()
            row = {"reason": "compiler-artifact", "target": {"kind": ["bin"], "name": role},
                   "profile": {"test": False}, "executable": str(original),
                   "trust_compile_kind": "host", "trust_compile_mode": "build",
                   "trust_executable_sha256": digest, "trust_unit_identity_sha256": "a" * 64}
            self.bindings[role] = {"cargo_row": row, "published_path": str(original),
                                   "frozen_path": str(frozen)}
            self.selected[role] = str(frozen)
            for path in [original, frozen]:
                st = path.stat()
                self.files[str(path)] = {"sha256": digest, "bytes": st.st_size,
                                         "physical": [st.st_dev, st.st_ino],
                                         "mode": stat.S_IMODE(st.st_mode)}
        self.pins = {"files": self.files, "source_scopes": {"source": {"head": "unchanged"}}}

    def tearDown(self):
        self.temp.cleanup()

    def partition(self, bindings=None, selected=None):
        return held_inputs.partition_published_outputs(
            self.pins, self.bindings if bindings is None else bindings,
            self.selected if selected is None else selected)

    def replace(self, path, data):
        pending = path.with_suffix(".new")
        pending.write_bytes(data)
        pending.chmod(0o555)
        os.replace(pending, path)

    def test_real_atomic_publication_does_not_replace_a_consumed_context(self):
        original = copy.deepcopy(self.pins)
        contract = self.partition()
        snapshots = native_runtime.snapshot_files(contract["files"])
        for binding in self.bindings.values():
            path = Path(binding["published_path"])
            self.replace(path, path.read_bytes())
        native_runtime.check_files(snapshots)
        self.assertEqual(self.pins, original)
        self.assertEqual(contract["source_scopes"], self.pins["source_scopes"])
        self.assertEqual(len(contract["producer_published_outputs"]), 3)

    def test_same_byte_frozen_path_replacement_is_still_refused(self):
        contract = self.partition()
        snapshots = native_runtime.snapshot_files(contract["files"])
        path = Path(self.selected["rust_verify"])
        self.replace(path, path.read_bytes())
        with self.assertRaises(RuntimeError):
            native_runtime.check_files(snapshots)

    def test_changed_frozen_bytes_are_still_refused(self):
        contract = self.partition()
        snapshots = native_runtime.snapshot_files(contract["files"])
        path = Path(self.selected["verus"])
        self.replace(path, b"another input")
        with self.assertRaises(RuntimeError):
            native_runtime.check_files(snapshots)

    def test_unbound_published_looking_file_keeps_its_strict_guard(self):
        contract = self.partition({"verus": self.bindings["verus"]})
        snapshots = native_runtime.snapshot_files(contract["files"])
        path = Path(self.bindings["rust_verify"]["published_path"])
        self.replace(path, path.read_bytes())
        with self.assertRaises(RuntimeError):
            native_runtime.check_files(snapshots)

    def test_a_different_consumer_port_cannot_use_a_published_alias(self):
        selected = dict(self.selected)
        selected["cargo-verus"] = self.bindings["rust_verify"]["published_path"]
        with self.assertRaisesRegex(ValueError, "runtime port still names"):
            self.partition({"rust_verify": self.bindings["rust_verify"]}, selected)

    def test_hash_equal_hardlink_is_not_an_independent_frozen_context(self):
        path = Path(self.selected["rust_verify"])
        path.unlink()
        os.link(self.bindings["rust_verify"]["published_path"], path)
        path.chmod(0o555)
        for name in [str(path), self.bindings["rust_verify"]["published_path"]]:
            st = Path(name).stat()
            self.files[name]["physical"] = [st.st_dev, st.st_ino]
            self.files[name]["mode"] = stat.S_IMODE(st.st_mode)
        with self.assertRaisesRegex(ValueError, "independent frozen"):
            self.partition()

    def test_alias_abbreviation_and_duplicate_runtime_ports_are_rejected(self):
        args = ["--label", "source-control", "--frontend", "trust-vc",
                "--verus", str(self.root / "upstream")]
        args += sum(([flag, self.selected[role]] for role, flag in held_inputs.FRONTEND_FLAGS.items()), [])
        self.assertEqual(held_inputs.selected_frontends(args), self.selected)
        with self.assertRaises(ValueError):
            held_inputs.selected_frontends(["--rust-v" if a == "--rust-verify" else a for a in args])
        with self.assertRaises(ValueError):
            held_inputs.selected_frontends(args + ["--rust-verify", self.selected["rust_verify"]])

    @unittest.skipUnless(hasattr(os, "mkfifo"), "requires a native FIFO")
    def test_replaced_input_fifo_refuses_without_waiting_for_a_writer(self):
        path = self.root / "not-an-executable"
        os.mkfifo(path)
        program = "import native_runtime,sys; native_runtime.snapshot_files([sys.argv[1]])"
        child = subprocess.run([sys.executable, "-c", program, str(path)],
                               cwd=Path(__file__).resolve().parent,
                               capture_output=True, text=True, timeout=10)
        self.assertNotEqual(child.returncode, 0)
        self.assertIn("not a regular file", child.stderr)
