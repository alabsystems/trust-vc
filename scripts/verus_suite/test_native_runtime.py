# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""ABI DATA controls using genuine selected native build outputs; no programs run."""

import json
import os
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import native_runtime


@unittest.skipUnless(os.environ.get("TRUST_VC_NATIVE_ABI_INPUTS"),
                     "requires genuine selected build/cohort inputs")
class GenuineNativeRuntimeTest(unittest.TestCase):
    def setUp(self):
        self.inputs = json.loads(Path(os.environ["TRUST_VC_NATIVE_ABI_INPUTS"]).read_text())
        self.directory = self.inputs["runtime_directory"]
        self.engine = self.inputs["engine_executables"]
        self.executables = self.inputs["selected_executables"]

    def test_complete_selected_cohort_uses_one_actual_driver(self):
        inventory = native_runtime.resolve(self.directory, self.executables)
        self.assertEqual(len(inventory["executables"]), len(set(self.executables)))
        self.assertTrue(inventory["driver_name"].startswith("librustc_driver-"))
        self.assertEqual(Path(inventory["driver"]["path"]).parent, Path(self.directory).resolve())
        self.assertFalse(inventory["permission_from_inventory"])
        native_runtime.check(inventory)

    def test_real_engine_refuses_a_different_installed_runtime_directory(self):
        with self.assertRaisesRegex(SystemExit, "lacks the selected driver ABI"):
            native_runtime.resolve(self.inputs["wrong_runtime_directory"], self.engine)

    def test_changed_load_abi_in_an_independent_real_image_copy_refuses(self):
        with tempfile.TemporaryDirectory(prefix="native-abi-mismatch-") as folder:
            original = Path(self.engine[0])
            copy = Path(folder) / original.name
            shutil.copyfile(original, copy)
            data = copy.read_bytes()
            names = [name for name in native_runtime._macho_dylibs(data)
                     if Path(name).name.startswith("librustc_driver-")]
            self.assertEqual(len(names), 1)
            actual = names[0].encode()
            altered = actual
            at = altered.index(b"librustc_driver-") + len(b"librustc_driver-")
            altered = altered[:at] + (b"0" if altered[at:at + 1] != b"0" else b"1") + altered[at + 1:]
            self.assertEqual(data.count(actual), 1)
            copy.write_bytes(data.replace(actual, altered))
            with self.assertRaisesRegex(SystemExit, "one consistent driver ABI"):
                native_runtime.resolve(self.directory, [self.engine[1], copy])

    def test_changed_selected_image_bytes_revoke_the_retained_inventory(self):
        with tempfile.TemporaryDirectory(prefix="native-abi-bytes-") as folder:
            original = Path(self.engine[0])
            copy = Path(folder) / original.name
            shutil.copyfile(original, copy)
            inventory = native_runtime.resolve(self.directory, [copy])
            copy.write_bytes(copy.read_bytes() + b"changed")
            with self.assertRaisesRegex(RuntimeError, "native runtime input changed"):
                native_runtime.check(inventory)

    def test_native_selection_never_falls_back_to_rustup(self):
        with self.assertRaisesRegex(SystemExit, "no rustup fallback"):
            native_runtime.resolve(None, self.engine)
