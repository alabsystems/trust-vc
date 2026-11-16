# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Synthetic file-inventory controls only: no native owner or verifier is created."""

import hashlib
import json
import os
import socket
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import native_request_channel as channel
import owned_processes as owned
import prepared_sdk
import native_runtime
import run_suite


class PreparedInventoryTest(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="prepared-inventory-")
        self.root = Path(self.directory.name).resolve()
        self.label = self.root / "run"
        self.target = self.label / "stage/source/target-verus/debug"
        self.target.mkdir(parents=True)
        self.inputs = self.root / "retained"
        self.inputs.mkdir()
        self.request = self.root / "coordinator.json"
        self.server, self.client = socket.socketpair(socket.AF_UNIX, socket.SOCK_DGRAM)
        self.endpoint = channel.capture({channel.ENV: str(self.client.fileno())})
        self.previous = owned.CURRENT
        owned.CURRENT = owned.Registry(self.endpoint)
        # This JSON describes test files only. It cannot create an import owner.
        images = []
        for name in sorted(prepared_sdk.IMAGES):
            path = self.inputs / name
            path.write_bytes(("synthetic inventory data: " + name).encode())
            (self.target / name).symlink_to(path)
            images.append({"operand": str(self.target / name), "actual_target": str(path),
                           "sha256": list(hashlib.sha256(path.read_bytes()).digest())})
        self.reference = {"schema": "trust-vc.native-sdk-reference@1",
            "representation": "live-owner-native-library-reference", "library": "vstd",
            "stable_crate_id": "data-only", "crate_svh": "data-only", "source_manifest_sha256": [],
            "native_images": images, "serialized_declarations": False, "serialized_bodies": False,
            "permission_from_reference": False, "requires_same_live_producer_owner": True}
        (self.target / "vstd.vir").write_text(json.dumps(self.reference))
        client = Path(sys.executable).resolve()
        digest = hashlib.sha256(client.read_bytes()).hexdigest()
        wrapper = self.inputs / "private wrapper"
        forwarder = prepared_sdk.write_forwarder_wrapper(wrapper, client, digest, self.root)
        self.value = {"schema": prepared_sdk.SCHEMA,
            "producer_request": str(self.root / "producer-request.json"), "sdk": str(self.target),
            "frontends": [forwarder, {"name": "vstd_sdk_client", "path": str(client),
                                     "sha256": list(bytes.fromhex(digest))}],
            "runner": {"program": str(client), "cwd": str(self.root),
                       "arguments": ["run_suite.py", "--owned-stdin", "--prepared-sdk-request", str(self.request)]}}
        for frontend in self.value["frontends"]:
            (self.target / frontend["name"]).symlink_to(frontend["path"])
        self.save_request()
        self.args = SimpleNamespace(prepared_sdk_request=self.request, frontend="trust-vc",
            capture_diagnostics=False, execution_lender=None, dyld=self.root, threads=1, parallel_bins=1)

    def tearDown(self):
        try:
            owned.CURRENT.cleanup()
        finally:
            owned.CURRENT = self.previous
            self.endpoint.close()
            self.client.close()
            self.server.close()
            self.directory.cleanup()

    def save_request(self):
        self.request.write_text(json.dumps(self.value))

    def inventory(self):
        return prepared_sdk.PreparedSdk(self.request, self.target, self.root)

    def tree(self):
        paths = [self.target, *self.target.iterdir()]
        return {str(path): (prepared_sdk._id(path.lstat()),
                           os.readlink(path) if path.is_symlink() else
                           path.read_bytes() if path.is_file() else None) for path in paths}

    def test_prepared_staging_preserves_entire_sealed_directory_without_warmup(self):
        before = self.tree()
        with patch.object(run_suite, "clone_file", side_effect=AssertionError("clone")), \
                patch.object(run_suite, "link_to", side_effect=AssertionError("link")), \
                patch.object(run_suite.owned, "run", side_effect=AssertionError("warmup")), \
                patch.object(run_suite.shutil, "rmtree", side_effect=AssertionError("cleanup")):
            staged = run_suite.stage_target_verus(self.target, self.root / "unused", self.args, self.label)
            again = run_suite.stage_target_verus(self.target, self.root / "unused", self.args, self.label)
        self.assertEqual(staged, again)
        self.assertEqual(set(staged), prepared_sdk.IMAGES | {"vstd.vir", "rust_verify", "vstd_sdk_client"})
        self.assertEqual(before, self.tree())
        self.assertFalse(owned.CURRENT.records)

    def test_unexpected_entry_is_refused_and_left_in_place(self):
        extra = self.target / "unowned"
        extra.write_bytes(b"preserve rejected inventory")
        before = self.tree()
        with self.assertRaisesRegex(RuntimeError, "complete inventory"):
            self.inventory()
        self.assertEqual(before, self.tree())

    def test_missing_image_and_wrong_link_or_frontend_pin_refuse(self):
        name = sorted(prepared_sdk.IMAGES)[0]
        link = self.target / name
        target = os.readlink(link)
        link.unlink()
        with self.assertRaisesRegex(RuntimeError, "complete inventory"):
            self.inventory()
        link.symlink_to(target)
        link.unlink()
        link.symlink_to(self.inputs / sorted(prepared_sdk.IMAGES)[1])
        with self.assertRaisesRegex(RuntimeError, "link changed"):
            self.inventory()
        link.unlink()
        link.symlink_to(target)
        self.value["frontends"][0]["sha256"][0] ^= 1
        self.save_request()
        with self.assertRaisesRegex(RuntimeError, "differs from its pin"):
            self.inventory()

    def test_no_marker_or_saved_permission_can_replace_native_reference(self):
        reference = self.target / "vstd.vir"
        reference.write_text("{}")
        with self.assertRaisesRegex(RuntimeError, "missing or unrepresented"):
            self.inventory()
        self.reference["permission_from_reference"] = True
        reference.write_text(json.dumps(self.reference))
        with self.assertRaisesRegex(RuntimeError, "not serialized authority"):
            self.inventory()

    def test_restore_bytes_does_not_restore_selected_physical_identity(self):
        inventory = self.inventory()
        target = self.inputs / sorted(prepared_sdk.IMAGES)[0]
        original = target.read_bytes()
        target.write_bytes(original + b"changed")
        target.write_bytes(original)
        with self.assertRaisesRegex(RuntimeError, "input changed"):
            inventory.check()

    def test_link_replacement_same_target_and_new_entry_revoke_inventory(self):
        inventory = self.inventory()
        link = self.target / "libvstd.rlib"
        target = os.readlink(link)
        link.unlink()
        link.symlink_to(target)
        with self.assertRaisesRegex(RuntimeError, "inventory changed|link changed"):
            inventory.check()
        inventory = self.inventory()
        (self.target / "new-entry").write_bytes(b"not adopted")
        with self.assertRaisesRegex(RuntimeError, "inventory changed"):
            inventory.check()

    def test_request_substitution_unknown_fields_and_sdk_path_refuse(self):
        self.value["runner"]["arguments"][-1] = str(self.root / "another.json")
        self.save_request()
        with self.assertRaisesRegex(RuntimeError, "different request"):
            self.inventory()
        self.value["runner"]["arguments"][-1] = str(self.request)
        self.value["extra"] = "unrepresented"
        self.save_request()
        with self.assertRaisesRegex(RuntimeError, "unrepresented"):
            self.inventory()
        del self.value["extra"]
        self.value["sdk"] = str(self.root)
        self.save_request()
        with self.assertRaisesRegex(RuntimeError, "exact selected"):
            self.inventory()

    def test_channel_required_and_sdk_wrapper_cannot_be_added_after_sealing(self):
        owned.CURRENT = owned.Registry()
        before = self.tree()
        with self.assertRaisesRegex(RuntimeError, "actual captured"):
            run_suite.stage_target_verus(self.target, self.root, self.args, self.label)
        with self.assertRaisesRegex(RuntimeError, "outside the sealed SDK"):
            prepared_sdk.write_forwarder_wrapper(self.target / "new-wrapper", Path(sys.executable).resolve(),
                "0" * 64, self.root)
        self.assertEqual(before, self.tree())

    def test_prepared_parallelism_refuses_before_touching_the_sealed_inventory(self):
        before = self.tree()
        for threads, bins in ((2, 1), (1, 2), (3, 3)):
            self.args.threads, self.args.parallel_bins = threads, bins
            with self.subTest(threads=threads, bins=bins), self.assertRaisesRegex(RuntimeError, "serial coordinator"):
                run_suite.stage_target_verus(self.target, self.root, self.args, self.label)
            self.assertEqual(before, self.tree())
        self.assertFalse(owned.CURRENT.records)

    def test_private_wrapper_preserves_staged_argv0_real_channel_and_exit(self):
        client = Path(sys.executable).resolve()
        pin = native_runtime.snapshot_files([client])[str(client)]
        source = self.root / "private wrapper input"
        prepared_sdk.write_forwarder_wrapper(source, client, pin["sha256"], self.root)
        stage = self.root / "stage"
        stage.mkdir()
        invoked = stage / "rust_verify"
        invoked.symlink_to(source)
        program = ("import os,sys,socket,json;"
                   f"s=socket.socket(fileno=int(os.environ[{channel.ENV!r}]));"
                   "s.send(b'from native-client standin');"
                   "print(json.dumps({'argv0':sys.orig_argv[0],'args':sys.argv[1:],"
                   "'dyld':os.environ['DYLD_LIBRARY_PATH']}));raise SystemExit(17)")
        with channel.capture({channel.ENV: str(self.client.fileno())}) as endpoint:
            owned.CURRENT = owned.Registry(endpoint)
            result = owned.run([str(invoked), "-c", program, "two words"], env={"PATH": os.defpath},
                               capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, 17, result.stderr)
            self.assertEqual(self.server.recv(128), b"from native-client standin")
            self.assertEqual(json.loads(result.stdout), {
                "argv0": str(invoked), "args": ["two words"], "dyld": str(self.root)})
            endpoint.check()

    def test_failed_exec_restores_cloexec_and_keeps_owned_channel(self):
        invalid = self.root / "not executable format"
        invalid.write_bytes(b"actual ENOEXEC control")
        invalid.chmod(0o755)
        digest = native_runtime.snapshot_files([invalid])[str(invalid)]["sha256"]
        with channel.capture({channel.ENV: str(self.client.fileno())}) as endpoint:
            with self.assertRaises(OSError):
                prepared_sdk.exec_forwarder(endpoint, str(invalid), digest, str(self.root), ["original"])
            endpoint.check()


if __name__ == "__main__":
    unittest.main()
