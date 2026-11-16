# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Read an existing live-owner SDK layout without modifying it.

These inventories are data observations. Only the still-live native coordinator
can accept an import or run the compiler; neither JSON nor this class can do so.
"""

import hashlib
import json
import os
import shlex
import stat
import sys
from pathlib import Path

import native_runtime
import native_request_channel

SCHEMA = "trust-vc.native-sdk-coordinator-request@1"
IMAGES = frozenset(("libverus_builtin.rlib", "libverus_builtin_macros.dylib",
                    "libverus_state_machines_macros.dylib", "libvstd.rmeta", "libvstd.rlib"))
FRONTENDS = frozenset(("rust_verify", "rust_verify.real", "rust_verify.execution.py", "verus",
                       "verus.real", "verus.execution.py", "execution-lender", "cargo-verus",
                       "vstd_metadata_inspect", "vstd_declaration_observe", "vstd_declaration_stage",
                       "vstd_macro_context_observe", "vstd_declaration_read", "vstd_declaration_verify",
                       "vstd_normal_client_verify", "vstd_sdk_client", "rust_verify.public"))


def _object(value, fields):
    if not isinstance(value, dict) or set(value) != set(fields):
        raise RuntimeError("prepared SDK data has missing or unrepresented fields")
    return value


def _path(value):
    if not isinstance(value, str):
        raise RuntimeError("prepared SDK path must be a string")
    path = Path(value)
    if not path.is_absolute() or str(path) != value or ".." in path.parts:
        raise RuntimeError("prepared SDK paths must be exact absolute paths")
    return path


def _sha(value):
    if (not isinstance(value, list) or len(value) != 32
            or any(type(byte) is not int or not 0 <= byte <= 255 for byte in value)):
        raise RuntimeError("prepared SDK SHA256 must be exactly 32 bytes")
    return bytes(value).hex()


def _id(metadata):
    return (metadata.st_dev, metadata.st_ino, metadata.st_mode,
            metadata.st_size, metadata.st_mtime_ns, metadata.st_ctime_ns)


def _regular(path):
    if not stat.S_ISREG(path.lstat().st_mode) or path.resolve(strict=True) != path:
        raise RuntimeError(f"prepared SDK target is not its exact canonical regular file: {path}")


def _json(path):
    _regular(path)
    if path.stat().st_size > 1_048_576:
        raise RuntimeError("prepared SDK JSON exceeds its data bound")
    data, pin = native_runtime._snapshot(path)
    return json.loads(data), pin


class PreparedSdk:
    """A closed inventory observation, not an owner or an import capability."""

    def __init__(self, request, target, dyld):
        self.request = _path(str(request))
        value, request_pin = _json(self.request)
        _object(value, ("schema", "producer_request", "sdk", "frontends", "runner"))
        if value["schema"] != SCHEMA:
            raise RuntimeError("unsupported prepared SDK request schema")
        _path(value["producer_request"])
        runner = _object(value["runner"], ("program", "arguments", "cwd"))
        _path(runner["program"])
        _path(runner["cwd"])
        arguments = runner["arguments"]
        if (not isinstance(arguments, list) or len(arguments) > 4096
                or not all(isinstance(arg, str) for arg in arguments)
                or "--owned-stdin" not in arguments
                or arguments.count("--prepared-sdk-request") != 1):
            raise RuntimeError("prepared SDK needs its exact owned runner request")
        position = arguments.index("--prepared-sdk-request")
        if position + 1 == len(arguments) or arguments[position + 1] != str(self.request):
            raise RuntimeError("prepared SDK runner selects a different request")
        self.root = _path(value["sdk"])
        if self.root != target or self.root.resolve(strict=True) != self.root:
            raise RuntimeError("prepared SDK must be the exact selected staged directory")
        if not stat.S_ISDIR(self.root.lstat().st_mode):
            raise RuntimeError("prepared SDK root must be a real directory")
        frontends = value["frontends"]
        if not isinstance(frontends, list) or not 1 <= len(frontends) <= 20:
            raise RuntimeError("prepared SDK needs its complete frontend inventory")
        self.links = {}
        self.pins = {str(self.request): request_pin}
        declared = {}
        for frontend in frontends:
            _object(frontend, ("name", "path", "sha256"))
            name = frontend["name"]
            if not isinstance(name, str) or name not in FRONTENDS or name in declared:
                raise RuntimeError("prepared SDK has an unrepresented or repeated frontend")
            declared[name] = (_path(frontend["path"]), _sha(frontend["sha256"]))
        if not {"rust_verify", "vstd_sdk_client"} <= declared.keys():
            raise RuntimeError("prepared SDK needs its private forwarder and native data client")
        reference, reference_pin = _json(self.root / "vstd.vir")
        _object(reference, ("schema", "representation", "library", "stable_crate_id", "crate_svh",
                            "source_manifest_sha256", "native_images", "serialized_declarations",
                            "serialized_bodies", "permission_from_reference", "requires_same_live_producer_owner"))
        if (reference["schema"] != "trust-vc.native-sdk-reference@1"
                or reference["representation"] != "live-owner-native-library-reference"
                or reference["library"] != "vstd"
                or reference["serialized_declarations"] is not False
                or reference["serialized_bodies"] is not False
                or reference["permission_from_reference"] is not False
                or reference["requires_same_live_producer_owner"] is not True):
            raise RuntimeError("prepared SDK needs the native live-owner reference, not serialized authority")
        images = reference["native_images"]
        if not isinstance(images, list) or len(images) != len(IMAGES):
            raise RuntimeError("prepared SDK native reference needs the exact five images")
        seen = set()
        for image in images:
            _object(image, ("operand", "actual_target", "sha256"))
            operand = _path(image["operand"])
            name = operand.name
            if operand != self.root / name or name not in IMAGES or name in seen:
                raise RuntimeError("prepared SDK native image operand differs from its exact inventory")
            seen.add(name)
            declared[name] = (_path(image["actual_target"]), _sha(image["sha256"]))
        self.names = frozenset((*declared, "vstd.vir"))
        if set(path.name for path in self.root.iterdir()) != self.names:
            raise RuntimeError("prepared SDK directory differs from its complete inventory")
        self.root_id = _id(self.root.lstat())
        self.reference_id = _id((self.root / "vstd.vir").lstat())
        self.pins[str(self.root / "vstd.vir")] = reference_pin
        # The private wrapper executes these maintained data helpers and this
        # interpreter. Retain/recheck their physical byte inputs too, outside
        # the sealed directory; they supply no native library authority.
        self.pins.update(native_runtime.snapshot_files([
            Path(sys.executable).absolute(), Path(__file__).absolute(),
            Path(native_request_channel.__file__).absolute(),
            Path(native_runtime.__file__).absolute()]))
        for name, (expected, digest) in declared.items():
            link = self.root / name
            before = link.lstat()
            if (not stat.S_ISLNK(before.st_mode) or os.readlink(link) != str(expected)
                    or link.resolve(strict=True) != expected):
                raise RuntimeError(f"prepared SDK link changed: {name}")
            _regular(expected)
            _data, pin = native_runtime._snapshot(expected)
            if pin["sha256"] != digest or _id(link.lstat()) != _id(before):
                raise RuntimeError(f"prepared SDK target differs from its pin: {name}")
            self.links[name] = (str(expected), _id(before))
            self.pins[str(expected)] = pin
        self.staged = {name: self.pins[str(self.root / name)]["sha256"]
                       if name == "vstd.vir" else self.pins[self.links[name][0]]["sha256"]
                       for name in self.names}
        # The private wrapper is deterministic and bound to this actual client.
        wrapper = Path(self.links["rust_verify"][0])
        client = Path(self.links["vstd_sdk_client"][0])
        if wrapper.read_bytes() != forwarder_source(client, self.staged["vstd_sdk_client"], dyld):
            raise RuntimeError("prepared SDK rust_verify is not its pinned private data forwarder")
        if not os.access(wrapper, os.X_OK) or not os.access(client, os.X_OK):
            raise RuntimeError("prepared SDK forwarder/client is not executable")
        self.check()

    def check(self):
        if (_id(self.root.lstat()) != self.root_id
                or self.root.resolve(strict=True) != self.root
                or set(path.name for path in self.root.iterdir()) != self.names
                or _id((self.root / "vstd.vir").lstat()) != self.reference_id):
            raise RuntimeError("prepared SDK sealed inventory changed")
        for name, (target, identity) in self.links.items():
            link = self.root / name
            if _id(link.lstat()) != identity or os.readlink(link) != target:
                raise RuntimeError(f"prepared SDK sealed link changed: {name}")
        native_runtime.check_files(self.pins)


def forwarder_source(client, digest, dyld):
    """Generate the private script BEFORE the owner seals its SDK directory."""
    client = _path(str(client))
    dyld = _path(str(dyld))
    if not isinstance(digest, str) or len(digest) != 64 or bytes.fromhex(digest).hex() != digest:
        raise RuntimeError("private forwarder needs an exact SHA256")
    module_dir = Path(__file__).resolve().parent
    # A direct shebang cannot represent the installed interpreter's spaces.
    # Carry the shell's actual invoked $0 explicitly through Python to execve.
    source = ("import sys\n"
            f"sys.path.insert(0, {str(module_dir)!r})\n"
            "import native_request_channel as channel\n"
            "endpoint = channel.capture()\n"
            "try:\n"
            " import prepared_sdk\n"
            f" prepared_sdk.exec_forwarder(endpoint, {str(client)!r}, {digest!r}, {str(dyld)!r}, sys.argv[1:])\n"
            "finally:\n"
            " if endpoint is not None: endpoint.close()\n")
    return ("#!/bin/bash\nexec " + shlex.quote(sys.executable) + " -I -S -c "
            + shlex.quote(source) + ' "$0" "$@"\n').encode()


def write_forwarder_wrapper(path, client, digest, dyld):
    """Create an independent frontend input, never append to a sealed SDK."""
    path = _path(str(path))
    if os.path.lexists(path.parent / "vstd.vir"):
        raise RuntimeError("a private wrapper must be created outside the sealed SDK")
    source = forwarder_source(client, digest, dyld)
    with path.open("xb") as output:
        output.write(source)
    path.chmod(0o755)
    return {"name": "rust_verify", "path": str(path),
            "sha256": list(hashlib.sha256(source).digest())}


def exec_forwarder(channel, client, digest, dyld, arguments):
    if channel is None:
        raise RuntimeError("the private SDK forwarder requires its actual inherited data channel")
    client = _path(client)
    _regular(client)
    _data, pin = native_runtime._snapshot(client)
    if pin["sha256"] != digest or not os.access(client, os.X_OK):
        raise RuntimeError("the private SDK data client changed")
    environment, descriptors = channel.bind(os.environ)
    # /bin/bash is protected on macOS and strips DYLD; restore the selected
    # explicit runtime only after it, immediately before the actual client exec.
    environment["DYLD_LIBRARY_PATH"] = str(_path(dyld))
    descriptor, = descriptors
    # Only this checked owned descriptor loses CLOEXEC, for this exact exec.
    os.set_inheritable(descriptor, True)
    try:
        os.execve(client, list(arguments), environment)
    finally:
        os.set_inheritable(descriptor, False)
