# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Native executable ABI/load inventory. These pins are DATA, not proof authority."""

import hashlib
import os
import stat
import struct
from pathlib import Path
from typing import List

# The maintained AY installer Mach-O load parser, kept unchanged here so suite
# execution does not depend on a separately installed Python package or source tree.
LC_REQ_DYLD = 0x80000000
DYLIB_COMMANDS = {0xC, 0x18 | LC_REQ_DYLD, 0x1F | LC_REQ_DYLD, 0x20, 0x23 | LC_REQ_DYLD}

def _macho_dylibs(data: bytes, base: int = 0) -> List[str]:
    """The dylibs a Mach-O (thin or universal) loads, from its load commands."""
    magic = data[base:base + 4]
    if magic in (b"\xca\xfe\xba\xbe", b"\xca\xfe\xba\xbf"):  # universal: big-endian fat header
        wide = magic[3] == 0xBF
        (count,) = struct.unpack_from(">I", data, base + 4)
        names: List[str] = []
        for index in range(count):
            if wide:
                _cpu, _sub, offset, _size, _align, _res = struct.unpack_from(">iiQQII", data, base + 8 + 32 * index)
            else:
                _cpu, _sub, offset, _size, _align = struct.unpack_from(">iiIII", data, base + 8 + 20 * index)
            names += [name for name in _macho_dylibs(data, offset) if name not in names]
        return names
    kinds = {b"\xcf\xfa\xed\xfe": ("<", 32), b"\xce\xfa\xed\xfe": ("<", 28),
             b"\xfe\xed\xfa\xcf": (">", 32), b"\xfe\xed\xfa\xce": (">", 28)}
    if magic not in kinds:
        raise ValueError("not a Mach-O file")
    order, header = kinds[magic]
    (ncmds,) = struct.unpack_from(order + "I", data, base + 16)
    offset, names = base + header, []
    for _ in range(ncmds):
        cmd, size = struct.unpack_from(order + "II", data, offset)
        if cmd in DYLIB_COMMANDS:
            (name_at,) = struct.unpack_from(order + "I", data, offset + 8)
            raw = data[offset + name_at:offset + size]
            names.append(raw.split(b"\0", 1)[0].decode("utf-8", "replace"))
        offset += size
    return names


def _snapshot(path):
    path = Path(path).absolute()
    # A replaced path may be a FIFO: reject the actual opened descriptor before
    # reading, without blocking on a writer before regular-file validation.
    flags = os.O_RDONLY | os.O_NONBLOCK | getattr(os, "O_CLOEXEC", 0)
    descriptor = os.open(path, flags)
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise SystemExit(f"native runtime input is not a regular file: {path}")
        with os.fdopen(descriptor, "rb", closefd=False) as file:
            data = file.read()
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    identity = lambda value: (value.st_dev, value.st_ino, value.st_size,
                              value.st_mtime_ns, value.st_ctime_ns)
    if identity(before) != identity(after) or len(data) != before.st_size:
        raise SystemExit(f"native runtime input changed while reading: {path}")
    current = path.stat()
    if identity(current) != identity(after):
        raise SystemExit(f"native runtime input path changed while reading: {path}")
    return data, {"path": str(path), "sha256": hashlib.sha256(data).hexdigest(),
                  "device": after.st_dev, "inode": after.st_ino, "bytes": len(data),
                  "mtime_ns": after.st_mtime_ns, "ctime_ns": after.st_ctime_ns}


def resolve(directory, executables):
    """Join actual selected Mach-O load names to one explicit native runtime."""
    if directory is None:
        raise SystemExit("native Trust execution needs --dyld (or VERUS_SUITE_DYLD); no rustup fallback")
    try:
        directory = Path(directory).expanduser().absolute().resolve(strict=True)
    except OSError as error:
        raise SystemExit(f"cannot read native runtime directory {directory}: {error}") from error
    if not directory.is_dir():
        raise SystemExit(f"native runtime directory is not a directory: {directory}")
    files, names = {}, set()
    for executable in dict.fromkeys(str(Path(p).absolute()) for p in executables):
        try:
            data, pin = _snapshot(executable)
            loads = _macho_dylibs(data)
        except (OSError, ValueError, struct.error) as error:
            raise SystemExit(f"cannot read selected native executable {executable}: {error}") from error
        driver_loads = []
        for load in loads:
            name = Path(load).name
            if not (name.startswith("librustc_driver-") and name.endswith(".dylib")):
                continue
            if load != "@rpath/" + name:
                raise SystemExit(f"selected native driver load is not relative to --dyld: {load}")
            names.add(name)
            driver_loads.append(load)
        files[executable] = dict(pin, driver_loads=driver_loads)
    if len(names) != 1:
        raise SystemExit(f"selected native executables require one consistent driver ABI, found {sorted(names)}")
    name = next(iter(names))
    driver = directory / name
    try:
        data, pin = _snapshot(driver)
        _macho_dylibs(data)
    except (OSError, ValueError, struct.error) as error:
        raise SystemExit(f"native runtime lacks the selected driver ABI {name}: {directory}") from error
    inventory = {"directory": str(directory), "driver_name": name, "driver": pin,
                 "executables": files, "permission_from_inventory": False}
    check(inventory)
    return inventory


def check(inventory, selected=None):
    """Revalidate held byte/path identities; this constructs no native capability."""
    if inventory is None:
        return
    wanted = None if selected is None else {str(Path(p).absolute()) for p in selected}
    pins = [inventory["driver"]]
    pins += [pin for path, pin in inventory["executables"].items()
             if wanted is None or path in wanted]
    if wanted is not None and wanted - inventory["executables"].keys():
        raise RuntimeError("native runtime check requested an unselected executable")
    check_files(pins)


def snapshot_files(paths):
    """Retain actual ordinary file reads; these observations grant no permission."""
    return {str(Path(path).absolute()): _snapshot(path)[1] for path in paths}


def check_files(pins, selected=None):
    """Keep exact held file identities for the actual consumed stage as well."""
    if isinstance(pins, dict):
        wanted = set(pins) if selected is None else {str(Path(p).absolute()) for p in selected}
        if wanted - pins.keys():
            raise RuntimeError("file check requested an unselected input")
        pins = [pins[path] for path in wanted]
    elif selected is not None:
        raise RuntimeError("selected file check needs a named input inventory")
    for pin in pins:
        _, actual = _snapshot(pin["path"])
        if any(actual[key] != pin[key] for key in
               ("sha256", "device", "inode", "bytes", "mtime_ns", "ctime_ns")):
            raise RuntimeError(f"selected native runtime input changed: {pin['path']}")
