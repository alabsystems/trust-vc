# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Full-suite guard accounting; DATA only, never build or verifier authority.

The caller must bind the producer's real closed Cargo rows through its existing
owned-build evidence. This module does not authenticate a JSON row or mint a
native declaration, body, proof, compilation lane or imported permission.
"""

import copy
import stat
from pathlib import Path

import native_runtime


FRONTEND_FLAGS = {"rust_verify": "--rust-verify", "verus": "--verus-driver",
                  "cargo-verus": "--cargo-verus"}


def selected_frontends(arguments):
    """Use the real runner grammar, retaining every frontend occurrence."""
    import run_suite

    parser = run_suite.argument_parser(frontend_action="append")
    parser.allow_abbrev = False
    try:
        parsed = parser.parse_args(arguments)
    except SystemExit as error:
        raise ValueError("the owner needs an exact runner argument vector") from error
    selected = {}
    for role, flag in FRONTEND_FLAGS.items():
        values = getattr(parsed, flag[2:].replace("-", "_"))
        if values is None or len(values) != 1 or not values[0].is_absolute():
            raise ValueError(f"bind one absolute selected frontend path: {flag}")
        selected[role] = str(values[0])
    return selected


def _canonical(path):
    return str(Path(path).resolve(strict=True))


def _held_index(files):
    index = {}
    for name in files:
        index.setdefault(_canonical(name), []).append(name)
    return index


def _held_names(index, path):
    names = index.get(_canonical(path), [])
    if not names:
        raise ValueError(f"frontend path is absent from the held input set: {path}")
    return names


def _check_held(files, path, index):
    names = _held_names(index, path)
    _, actual = native_runtime._snapshot(path)
    current = Path(path).stat()
    if (current.st_dev, current.st_ino, current.st_size, current.st_mtime_ns,
            current.st_ctime_ns) != (actual["device"], actual["inode"], actual["bytes"],
                                      actual["mtime_ns"], actual["ctime_ns"]):
        raise ValueError(f"frontend changed during guard construction: {path}")
    for name in names:
        wanted = files[name]
        if (actual["sha256"] != wanted["sha256"] or actual["bytes"] != wanted["bytes"]
                or [actual["device"], actual["inode"]] != wanted["physical"]
                or stat.S_IMODE(current.st_mode) != wanted["mode"]):
            raise ValueError(f"frontend does not match its held input: {name}")
    return names, actual, current


def partition_published_outputs(pins, bindings, selected):
    """Separate only exact producer aliases from distinct held runtime copies.

    Each binding names an actual producer row, its published path and the frozen
    path already selected by the real runner. Unbound files keep every existing
    strict guard. No filename, parent-directory or equal-hash exemption exists.
    The original pin object is not modified.
    """
    result = copy.deepcopy(pins)
    files = result["files"]
    index = _held_index(files)
    if set(selected) != set(FRONTEND_FLAGS):
        raise ValueError("the full owner needs all three selected frontend ports")
    for path in selected.values():
        _check_held(files, path, index)
    published, frozen_identities = {}, set()
    for role, binding in bindings.items():
        if role not in FRONTEND_FLAGS:
            raise ValueError(f"unknown producer binding: {role}")
        row = binding["cargo_row"]
        if (row.get("reason") != "compiler-artifact"
                or row["target"]["kind"] != ["bin"]
                or row["target"]["name"] != role or row["profile"]["test"]
                or row.get("trust_compile_kind") != "host"
                or row.get("trust_compile_mode") != "build"):
            raise ValueError(f"producer row is not the selected ordinary binary: {role}")
        original, frozen = binding["published_path"], binding["frozen_path"]
        if (_canonical(original) != _canonical(row["executable"])
                or _canonical(frozen) != _canonical(selected[role])):
            raise ValueError(f"producer/runtime path binding differs: {role}")
        original_names, before, original_stat = _check_held(files, original, index)
        _, held, held_stat = _check_held(files, frozen, index)
        actual_identity = (held["device"], held["inode"])
        if (_canonical(original) == _canonical(frozen)
                or (before["device"], before["inode"]) == actual_identity
                or Path(frozen).is_symlink() or held_stat.st_nlink != 1
                or stat.S_IMODE(held_stat.st_mode) & 0o222
                or not stat.S_IMODE(held_stat.st_mode) & 0o111
                or actual_identity in frozen_identities):
            raise ValueError(f"runtime frontend is not an independent frozen file: {role}")
        if before["sha256"] != held["sha256"] or held["sha256"] != row["trust_executable_sha256"]:
            raise ValueError(f"producer/runtime executable bytes differ: {role}")
        if any(_canonical(item["published_path"]) == _canonical(original)
               for item in published.values()):
            raise ValueError("one producer path cannot replace two distinct bindings")
        frozen_identities.add(actual_identity)
        published[role] = {"published_path": original, "frozen_path": frozen,
                           "pre_dispatch": dict(before, mode=stat.S_IMODE(original_stat.st_mode)),
                           "removed_pin_paths": original_names,
                           "removed_pins": {name: copy.deepcopy(files[name]) for name in original_names},
                           "unit_identity": row["trust_unit_identity_sha256"]}
    # A producer alias cannot be any configured consumer port, including a
    # different role or a symlink spelling of that same published path.
    originals = {_canonical(item["published_path"]) for item in published.values()}
    if any(_canonical(path) in originals for path in selected.values()):
        raise ValueError("a selected runtime port still names a producer alias")
    for item in published.values():
        for path in item["removed_pin_paths"]:
            del files[path]
    result["schema"] = "trust-vc.held-consumed-inputs@2"
    result["producer_published_outputs"] = published
    return result


def observe_published_outputs(contract):
    """Post-producer observations only; they are not consumed-file guards."""
    result = {}
    for role, item in contract["producer_published_outputs"].items():
        try:
            _, current = native_runtime._snapshot(item["published_path"])
            attributes = Path(item["published_path"]).stat()
            if (attributes.st_dev, attributes.st_ino, attributes.st_mtime_ns,
                    attributes.st_ctime_ns) != (current["device"], current["inode"],
                                                current["mtime_ns"], current["ctime_ns"]):
                raise RuntimeError("published output changed during observation")
            result[role] = {"current": dict(current, mode=stat.S_IMODE(attributes.st_mode))}
        except (OSError, SystemExit) as error:
            result[role] = {"observation_error": str(error)}
    return result
