#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
# Author: Andrew Yates <andrewyates.name@gmail.com>

"""Execute the trust_vc merge runner binary for a single MergeBundle fixture."""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
from pathlib import Path


def repo_root() -> Path:
    return Path(__file__).resolve().parent.parent


def target_dir(root: Path) -> Path:
    configured = os.environ.get("CARGO_TARGET_DIR")
    if configured:
        return Path(configured)

    worker_id = os.environ.get("AI_WORKER_ID")
    if worker_id and worker_id.isdigit():
        role_name = (os.environ.get("AI_ROLE") or "worker").strip().lower()
        return root / "target" / f"{role_name}_{worker_id}"

    return root / "target"


def runner_binary_candidates(root: Path) -> list[Path]:
    candidates = [target_dir(root) / "debug" / "trust-vc-merge-runner"]
    candidates.append(root / "target" / "debug" / "trust-vc-merge-runner")
    candidates.extend(sorted(root.glob("target/*/debug/trust-vc-merge-runner")))
    deduped: list[Path] = []
    seen: set[Path] = set()
    for candidate in candidates:
        if candidate in seen:
            continue
        seen.add(candidate)
        deduped.append(candidate)
    return deduped


def existing_runner_binary(root: Path) -> Path | None:
    existing = [path for path in runner_binary_candidates(root) if path.exists()]
    if not existing:
        return None
    return max(existing, key=lambda path: path.stat().st_mtime)


def latest_source_mtime(root: Path) -> float:
    candidates = [
        root / "Cargo.toml",
        root / "Cargo.lock",
        root / "crates/trust-vc-merge-runner/Cargo.toml",
        root / "crates/trust-vc-merge-contract/Cargo.toml",
    ]
    for pattern in (
        "crates/trust-vc-merge-runner/src/**/*.rs",
        "crates/trust-vc-merge-contract/src/**/*.rs",
        "crates/trust-vc-merge-contract/fixtures/merge_bundle/*.json",
    ):
        candidates.extend(root.glob(pattern))
    return max(path.stat().st_mtime for path in candidates if path.exists())


def resolve_targo() -> str:
    """Absolute path to the PINNED toolchain's targo.

    A bare "targo" is not enough: it is absent from PATH on an ordinary host
    (the sysroot's bin/ is not added by rustup's shims), and subprocess then
    raises an uncaught FileNotFoundError that surfaces as `kind=engine_error`
    on every fixture -- a gate failure that looks like an engine disagreement.
    `rustc --print sysroot` honours rust-toolchain.toml, so this follows the PIN
    rather than whatever happens to be on PATH, and falls back to PATH only if
    the sysroot copy is missing.
    """
    try:
        sysroot = subprocess.run(
            ["rustc", "--print", "sysroot"],
            capture_output=True, text=True, check=False,
        ).stdout.strip()
    except OSError:
        sysroot = ""
    if sysroot:
        candidate = Path(sysroot) / "bin" / "targo"
        if candidate.is_file():
            return str(candidate)
    found = shutil.which("targo")
    if found:
        return found
    sys.stderr.write(
        "run_merge_bundle: cannot locate the pinned Trust `targo`.\n"
        "  rust-toolchain.toml pins channel = \"trust\"; that sysroot must supply bin/targo.\n"
        f"  resolved sysroot: {sysroot or '<none>'}\n"
        "  refusing to continue -- a missing toolchain must not read as an engine disagreement.\n"
    )
    raise SystemExit(2)


def ensure_runner_binary(root: Path) -> Path:
    binary = existing_runner_binary(root)
    if binary is not None and binary.stat().st_mtime >= latest_source_mtime(root):
        return binary

    manifest_path = root / "crates/trust-vc-merge-runner/Cargo.toml"
    # `--unverified` is REQUIRED, not a shortcut: targo has exactly two lanes and
    # refuses a bare `targo build` outright ("refuses to create an implicitly
    # unverified artifact", exit 101), so without it this gate can never build its
    # own runner. The runner is harness tooling, never a proof artifact — the
    # verdicts it compares come from the MergeBundle, not from compiling it — and
    # trust-vc is the verifier, not a verification target (see .cargo/config.toml).
    result = subprocess.run(
        [
            resolve_targo(),
            "--unverified",
            "build",
            "--quiet",
            "--manifest-path",
            str(manifest_path),
            "--bin",
            "trust-vc-merge-runner",
        ],
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        if result.stdout:
            sys.stdout.write(result.stdout)
        if result.stderr:
            sys.stderr.write(result.stderr)
        raise SystemExit(result.returncode)
    binary = existing_runner_binary(root)
    if binary is None:
        sys.stderr.write("failed to locate trust-vc-merge-runner binary after targo build\n")
        raise SystemExit(1)
    return binary


def main(argv: list[str]) -> int:
    if len(argv) != 3:
        sys.stderr.write(
            "usage: run_merge_bundle.py <bundle_path> <obligation_id> <engine>\n"
        )
        return 2

    root = repo_root()
    binary = ensure_runner_binary(root)
    result = subprocess.run(
        [str(binary), *argv],
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.stdout:
        sys.stdout.write(result.stdout)
    if result.stderr:
        sys.stderr.write(result.stderr)
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
