# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Paths shared by the Verus-suite scripts: the output root, the Verus checkout, the
rustc 1.95.0 library directory the prebuilt Verus binaries link, and the ay binary.

No default here names a machine. Every output goes under the out root; the Verus
checkout and the library directory are found the way the rest of this repository
finds them; AY_BIN has no default at all.

It also holds the one way the Python drivers start run_one.sh (run_one, pool_map), so
that a run_one.sh refusal stops the driver instead of being read as a test outcome.
"""
from __future__ import annotations

import os
import signal
import subprocess
import sys
import threading
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
SHIM = HERE / "ay_z3shim.py"
RUN_ONE = HERE / "run_one.sh"

OUT_ROOT_ENV = "VERUS_SUITE_OUT_ROOT"
DYLD_ENV = "VERUS_SUITE_DYLD"
# The prebuilt Verus a40d57c7 binaries link @rpath/librustc_driver-eea6b8737cd03a8e.dylib
# and carry no LC_RPATH; that library ships with rustc 1.95.0. Only that exact file loads:
# a directory holding a librustc_driver with another hash makes dyld halt rust_verify and
# every test binary at launch (and each halt files a macOS crash report).
RUST_TOOLCHAIN = "1.95.0"
RUSTC_DRIVER = "librustc_driver-eea6b8737cd03a8e.dylib"


def default_out_root() -> Path:
    """VERUS_SUITE_OUT_ROOT, else .verus-suite/ at the repository root (gitignored)."""
    env = os.environ.get(OUT_ROOT_ENV)
    return Path(env).expanduser().absolute() if env else REPO / ".verus-suite"


def resolve_verus(arg: str | os.PathLike | None) -> Path:
    """The Verus checkout: --verus, then TRUST_VC_VERUS_PATH, then VERUS_PATH (the order
    cargo-trust-vc's evidence CLI uses), then ../verus beside the repository (the default
    scripts/corpus_coverage.py uses). A path to its source/ subdirectory is accepted too."""
    if arg:
        path = Path(arg)
    else:
        env = os.environ.get("TRUST_VC_VERUS_PATH") or os.environ.get("VERUS_PATH")
        path = Path(env) if env else REPO.parent / "verus"
    path = path.expanduser().absolute()
    if path.name == "source" and (path / "rust_verify_test").is_dir():
        path = path.parent
    return path


def require_verus(verus: Path) -> Path:
    if not (verus / "source" / "rust_verify_test" / "tests").is_dir():
        raise SystemExit(
            f"no Verus checkout at {verus} (expected source/rust_verify_test/tests). "
            "Pass --verus, or set TRUST_VC_VERUS_PATH or VERUS_PATH, to a checkout at the "
            "pinned upstream.ref of evals/verus/verus-tests.json with its test binaries built.")
    return verus


def oracle_not_installed(detail: str) -> str:
    """The one line every script prints when the stock oracle is absent."""
    return f"NOT RUN: oracle rustc {RUST_TOOLCHAIN} not installed ({detail}); pass --dyld <dir holding {RUSTC_DRIVER}>"


def resolve_dyld(arg: str | os.PathLike | None) -> Path:
    """The directory holding RUSTC_DRIVER: --dyld, then VERUS_SUITE_DYLD, then the lib/
    directory of rustup's RUST_TOOLCHAIN. Refused unless that exact file is there."""
    if arg or os.environ.get(DYLD_ENV):
        lib = Path(arg or os.environ[DYLD_ENV]).expanduser().absolute()
    else:
        # STOCK-AS-ORACLE (docs/rulings.md: kept, pinned, never a blocker): upstream
        # Verus's prebuilt binaries link rustc 1.95.0's librustc_driver; this only locates
        # that dylib to run the third-party baseline and builds no ALab code. It is never
        # installed: without RUSTUP_AUTO_INSTALL=0 `rustup which` on a missing toolchain
        # downloads it (measured, rustup 1.29).
        try:
            r = subprocess.run(["rustup", "which", "--toolchain", RUST_TOOLCHAIN, "rustc"],
                               capture_output=True, text=True, timeout=120,
                               env={**os.environ, "RUSTUP_AUTO_INSTALL": "0"})
        except (OSError, subprocess.TimeoutExpired) as e:
            raise SystemExit(oracle_not_installed(f"cannot run rustup: {e}"))
        if r.returncode != 0:
            raise SystemExit(oracle_not_installed((r.stderr.strip().splitlines() or ["rustup failed"])[0][:300]))
        lib = Path(r.stdout.strip()).parent.parent / "lib"
    if not (lib / RUSTC_DRIVER).is_file():
        raise SystemExit(f"no {RUSTC_DRIVER} in {lib}; the prebuilt Verus binaries load exactly that "
                         f"file and dyld halts them at launch without it (pass --dyld)")
    return lib


def require_ay_bin(value: str | None, where: str) -> str:
    """AY_BIN is required and has no default: a default once pointed at a stale build and
    silently measured the wrong solver."""
    if not value:
        raise SystemExit(f"AY_BIN is required ({where}) and has no default: set it to the ay binary "
                         f"to measure. A default path once measured a stale build without saying so.")
    if not (os.path.isfile(value) and os.access(value, os.X_OK)):
        raise SystemExit(f"AY_BIN={value!r} ({where}) is not an executable file")
    return value


def display_path(path: str | os.PathLike) -> str:
    """A path for reports that may be committed: the home directory is written as ~."""
    text = str(path)
    home = str(Path.home())
    if text == home:
        return "~"
    if text.startswith(home + os.sep):
        return "~" + text[len(home):]
    return text


def run_one_env(out_root: Path, **extra: str) -> dict:
    """Environment for run_one.sh: this process's environment, the out root, and `extra`."""
    env = dict(os.environ)
    env[OUT_ROOT_ENV] = str(out_root)
    env.update({k: v for k, v in extra.items() if v is not None})
    return env


class RunOneRefused(Exception):
    """run_one.sh exited non-zero on its own: a usage, AY_BIN, stage, library or rustup
    problem. It exits 0 whenever the test binary ran, whatever the test did."""


def run_one(args, env: dict, limit: float | None = None) -> bool:
    """Run run_one.sh with `args` in its own session. True when it was killed at `limit`
    seconds (with its whole process group), False when it finished. A non-zero exit that
    was not that kill raises RunOneRefused with run_one.sh's stderr: it is never a result."""
    p = subprocess.Popen([str(RUN_ONE), *map(str, args)], env=env, stdin=subprocess.DEVNULL,
                         stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, start_new_session=True)
    try:
        _, err = p.communicate(timeout=limit)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        p.communicate()
        return True
    if p.returncode != 0:
        raise RunOneRefused(f"run_one.sh {' '.join(map(str, args))} exited {p.returncode}: "
                            f"{err.decode(errors='replace').strip()[-2000:]}")
    return False


def pool_map(fn, items, jobs: int) -> list:
    """fn over items on `jobs` threads, in order. Once one call raises RunOneRefused no
    further item starts, and the driver stops with that refusal (exit 1, message on
    stderr) instead of writing a summary of tests that never ran."""
    stop = threading.Event()

    def guarded(item):
        if stop.is_set():
            return None
        try:
            return fn(item)
        except RunOneRefused:
            stop.set()
            raise

    with ThreadPoolExecutor(max(1, jobs)) as ex:
        futures = [ex.submit(guarded, item) for item in items]
    for f in futures:
        if isinstance(f.exception(), RunOneRefused):
            raise SystemExit(f"{Path(sys.argv[0]).name}: stopped, nothing summarized: {f.exception()}")
    return [f.result() for f in futures]
