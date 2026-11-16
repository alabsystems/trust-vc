#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
"""Run upstream Verus's prebuilt rust_verify_test binaries, unmodified, against one
front end and one SMT solver.

The test binaries are used exactly as built in <verus>/source. The harness starts
<stage>/source/target-verus/debug/rust_verify for every case, and that is the one
thing a run chooses:

  --frontend verus (default)  Verus's own rust_verify, vstd and builtin crates;
                              only the solver behind VERUS_Z3_PATH (--solver)
                              changes between runs (z3, ay, ay behind a shim).
  --frontend trust-vc         trust-vc-rustc's rust_verify (--rust-verify) and the
                              trustc-built builtin crates (--builtins, made by
                              build_verus_builtins.sh). No solver process runs.
                              Every test is scored against trust-vc's verdict
                              records and a Verus+z3 reference run (--reference),
                              see trust_vc_score.py.

--prepared-sdk-request consumes an existing complete SDK layout prepared by a
still-live native coordinator. It requires that coordinator's actual data socket
and --owned-stdin lifecycle. This runner never constructs a native SDK owner.

--capture-diagnostics puts a wrapper in rust_verify's place that copies each run's
stderr (the JSON diagnostics) to runs/<label>/diags/<test dir>/; a Verus+z3 run
captured this way is the reference for trust-vc runs.

Nothing is rebuilt and nothing under <verus> is written: test binaries are
APFS-cloned into a per-label stage, and the harness derives its test_inputs/
directory from the clone's path.

<verus> is --verus, else TRUST_VC_VERUS_PATH, else VERUS_PATH, else ../verus beside
this repository. Oracle binaries use the rustc 1.95.0 runtime lookup. Native Trust
execution requires an explicit --dyld runtime whose driver name matches actual
selected Mach-O load commands; it never falls back to rustup. Every output goes
under --out-root (default
.verus-suite/ at the repository root, or VERUS_SUITE_OUT_ROOT).

Usage:
  run_suite.py --solver <verus>/source/target-verus/debug/z3 --label z3
  run_suite.py --solver <dir>/z3 --label ay-direct \
      --verus-extra-args "-V no-solver-version-check --smt-option timeout=20000"
      (<dir>/z3 is a symlink NAMED z3 pointing at ay: ay's z3 mode, no shim)
  run_suite.py --solver scripts/verus_suite/ay_z3shim.py --label ay \
      --verus-extra-args "-V no-solver-version-check" --env AY_BIN=<ay> ...
  run_suite.py --solver <verus>/source/target-verus/debug/z3 --label z3-diags --capture-diagnostics
  run_suite.py --frontend trust-vc --rust-verify target/debug/rust_verify \
      --builtins <dir> --reference <out-root>/runs/z3-diags --label trust-vc --only basic
  run_suite.py --label z3 --summarize-only        # rebuild csv/summary from cached per-binary results

Outputs (under <out-root>/runs/<label>/):
  results.csv      one row per test
  summary.md       totals + per-file table + every non-ok test
  run.json         arguments, environment, invocations, <verus> write check
  bins/<bin>.json  cached per-binary result (a re-run skips these unless --force/--only)
  logs/<bin>.*     raw libtest JSON stream and stderr for each attempt
  stage/           the staged tree (test_inputs/ of failing tests stay here)
  diags/           --capture-diagnostics: <test dir>/<n>.stderr per rust_verify run
  verdicts/        trust-vc: <test dir>.jsonl verdict records
  score.csv        trust-vc: one scored row per test

Every run that runs anything appends one line to --ledger (default
<out-root>/runs.csv): what ran and its totals, and for trust-vc the score.
"""

# Capture the actual inherited socket before imports/staging can allocate a
# descriptor at an invalid numeric locator. It carries requests, never an SDK.
import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import native_request_channel
_NATIVE_CHANNEL = native_request_channel.capture() if __name__ == "__main__" else None

import argparse
import csv
import datetime as dt
import hashlib
import json
import queue
import re
import shlex
import shutil
import signal
import subprocess
import threading
import time
from pathlib import Path

import suite_common
import native_runtime
import prepared_sdk
import owned_processes as owned
import trust_vc_score

RUST_MIN_STACK = str(20 * 1024 * 1024)  # what vargo sets for `vargo test`

# Binaries that need something other than the solver swap. cargo.rs shells out
# to `cargo clean/check/build` and `cargo verus` on copies of cargo-tests/, which
# on this machine resolves to aterm's cargo reroute and needs a writable vstd
# checkout; it does not exercise the solver in a way the other files do not.
DEFAULT_EXCLUDE = {"cargo": "invokes `cargo`/`cargo verus` builds (PATH cargo is a reroute here); not run"}

OUTCOMES = ["ok", "FAILED", "ignored", "timeout", "crashed", "not-run"]

# The files upstream's harness takes from target-verus/<profile>/ for a test that
# does not import vstd (common/mod.rs run_verus). Ordinary unprepared trust-vc
# staging holds these and rust_verify. Prepared mode consumes its owner's entire
# already-sealed SDK inventory instead.
BUILTIN_ARTIFACTS = [
    "libverus_builtin.rlib",
    "libverus_builtin_macros.dylib",
    "libverus_state_machines_macros.dylib",
]

# trust-vc's rust_verify never starts a solver; a solver path that cannot run makes
# any accidental use fail loudly instead of reaching some z3 on the machine.
NO_SOLVER = "/nonexistent/trust-vc-runs-no-solver-process"
TRUST_VC_VERDICT_ENV = "TRUST_VC_VERDICT_DIR"
# Inert locator only. Nested Targo authenticates its actual live ancestor.
TARGO_NESTED_ENDPOINT = "TRUST_TARGO_NESTED_UNVERIFIED_ENDPOINT"
TARGO_LEGACY_ENDPOINT = "TRUST_TARGO_NESTED_UNVERIFIED_BROKER"

# The maintained zero-token lender accepts only a bare fixed execution. These
# advertisements must be refused before child_env's allowlist can discard them.
LENDER_ADVERTISEMENTS = (
    "CARGO_JOBSERVER_HANDOFF", "TRUST_CPU_HANDOFF", "TRUST_FIXED_CLAIM_HANDOFF_V1",
    "CARGO_MAKEFLAGS", "MAKEFLAGS", "MFLAGS", "TRUST_CPU_IMPLICIT_FD",
    "BUILD_SLOT_FENCE_FDS", "ATERM_SDK_LEASE_V3", "ATERM_WORKLOAD_CPU_FDS_V1",
    "ATERM_WORKLOAD_HOST_STORE_FD_V1", "ATERM_WORKLOAD_HOST_CONTROL_FDS_V1",
)


def execution_lender_context(env):
    if env.get("BUILD_SLOT_HELD") != "1" or env.get("BUILD_SLOT_CPU_PROTOCOL") != "1":
        raise SystemExit("execution lending needs an existing fixed build-slot protocol 1 reservation")
    advertised = [key for key in LENDER_ADVERTISEMENTS if key in env]
    if advertised:
        raise SystemExit("execution lending cannot replace advertised custody: " + ", ".join(advertised))


def execution_lender_inputs(args):
    path = getattr(args, "execution_lender", None)
    if path is None:
        return {}
    if args.frontend != "trust-vc":
        raise SystemExit("--execution-lender applies to --frontend trust-vc only")
    if args.threads != 1 or args.parallel_bins != 1:
        raise SystemExit("execution lending requires --threads 1 --parallel-bins 1")
    execution_lender_context(os.environ)
    for entry in args.env:
        key = entry.partition("=")[0]
        if (key in LENDER_ADVERTISEMENTS or key == "CARGO_BUILD_JOBS"
                or key.startswith(("BUILD_SLOT_", "TARGO_", "TRUST_CPU_", "ATERM_WORKLOAD_", "ATERM_SDK_"))):
            raise SystemExit("--env cannot change execution-lender admission context: " + key)
    path = Path(os.path.abspath(path.expanduser()))
    if not path.is_file() or not os.access(path, os.X_OK):
        raise SystemExit(f"execution lender is not an executable file: {path}")
    # These are executable input identities, never admission or proof authority.
    return native_runtime.snapshot_files([path, Path(sys.executable).absolute()])


def stage_execution_wrapper(wrapper, real, lender, dyld, diags=None):
    """Exec the selected lender; capture mode retains actual wait status too."""
    adapter = wrapper.with_name(wrapper.name + ".execution.py")
    source = '''import os, signal, subprocess, sys, tempfile, time
from pathlib import Path
REAL = %r
LENDER = %r
DYLD = %r
DIAGS = %r
FORBIDDEN = %r
if os.environ.get("BUILD_SLOT_HELD") != "1" or os.environ.get("BUILD_SLOT_CPU_PROTOCOL") != "1" or any(key in os.environ for key in FORBIDDEN):
    sys.stderr.write("execution lending requires bare fixed protocol 1 custody\\n")
    sys.exit(75)
env = dict(os.environ, DYLD_LIBRARY_PATH=DYLD)
argv = [LENDER, REAL, *sys.argv[1:]]
if DIAGS is None:
    os.execve(LENDER, argv, env)
out, entry = "", ""
for index, argument in enumerate(sys.argv[1:], 1):
    if index > 1 and sys.argv[index - 1] == "-o":
        out = argument
    if not argument.startswith("-") and argument.endswith(".rs"):
        entry = argument
with tempfile.TemporaryFile() as stderr:
    status = subprocess.run(argv, env=env, stderr=stderr).returncode
    stderr.seek(0)
    body = stderr.read()
sys.stderr.buffer.write(body)
sys.stderr.buffer.flush()
if out:
    directory = Path(DIAGS) / Path(out).parent.name
    directory.mkdir(parents=True, exist_ok=True)
    (directory / (str(time.time_ns()) + "-" + str(os.getpid()) + ".stderr")).write_bytes(
        ("entry=" + entry + "\\n").encode() + body + ("exit=" + str(status) + "\\n").encode())
if status < 0:
    if -status not in (signal.SIGKILL, signal.SIGSTOP):
        signal.signal(-status, signal.SIG_DFL)
    signal.pthread_sigmask(signal.SIG_UNBLOCK, [-status])
    os.kill(os.getpid(), -status)
os._exit(status)
''' % (str(real), str(lender), str(dyld), str(diags) if diags is not None else None,
       LENDER_ADVERTISEMENTS)
    write_if_changed(adapter, source, 0o644)
    # A shell exec handles interpreter paths containing spaces. The adapter sets
    # DYLD after this protected binary, and exec preserves ordinary signal status.
    write_if_changed(wrapper, "#!/bin/bash\nexec " + shlex.quote(sys.executable)
                     + " -I -S " + shlex.quote(str(adapter)) + ' "$@"\n', 0o755)
    return {path.name: sha256(path, {}) for path in (wrapper, adapter)}

# Stands in for rust_verify under --capture-diagnostics. It runs the real binary,
# passes its stdout, stderr and exit status through, and copies its stderr to
# $DIAGS/<test dir>/<time>-<pid>.stderr between an "entry=" and an "exit=" line.
# The test dir is the directory of rustc's -o output, which the harness makes per
# test. DYLD_LIBRARY_PATH is set here because macOS strips DYLD_* from a process
# started through /bin/bash.
TEE_WRAPPER = """#!/bin/bash
out=""
entry=""
prev=""
for a in "$@"; do
  if [ "$prev" = "-o" ]; then out="$a"; fi
  case "$a" in -*) ;; *.rs) entry="$a";; esac
  prev="$a"
done
tmp=$(mktemp)
export DYLD_LIBRARY_PATH="@DYLD@"
"@REAL@" "$@" 2> "$tmp"
code=$?
cat "$tmp" >&2
if [ -n "$out" ]; then
  dir="@DIAGS@/$(basename "$(dirname "$out")")"
  mkdir -p "$dir"
  { echo "entry=$entry"; cat "$tmp"; echo "exit=$code"; } > "$dir/$(date +%s)-$$.stderr"
fi
rm -f "$tmp"
if [ $code -gt 128 ]; then
  # re-raise the signal that ended rust_verify, so the harness sees it as rust_verify's
  trap - $((code - 128))
  kill -$((code - 128)) $$
fi
exit $code
"""

print_lock = threading.Lock()


def log(msg):
    with print_lock:
        print(f"[{dt.datetime.now().strftime('%H:%M:%S')}] {msg}", flush=True)


def sha256(path, cache={}):
    path = Path(path).resolve()
    if path in cache:
        return cache[path]
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    cache[path] = h.hexdigest()
    return cache[path]


# --------------------------------------------------------------------------- staging

def test_roots():
    manifest = suite_common.REPO / "evals/verus/verus-tests.json"
    roots = json.loads(manifest.read_text())["upstream"]["test_roots"]
    result = []
    for root in roots:
        path = Path(root)
        if path.is_absolute() or ".." in path.parts or path.parts[0] != "source" or path.name != "tests":
            raise SystemExit(f"invalid upstream test root: {root}")
        result.append(path.relative_to("source"))
    if not result or len(set(result)) != len(result):
        raise SystemExit("upstream test roots must be nonempty and unique")
    return result


def binary_id(root, stem):
    # Existing rust_verify_test IDs are also the keys of the committed reference.
    return stem if root == Path("rust_verify_test/tests") else f"{root.parent.as_posix().replace('/', '.')}.{stem}"


def binary_source(name):
    for root in test_roots():
        prefix = binary_id(root, "")
        if prefix and name.startswith(prefix):
            return root / (name[len(prefix):] + ".rs")
    return Path("rust_verify_test/tests") / (name + ".rs")


def binary_cwd(name, src):
    return src / binary_source(name).parent.parent


def discover_binaries(verus_src, roots=None):
    deps = verus_src / "target.noindex/debug/deps"
    sources = {}
    for root in test_roots() if roots is None else roots:
        tests_dir = verus_src / root
        if not tests_dir.is_dir():
            raise SystemExit(f"missing upstream test root: {tests_dir}")
        files = sorted(tests_dir.glob("*.rs"))
        if not files:
            raise SystemExit(f"no test sources in upstream test root: {tests_dir}")
        for source in files:
            if source.stem in sources:
                raise SystemExit(f"ambiguous upstream test target {source.stem}: {sources[source.stem]} and {source}")
            sources[source.stem] = root
    bins = {}
    extras = {}
    for p in sorted(deps.iterdir()):
        if not p.is_file() or "." in p.name or not os.access(p, os.X_OK):
            continue
        m = re.fullmatch(r"(.+)-([0-9a-f]{16})", p.name)
        if not m:
            continue
        name = m.group(1)
        if name in sources:
            key = binary_id(sources[name], name)
            if key in bins:
                raise SystemExit(f"two binaries for {key}: {bins[key]} and {p}")
            bins[key] = p
        else:
            extras[name] = p
    missing = {binary_id(root, name) for name, root in sources.items()} - set(bins)
    if missing:
        raise SystemExit(f"no binary for test sources: {sorted(missing)}")
    return bins, extras


def cargo_helpers(binary, source):
    """cargo_bin! embeds absolute paths; staging a replacement cannot redirect it.

    rustc records env! dependencies in the matching .d file. Require those actual
    helpers, rather than guessing a target directory or silently using PATH tools.
    """
    dep_info = binary.with_suffix(".d")
    if not dep_info.is_file():
        raise SystemExit(f"no compiled helper provenance for {binary}: missing {dep_info}")
    helpers = {}
    for line in dep_info.read_text().splitlines():
        match = re.fullmatch(r"# env-dep:CARGO_BIN_EXE_([^=]+)=(.*)", line)
        if not match:
            continue
        value = re.sub(r"\\([\\nr])", lambda m: {"\\": "\\", "n": "\n", "r": "\r"}[m[1]], match[2])
        path = Path(value)
        if not path.is_absolute() or not path.is_file() or not os.access(path, os.X_OK):
            raise SystemExit(f"compiled helper {match[1]} for {binary} is not executable: {path}")
        if match[1] in helpers:
            raise SystemExit(f"duplicate compiled helper {match[1]} in {dep_info}")
        helpers[match[1]] = {"path": str(path), "sha256": sha256(path, {})}
    # These harnesses import the upstream utility module containing both cargo_bin!
    # calls. The planning-only test_build_new target does not import that module.
    if re.search(r"\bmod\s+utils\s*;", source.read_text()) and not {"cargo-verus", "fake-cargo"} <= helpers.keys():
        raise SystemExit(f"missing cargo-verus/fake-cargo compiled helper paths in {dep_info}; build integration-tests")
    return {"dep_info": str(dep_info), "dep_info_sha256": sha256(dep_info, {}), "helpers": helpers}


def check_cargo_helpers(record):
    if record is None:
        return
    if sha256(record["dep_info"], {}) != record["dep_info_sha256"]:
        raise RuntimeError("compiled cargo harness dependency record changed")
    for helper in record["helpers"].values():
        if not os.access(helper["path"], os.X_OK) or sha256(helper["path"], {}) != helper["sha256"]:
            raise RuntimeError(f"compiled cargo harness helper changed: {helper['path']}")


def describe_extra(path, verus_src):
    tv = verus_src / "target-verus/debug"
    size = path.stat().st_size
    for cand in tv.iterdir():
        if cand.is_file() and cand.stat().st_size == size and sha256(cand) == sha256(path):
            return f"identical to target-verus/debug/{cand.name}; a tool binary, not a libtest harness"
    return "no source in the manifest's test roots; not a libtest harness (not run)"


def clone_file(src, dst):
    """An APFS clone of src at dst (a copy on other filesystems). A dst with the
    same bytes is kept: macOS scans every new executable on its first launch, and
    under load that scan held the first tests of a binary for about a minute."""
    if dst.is_file() and not dst.is_symlink() and dst.stat().st_size == src.stat().st_size \
            and sha256(dst, {}) == sha256(src):
        return
    if dst.is_symlink() or dst.exists():
        dst.unlink()
    if owned.run(["cp", "-c", str(src), str(dst)], capture_output=True).returncode != 0:
        shutil.copy2(src, dst)


def write_if_changed(path, text, mode):
    """Write text to path unless it already holds it (see clone_file)."""
    if path.is_symlink():
        path.unlink()
    if not (path.is_file() and path.read_text() == text):
        path.write_text(text)
    path.chmod(mode)


def link_to(link, target):
    """A symlink at link to target, kept when it is one already."""
    if link.is_symlink() and os.readlink(link) == str(target):
        return
    if link.is_symlink() or link.is_file():
        link.unlink()
    elif link.exists():
        shutil.rmtree(link)
    link.symlink_to(target)


def check_resource_handoff(env):
    # Unmodified upstream libtests start compiler/Cargo grandchildren without
    # the native scheduler's owned descriptor capsule. Environment strings
    # cannot preserve that live ownership across these process boundaries.
    if env.get("BUILD_SLOT_CPU_PROTOCOL") == "2" or "BUILD_SLOT_FENCE_FDS" in env:
        raise SystemExit(
            "native CPU epochs are not supported through upstream libtest children; "
            "use the maintained fixed CPU reservation before suite execution")


def native_cli_inputs(args, bins):
    """Selected executable bytes are run inputs, never imported library authority."""
    tools = {}
    if args.frontend != "trust-vc":
        if args.verus_driver or args.cargo_verus:
            raise SystemExit("--verus-driver and --cargo-verus apply to --frontend trust-vc only")
        return tools
    if bool(args.verus_driver) != bool(args.cargo_verus):
        raise SystemExit("--verus-driver and --cargo-verus must be supplied together")
    if "cargo" in bins and not args.verus_driver:
        raise SystemExit("the cargo harness needs genuine --verus-driver and --cargo-verus build outputs")
    for name, path in (("verus", args.verus_driver), ("cargo-verus", args.cargo_verus)):
        if path:
            path = Path(os.path.abspath(path.expanduser()))
            if not path.is_file() or not os.access(path, os.X_OK):
                raise SystemExit(f"{name} is not an executable file: {path}")
            tools[name] = {"path": str(path), "sha256": sha256(path, {})}
    return tools


def check_native_cli_inputs(tools):
    for name, item in tools.items():
        for field in ("path", "staged_path"):
            if field not in item:
                continue
            path = Path(item[field])
            if not path.is_file() or not os.access(path, os.X_OK) or sha256(path, {}) != item["sha256"]:
                raise RuntimeError(f"native CLI build output changed: {name}: {path}")


def prepared_sdk_inventory(args, target):
    request = getattr(args, "prepared_sdk_request", None)
    if request is None:
        return None
    if (args.frontend != "trust-vc" or args.capture_diagnostics
            or getattr(args, "execution_lender", None)):
        raise RuntimeError("prepared SDK mode needs its private data forwarder without staging adapters")
    if args.threads != 1 or args.parallel_bins != 1:
        raise RuntimeError("prepared SDK mode requires --threads 1 --parallel-bins 1 for its serial coordinator")
    channel = owned.CURRENT.native_channel
    if channel is None:
        raise RuntimeError("prepared SDK mode needs its actual captured native request channel")
    channel.check()
    inventory = getattr(args, "prepared_sdk_inventory", None)
    if inventory is None:
        runtime = args.dyld or os.environ.get(suite_common.DYLD_ENV)
        if runtime is None:
            raise RuntimeError("prepared SDK mode needs its explicit selected native runtime")
        runtime = Path(runtime).expanduser().resolve(strict=True)
        inventory = prepared_sdk.PreparedSdk(request, target, runtime)
        args.prepared_sdk_inventory = inventory
    if inventory.root != target:
        raise RuntimeError("prepared SDK inventory belongs to a different stage")
    inventory.check()
    return inventory


def check_prepared_sdk(args):
    inventory = getattr(args, "prepared_sdk_inventory", None)
    if inventory is not None:
        inventory.check()


def stage_target_verus(tv, verus_src, args, label_dir):
    """<stage>/source/target-verus/debug, where run_verus finds rust_verify and the
    builtin crates. Verus's own, with nothing captured: a symlink to it. Otherwise a
    directory of this run's own: symlinks to Verus's files, or trust-vc's clones, and
    under --capture-diagnostics the tee wrapper as rust_verify. Returns the sha256 of
    every file the run puts there itself."""
    # The native owner has already populated and sealed this entire directory.
    # Consume its COMPLETE inventory before warmups/snapshots and return before
    # any unlink/clone/mkdir or stale-entry cleanup can touch the owned layout.
    check_resource_handoff(os.environ)
    inventory = prepared_sdk_inventory(args, tv)
    if inventory is not None:
        return dict(inventory.staged)
    lender_inputs = getattr(args, "execution_lender_inputs", {})
    if lender_inputs:
        execution_lender_context(os.environ)
        native_runtime.check_files(lender_inputs)
    real_tv = verus_src / "target-verus/debug"
    if args.frontend == "verus" and not args.capture_diagnostics:
        link_to(tv, real_tv)  # never rmtree through the link: it points into <verus>
        return {}
    if tv.is_symlink():
        tv.unlink()
    tv.mkdir(parents=True, exist_ok=True)
    wanted = set()
    staged = {}
    if args.frontend == "verus":
        for entry in real_tv.iterdir():
            if entry.name != "rust_verify":
                link_to(tv / entry.name, entry)
                wanted.add(entry.name)
        real = real_tv / "rust_verify"
    else:
        source_paths = [args.rust_verify, *(args.builtins / name for name in BUILTIN_ARTIFACTS)]
        source_inputs = native_runtime.snapshot_files(source_paths)
        for name in BUILTIN_ARTIFACTS:
            clone_file(args.builtins / name, tv / name)
            staged[name] = sha256(tv / name, {})
            if staged[name] != source_inputs[str((args.builtins / name).absolute())]["sha256"]:
                raise RuntimeError(f"staged builtin differs from its selected input: {name}")
            wanted.add(name)
        real = tv / ("rust_verify.real" if args.capture_diagnostics or lender_inputs else "rust_verify")
        clone_file(args.rust_verify, real)
        staged[real.name] = sha256(real, {})
        if staged[real.name] != source_inputs[str(args.rust_verify.absolute())]["sha256"]:
            raise RuntimeError("staged frontend differs from its selected input")
        native_runtime.check_files(source_inputs)
        wanted.add(real.name)
        if lender_inputs:
            lender = tv / "execution-lender"
            clone_file(args.execution_lender, lender)
            staged[lender.name] = sha256(lender, {})
            if staged[lender.name] != lender_inputs[str(args.execution_lender.absolute())]["sha256"]:
                raise RuntimeError("staged execution lender differs from its selected input")
            wanted.add(lender.name)
            staged.update(stage_execution_wrapper(tv / "rust_verify", real, lender, args.dyld,
                          label_dir / "diags" if args.capture_diagnostics else None))
            wanted.update(("rust_verify", "rust_verify.execution.py"))
        for name, item in args.native_cli_inputs.items():
            original = Path(item["path"])
            if sha256(original, {}) != item["sha256"]:
                raise RuntimeError(f"native CLI build output changed before staging: {original}")
            actual_name = name + ".real" if lender_inputs and name == "verus" else name
            clone_file(original, tv / actual_name)
            staged[actual_name] = sha256(tv / actual_name, {})
            if staged[actual_name] != item["sha256"]:
                raise RuntimeError(f"native CLI stage differs from selected output: {name}")
            item["staged_path"] = str(tv / actual_name)
            wanted.add(actual_name)
            if lender_inputs and name == "verus":
                staged.update(stage_execution_wrapper(tv / name, tv / actual_name, lender, args.dyld))
                wanted.update((name, name + ".execution.py"))
    if args.capture_diagnostics and not lender_inputs:
        wrapper = tv / "rust_verify"
        write_if_changed(wrapper, TEE_WRAPPER.replace("@DYLD@", str(args.dyld)).replace("@REAL@", str(real))
                         .replace("@DIAGS@", str(label_dir / "diags")), 0o755)
        staged["rust_verify"] = sha256(wrapper, {})
        wanted.add("rust_verify")
    warm_inputs = (native_runtime.snapshot_files(tv / name for name in wanted)
                   if args.frontend == "trust-vc" else {})
    # Launch each executable this run staged once, so the macOS first-launch scan
    # of a new file is paid here and not inside the first tests' time.
    for name in ("rust_verify.real", "rust_verify"):
        if name in wanted:
            native_runtime.check_files(warm_inputs)
            try:
                warm_env = ({key: os.environ[key] for key in
                             ("PATH", "BUILD_SLOT_HELD", "BUILD_SLOT_CPU_PROTOCOL") if key in os.environ}
                            if lender_inputs else {"PATH": os.environ.get("PATH", "")})
                owned.run([str(tv / name), "--version"], env=warm_env,
                               capture_output=True, timeout=1800)
            except (OSError, subprocess.TimeoutExpired):
                pass
            native_runtime.check_files(warm_inputs)
    for entry in tv.iterdir():
        # whatever an earlier invocation of this label staged and this one does not
        if entry.name not in wanted:
            if entry.is_dir() and not entry.is_symlink():
                shutil.rmtree(entry)
            else:
                entry.unlink()
    return staged


def stage_cargo_sources(root, verus_src):
    """Cargo fixtures build relative source dependencies; copy tracked inputs only.

    A symlink to upstream would let cargo clean/build touch the checkout being
    measured. Include submodule sources and workspace/config files, never caches.
    """
    checkout = verus_src.parent
    tracked = owned.run(["git", "-C", str(checkout), "ls-files", "--recurse-submodules", "-z"],
                             capture_output=True, check=True).stdout.split(b"\0")
    fixtures = Path("source/rust_verify_test/tests/cargo-tests")
    paths = [Path(os.fsdecode(p)) for p in tracked if p]
    if not any(fixtures in p.parents for p in paths):
        raise SystemExit("no tracked cargo-tests fixtures; full Cargo execution cannot be staged")
    # Earlier ordinary runs used read-only links for these trees.
    for link in (root / "source/builtin", root / "source/vstd", root / "examples"):
        if link.is_symlink():
            link.unlink()
    for relative in paths:
        source, dest = checkout / relative, root / relative
        if not source.is_file():
            raise SystemExit(f"missing tracked Cargo-stage input: {source}")
        dest.parent.mkdir(parents=True, exist_ok=True)
        if dest.is_symlink():
            dest.unlink()
        shutil.copy2(source, dest)


def cargo_internal_skips(verus_src):
    # cargo_examples! derives verified_<directory>/unverified_<directory> names.
    # The original body returns early for this metadata, even with --include-ignored.
    try:
        import tomllib
    except ImportError:
        raise SystemExit("Cargo fixture coverage requires Python 3.11 or newer (tomllib)")
    result = {}
    fixtures = verus_src / "rust_verify_test/tests/cargo-tests"
    for manifest in sorted(fixtures.glob("*/*/Cargo.toml")):
        data = tomllib.loads(manifest.read_text())
        if data.get("package", {}).get("metadata", {}).get("verus", {}).get("test_ignore") is True:
            name = manifest.parent.parent.name + "_" + manifest.parent.name.replace("-", "_")
            result[name] = {"manifest": str(manifest), "sha256": sha256(manifest, {}),
                            "reason": "upstream package.metadata.verus.test_ignore=true; body returns before Cargo"}
    return result


def stage(label_dir, verus_src, bins, args):
    """runs/<label>/stage mirrors the parts of <verus> the harness reaches by relative path."""
    root = label_dir / "stage"
    src = root / "source"
    deps = src / "target.noindex/debug/deps"
    deps.mkdir(parents=True, exist_ok=True)
    (src / "target-verus").mkdir(parents=True, exist_ok=True)
    for tests in test_roots():
        (src / tests.parent).mkdir(parents=True, exist_ok=True)  # package cwd, as under `cargo test`
    # run_verus: exe/../../../target-verus/<profile>
    staged_tv = stage_target_verus(src / "target-verus/debug", verus_src, args, label_dir)
    links = {
        src / "builtin": verus_src / "builtin",                          # core_special_setup.rs #[path] ../../../../builtin
        src / "vstd": verus_src / "vstd",                                # core_special_setup.rs #[path] ../../../../vstd
        root / "examples": verus_src.parent / "examples",                # examples.rs opens ../../examples/* from cwd
    }
    if "cargo" in bins:
        stage_cargo_sources(root, verus_src)
        links = {}  # Cargo gets independent writable fixtures and their source dependencies.
    for link, target in links.items():
        if link.is_symlink() and os.readlink(link) == str(target):
            continue
        if link.is_symlink() or link.exists():
            link.unlink()
        link.symlink_to(target)
    staged = {}
    for name, p in bins.items():
        dst = deps / name
        if not (dst.exists() and dst.stat().st_size == p.stat().st_size and sha256(dst) == sha256(p)):
            if dst.exists():
                dst.unlink()
            # APFS clone: an independent file at no space cost. current_exe() then
            # names the stage, so the harness writes test_inputs/ under the stage.
            r = owned.run(["cp", "-c", str(p), str(dst)])
            if r.returncode != 0:
                shutil.copy2(p, dst)
        staged[name] = dst
    return root, src, staged, staged_tv


# --------------------------------------------------------------------------- env

def child_env(args, src):
    check_resource_handoff(os.environ)
    if getattr(args, "execution_lender_inputs", {}):
        execution_lender_context(os.environ)
    # Carry the actual Cargo inputs and the broker's reservation through every
    # native child. Keep unrelated environment values out of run.json.
    inherited = (
        "PATH", "HOME", "USER", "LOGNAME", "TMPDIR", "LANG", "LC_ALL", "SHELL",
        "CARGO", "RUSTC", "CARGO_HOME", "CARGO_TARGET_DIR", "CARGO_BUILD_JOBS", "ATPKG_BIN",
        "ATERM_CHILD", "ATERM_SESSION_ID", "ATERM_PARENT_SESSION_ID",
        "BUILD_SLOT_HELD", "BUILD_SLOT_DIR", "BUILD_SLOT_EXCLUSIVE",
        "BUILD_SLOT_CPU_SOURCE", "BUILD_SLOT_CPU_BUDGET", "BUILD_SLOT_CPU_MODE",
        "BUILD_SLOT_POOL_SLOTS", "BUILD_SLOT_CPU_PROTOCOL", "BUILD_SLOT_LEGACY_DIR",
        "BUILD_SLOT_V2_DIR", "BUILD_SLOT_V2_SLOTS", "BUILD_SLOT_FENCE_FDS",
        "TARGO_CALLER_JOBS", "TARGO_PLANNED_JOBS", TARGO_NESTED_ENDPOINT,
    )
    env = {key: os.environ[key] for key in inherited if key in os.environ}
    env.update({
        "VERUS_IN_VARGO": "1",
        "RUST_MIN_STACK": RUST_MIN_STACK,  # vargo sets it
        "VARGO_TARGET_DIR": str(src / "target-verus/debug"),
        "DYLD_LIBRARY_PATH": str(args.dyld),
    })
    if args.frontend == "trust-vc":
        env["VERUS_Z3_PATH"] = NO_SOLVER
        env[TRUST_VC_VERDICT_ENV] = str(args.label_dir / "verdicts")
    else:
        # Preserve vargo/libtest setup for the original Verus frontend.
        env["RUSTC_BOOTSTRAP"] = "1"
        # absolute(), never resolve(): a symlink NAMED z3 that points at ay is what
        # turns on ay's z3 mode, so the name must survive
        env["VERUS_Z3_PATH"] = str(Path(args.solver).expanduser().absolute())
    if args.verus_extra_args:
        env["VERUS_EXTRA_ARGS"] = args.verus_extra_args
    for kv in args.env:
        k, _, v = kv.partition("=")
        if k in (TARGO_NESTED_ENDPOINT, TARGO_LEGACY_ENDPOINT):
            raise SystemExit("a nested Targo locator must be inherited unchanged from its live host")
        if k.upper() == native_request_channel.ENV:
            raise SystemExit("a native request channel must be captured from its actual inherited socket")
        if args.frontend == "trust-vc" and k.upper() in (
            "RUSTC_BOOTSTRAP", "RUSTC", "RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER",
            "CARGO_BUILD_RUSTC", "CARGO_BUILD_RUSTC_WRAPPER",
            "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER",
        ):
            raise SystemExit("native suite compiler context must be inherited unchanged; "
                             "--env cannot add bootstrap or compiler overrides")
        env[k] = v
    check_resource_handoff(env)
    return env


# --------------------------------------------------------------------------- libtest driving

def binary_argv(binary):
    # Real process controls can invoke a genuine interpreter with an explicit
    # script argument. Corpus collection still supplies its checked Path values.
    return [str(part) for part in binary] if isinstance(binary, (list, tuple)) else [str(binary)]


def list_tests(binary, env, cwd):
    check_resource_handoff(env)
    # The first launch of a freshly cloned binary waits for macOS's scan of it,
    # which under load took over 120 s.
    r = owned.run(binary_argv(binary) + ["-Z", "unstable-options", "--format", "json", "--list"],
                       env=env, cwd=cwd, capture_output=True, text=True, timeout=1800)
    return parse_discovery(r.stdout, r.returncode, binary, r.stderr)


def parse_discovery(stdout, returncode, binary, stderr=""):
    """Validate a complete libtest JSON list, including lists captured by another owner."""
    tests = {}
    events = []
    for line in stdout.splitlines():
        try:
            e = json.loads(line)
        except json.JSONDecodeError:
            raise RuntimeError(f"non-JSON discovery output from {binary}: {line[:200]}")
        events.append(e)
        if e.get("type") == "test" and e.get("event") == "discovered":
            if e["name"] in tests:
                raise RuntimeError(f"duplicate discovered test in {binary}: {e['name']}")
            tests[e["name"]] = {
                "ignore": bool(e.get("ignore")),
                "source_path": e.get("source_path", ""),
                "line": e.get("start_line", ""),
            }
    completed = [e for e in events if e.get("type") == "suite" and e.get("event") == "completed"]
    starts = [e for e in events if e == {"type": "suite", "event": "discovery"}]
    expected = {"type": "suite", "event": "completed", "tests": len(tests), "benchmarks": 0,
                "total": len(tests), "ignored": sum(d["ignore"] for d in tests.values())}
    if (returncode != 0 or len(starts) != 1 or completed != [expected]
            or len(events) != len(tests) + 2 or events[0] != starts[0] or events[-1] != expected):
        raise RuntimeError(f"incomplete or inconsistent --list for {binary}: rc={returncode} {stderr[-500:]}")
    return tests


PANIC_RE = re.compile(r"^thread '([^']*)'(?: \(\d+\))? panicked at (.*):$")
UNEXP_RE = re.compile(r'^\[unexpected json\] "(.*)"$')


def first_lines(lines, start, n=3):
    out = []
    for l in lines[start:]:
        if not l.strip() or l.startswith("note: run with `RUST_BACKTRACE"):
            break
        out.append(l.strip())
        if len(out) >= n:
            break
    return " / ".join(out)


def extract_failure(name, stdout):
    """(message, detail): the test's own panic message, and the first informative
    line of what rust_verify produced (a verifier panic/signal, else the first
    error diagnostic, else the first warning)."""
    lines = stdout.splitlines()
    message = ""
    for i, l in enumerate(lines):
        m = PANIC_RE.match(l)
        if m and m.group(1) == name:
            message = first_lines(lines, i + 1)
    if not message:
        for i, l in enumerate(lines):
            if PANIC_RE.match(l):
                message = first_lines(lines, i + 1)
    detail = ""
    signal_line = next((l for l in lines if l.startswith("test terminated by a signal")), "")
    unexp = [UNEXP_RE.match(l).group(1) for l in lines if UNEXP_RE.match(l)]
    for i, u in enumerate(unexp):
        m = PANIC_RE.match(u)
        if m:
            nxt = next((x for x in unexp[i + 1:] if x.strip()), "")
            detail = f"rust_verify panicked at {m.group(2)}: {nxt}"
            break
    if not detail:
        nonempty = [u for u in unexp if u.strip()]
        if nonempty:
            detail = "unexpected non-JSON stderr: " + nonempty[0]
    if signal_line:
        detail = signal_line + ("; " + detail if detail else "")
    if not detail:
        for prefix in ("error", "warning"):
            hit = next((l for l in lines if l.startswith(prefix)), "")
            if hit:
                detail = hit
                break
    return message[:400], detail[:400]


def run_attempt(binary, names, env, cwd, threads, stall_s, deadline, log_prefix, attempt,
                include_ignored=False):
    """Run a libtest attempt; retain the actual session root until cleanup/reap."""
    check_resource_handoff(env)
    cmd = binary_argv(binary) + ["-Z", "unstable-options", "--format", "json", "--report-time",
                                "--test-threads", str(threads)]
    if include_ignored:
        cmd.append("--include-ignored")
    if names is not None:
        cmd += ["--exact"] + list(names)
    with open(f"{log_prefix}.a{attempt}.cmd", "w") as f:
        f.write(" ".join(cmd) + "\n")
    results, running, reason = {}, {}, None
    suite_done = False
    with open(f"{log_prefix}.a{attempt}.jsonl", "w") as jsonl, \
            open(f"{log_prefix}.a{attempt}.stderr", "w") as errf, \
            owned.Child(cmd, env=env, cwd=cwd, stdout=subprocess.PIPE, stderr=errf,
                        text=True, bufsize=1) as child:
        p = child.process
        q = queue.Queue()
        def reader():
            try:
                for line in p.stdout:
                    q.put(line)
            except BaseException as error:
                q.put(error)
            finally:
                q.put(None)
        t = threading.Thread(target=reader)
        eof = False
        reader_started = False
        try:
            t.start()
            reader_started = True
            while True:
                owned.CURRENT.check()
                if not eof:
                    try:
                        line = q.get(timeout=1.0)
                    except queue.Empty:
                        line = ""
                    if isinstance(line, BaseException):
                        raise line
                    if line is None:
                        eof = True
                    elif line:
                        jsonl.write(line)
                        try:
                            e = json.loads(line)
                        except json.JSONDecodeError:
                            e = None
                        if e is not None and e.get("type") == "suite" and e.get("event") in ("ok", "failed"):
                            suite_done = True
                        elif e is not None and e.get("type") == "test":
                            n, ev = e.get("name"), e.get("event")
                            if ev == "started":
                                running[n] = time.monotonic()
                            elif ev in ("ok", "failed", "ignored"):
                                running.pop(n, None)
                                outcome = {"ok": "ok", "failed": "FAILED", "ignored": "ignored"}[ev]
                                msg, detail = ("", "")
                                if outcome == "FAILED":
                                    msg, detail = extract_failure(n, e.get("stdout", ""))
                                elif outcome == "ignored":
                                    msg = e.get("message", "") or ""
                                results[n] = {"outcome": outcome, "exec_time": e.get("exec_time", ""),
                                              "message": msg, "detail": detail, "attempt": attempt}
                else:
                    # EOF alone does not mean the process exited. Observe its
                    # native exit without reaping, preserving exit19 after EOF.
                    time.sleep(0.05)
                if child.exited():
                    child.finish()
                    if eof:
                        break
                now = time.monotonic()
                if reason is None:
                    if now > deadline:
                        reason = "wall"
                    else:
                        for n, started in running.items():
                            if now - started > stall_s:
                                reason = f"stall:{n}"
                                break
                    if reason is not None:
                        child.finish()
        finally:
            try:
                rc = child.finish()
            finally:
                if reader_started:
                    t.join()
                p.stdout.close()
    if reason is None and (not suite_done or rc != 0):
        err_tail = Path(f"{log_prefix}.a{attempt}.stderr").read_text(errors="replace").strip().splitlines()
        tail = next((line for line in reversed(err_tail) if line.strip() and not line.startswith("note:")), "")
        status = f"signal {-rc}" if rc < 0 else f"exit {rc}"
        reason = f"crash:{status}; {tail[:300]}"
    return results, dict(running), reason, rc


def run_binary(name, binary, env, cwd, args, logs_dir, discovery):
    t0 = time.monotonic()
    deadline = t0 + args.bin_wall
    log_prefix = logs_dir / name
    results = {}
    attempts = []
    solo = []  # tests in flight during a crash: rerun one at a time to attribute the crash
    include_ignored = getattr(args, "include_ignored", False)
    runnable = [n for n, d in discovery.items() if include_ignored or not d["ignore"]]

    def rec(n, outcome, attempt, message, detail=""):
        results[n] = {"outcome": outcome, "exec_time": "", "attempt": attempt,
                      "message": message, "detail": detail}

    attempt = 0
    while attempt < args.max_attempts and time.monotonic() < deadline:
        pending = [n for n in runnable if n not in results and n not in solo]
        if solo:
            names, threads = [solo.pop(0)], 1
        elif pending:
            names, threads = (None if attempt == 0 else pending), args.threads
        else:
            break
        attempt += 1
        res, running, reason, rc = run_attempt(binary, names, env, cwd, threads, args.test_stall,
                                               deadline, log_prefix, attempt, include_ignored)
        attempts.append({"attempt": attempt, "tests": "all" if names is None else len(names),
                         "threads": threads, "reason": reason, "rc": rc,
                         "results": len(res), "in_flight": sorted(running)})
        results.update(res)
        requested = runnable if names is None else names
        if reason is None:
            for n in requested:
                if n not in results:
                    rec(n, "not-run", attempt, "suite finished without reporting this test")
        elif reason == "wall":
            for n in running:
                rec(n, "timeout", attempt, f"in flight when the per-binary wall limit ({args.bin_wall}s) hit")
        elif reason.startswith("stall:"):
            rec(reason[len("stall:"):], "timeout", attempt,
                f"ran longer than the per-test limit ({args.test_stall}s); binary killed")
        else:  # crash
            why = "test binary died: " + reason[len("crash:"):]
            if len(running) == 1:
                rec(next(iter(running)), "crashed", attempt, why)
            elif len(running) > 1:
                solo.extend(n for n in sorted(running) if n not in results and n not in solo)
            elif not res:
                # died with nothing in flight and nothing reported: it cannot run at all
                for n in requested:
                    if n not in results:
                        rec(n, "crashed", attempt, why)
        if reason is not None and res and all(r["outcome"] == "ok" for r in res.values()):
            # Case/suite events cannot certify an attempt that never finished
            # cleanly. Keep these exact IDs without replaying claimed passes.
            timed_out = reason == "wall" or reason.startswith("stall:")
            outcome = "timeout" if timed_out else "crashed"
            for n in res:
                rec(n, outcome, attempt, "test binary did not finish cleanly: " + reason)
    for n, d in discovery.items():
        if n in results:
            continue
        if d["ignore"] and not include_ignored:
            results[n] = {"outcome": "ignored", "exec_time": "", "attempt": 0, "message": "", "detail": ""}
        elif time.monotonic() >= deadline:
            rec(n, "not-run", attempt, f"per-binary wall limit ({args.bin_wall}s) exhausted before it started")
        else:
            rec(n, "not-run", attempt, f"not reported after {attempt} launches")
    return {"binary": name, "wall_s": round(time.monotonic() - t0, 2), "attempts": attempts,
            "results": results}


# --------------------------------------------------------------------------- reporting

def load_results(label_dir, bins, extras, excluded):
    rows = []
    per_bin = {}
    for name in sorted(bins):
        f = label_dir / "bins" / f"{name}.json"
        if not f.exists():
            continue
        data = json.loads(f.read_text())
        per_bin[name] = data
        disc = data["discovery"]
        unknown = set(data["results"]) - set(disc)
        if unknown:
            raise SystemExit(f"{name} reports undiscovered tests: {sorted(unknown)}")
        for tname in sorted(disc):
            r = data["results"].get(tname, {"outcome": "not-run", "message": "no recorded result"})
            d = disc.get(tname, {})
            rows.append({
                "binary": name,
                "test_file": d.get("source_path") or binary_source(name).as_posix(),
                "test_name": tname,
                "line": d.get("line", ""),
                "outcome": r["outcome"],
                "exec_time_s": r.get("exec_time", ""),
                "message": r.get("message", ""),
                "detail": r.get("detail", ""),
                "attempt": r.get("attempt", ""),
                "coverage_note": data.get("internal_skips", {}).get(tname, {}).get("reason", ""),
            })
    return rows, per_bin


def write_reports(label_dir, label, rows, per_bin, bins, extras, excluded, meta, score_lines=()):
    fields = ["binary", "test_file", "test_name", "line", "outcome", "exec_time_s", "message", "detail", "attempt", "coverage_note"]
    with open(label_dir / "results.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        for r in rows:
            w.writerow(r)
    tot = {o: 0 for o in OUTCOMES}
    by_file = {}
    for r in rows:
        tot[r["outcome"]] += 1
        bf = by_file.setdefault(r["binary"], {o: 0 for o in OUTCOMES})
        bf[r["outcome"]] += 1
    n = len(rows)
    ran = n - tot["ignored"] - tot["not-run"]
    lines = []
    if meta.get("frontend") == "trust-vc":
        lines.append(f"# Verus test suite, trust-vc label `{label}`\n")
    else:
        lines.append(f"# Verus test suite, solver label `{label}`\n")
    # list items rather than markdown's trailing-double-space line breaks, so a summary
    # can be committed without tripping `git diff --check`
    if meta.get("frontend") == "trust-vc":
        lines.append(f"- Front end: trust-vc rust_verify `{suite_common.display_path(meta.get('rust_verify'))}` "
                     f"(sha256 `{meta.get('rust_verify_sha256', '')[:16]}`), builtin crates from "
                     f"`{suite_common.display_path(meta.get('builtins'))}`; no solver process")
    else:
        lines.append(f"- Solver (VERUS_Z3_PATH): `{suite_common.display_path(meta.get('solver'))}`")
    policy = meta.get("coverage_policy")
    if policy:
        lines.append(f"- Coverage: roots {', '.join(policy['test_roots'])}; "
                     f"include ignored={policy['include_ignored']}; full suite={policy['full_suite']}")
    skips = [(binary, name) for binary, names in meta.get("internal_skips", {}).items() for name in names]
    if skips:
        lines.append("- Upstream internal skips (harness outcomes, no Cargo/solver execution): "
                     + ", ".join(f"`{binary}::{name}`" for binary, name in skips))
    if meta.get("capture_diagnostics"):
        lines.append("- rust_verify stderr captured to `diags/`")
    if meta.get("verus_extra_args"):
        lines.append(f"- VERUS_EXTRA_ARGS: `{meta.get('verus_extra_args')}`")
    for i, v in enumerate(meta.get("invocations", []), 1):
        lines.append(f"- Invocation {i}: started {v.get('start')}, {len(v.get('binaries', []))} binaries, "
                     f"wall {v.get('wall_s')} s, {v.get('parallel_bins', meta.get('parallel_bins'))} binaries x "
                     f"{v.get('threads', meta.get('threads'))} test threads at once")
    lines.append(f"- Sum of per-binary wall times: {round(sum(b['wall_s'] for b in per_bin.values()), 1)} s")
    lines.append(f"- Binaries run: {sum(1 for b in per_bin.values() if not b.get('excluded'))} of {len(bins)} test binaries"
                 + (f" (excluded: {', '.join(sorted(excluded))})" if excluded else "") + "\n")
    lines.append("## Totals\n")
    lines.append("| tests | " + " | ".join(OUTCOMES) + " |")
    lines.append("|---|" + "---|" * len(OUTCOMES))
    lines.append(f"| {n} | " + " | ".join(str(tot[o]) for o in OUTCOMES) + " |\n")
    if ran:
        lines.append(f"Pass rate over tests that ran (excludes ignored and not-run): {tot['ok']}/{ran} = {100.0*tot['ok']/ran:.2f}%\n")
    for i, v in enumerate(meta.get("invocations", []), 1):
        if v.get("verus_write_check"):
            lines.append(f"- Verus checkout write check after invocation {i}: {v['verus_write_check']}")
    lines.append("")
    lines.extend(score_lines)
    lines.append("## Per file\n")
    lines.append("| file | tests | " + " | ".join(OUTCOMES) + " | wall s | attempts |")
    lines.append("|---|---|" + "---|" * len(OUTCOMES) + "---|---|")
    for name in sorted(by_file):
        bf = by_file[name]
        b = per_bin[name]
        lines.append(f"| {name}.rs | {sum(bf.values())} | " + " | ".join(str(bf[o]) for o in OUTCOMES)
                     + f" | {b['wall_s']} | {len(b['attempts'])} |")
    lines.append("")
    if excluded or extras:
        lines.append("## Not run\n")
        for name, why in sorted(excluded.items()):
            lines.append(f"- `{name}` ({name}.rs): {why}")
        for name, why in sorted(extras.items()):
            lines.append(f"- `{name}` (deps binary with no tests/{name}.rs): {why}")
        lines.append("")
    bad = [r for r in rows if r["outcome"] in ("FAILED", "timeout", "crashed", "not-run")
           and not r["message"].startswith("excluded:")]
    lines.append(f"## Tests not ok and not ignored ({len(bad)})\n")
    if bad:
        lines.append("| file | test | outcome | message | detail |")
        lines.append("|---|---|---|---|---|")
        for r in bad:
            esc = lambda s: str(s).replace("|", "\\|").replace("\n", " ")
            lines.append(f"| {r['binary']}.rs:{r['line']} | {r['test_name']} | {r['outcome']} | {esc(r['message'])} | {esc(r['detail'])} |")
    else:
        lines.append("None.")
    lines.append("")
    (label_dir / "summary.md").write_text("\n".join(lines))
    return tot


# --------------------------------------------------------------------------- main

def verus_write_check(verus_root, marker):
    """Files or dirs under the Verus checkout modified after the run started, plus git status."""
    r = owned.run(["find", str(verus_root), "-newer", str(marker), "-not", "-path", "*/.git/*"],
                       capture_output=True, text=True)
    changed = [l for l in r.stdout.splitlines() if l.strip()]
    # --no-optional-locks: a plain `git status` creates .git/index.lock, which bumps .git's mtime
    g = owned.run(["git", "--no-optional-locks", "-C", str(verus_root), "status", "--porcelain"],
                       capture_output=True, text=True)
    status = g.stdout.strip()
    if not changed and not status:
        return "clean (no path newer than the run start, git status empty)"
    return f"{len(changed)} path(s) newer than run start: {changed[:10]}; git status: {status[:500] or 'empty'}"


def uses_measurement_shim(solver):
    """True when VERUS_Z3_PATH is the measurement shim (or a copy of it)."""
    return solver.resolve() == suite_common.SHIM.resolve() or "z3shim" in solver.name


def preflight(args, solver):
    """Refuse a run that cannot measure what it says, before anything is staged."""
    env = dict(kv.partition("=")[::2] for kv in args.env)
    shim_runs_z3 = uses_measurement_shim(solver) and env.get("SHIM_SOLVER", "").startswith("z3:")
    if uses_measurement_shim(solver) and not shim_runs_z3:
        if not env.get("AY_BIN"):
            raise SystemExit(
                f"{solver.name} is the measurement shim and runs ay, but no AY_BIN was given: pass "
                "--env AY_BIN=<ay binary> (the test processes get a fresh environment, so an AY_BIN "
                "exported in this shell does not reach them). There is no default: a default path once "
                "measured a stale build without saying so.")
        suite_common.require_ay_bin(env["AY_BIN"], "--env AY_BIN")
        if "AY_SHIM_ARGS" in env and "--z3-mode" not in env["AY_SHIM_ARGS"].split():
            log("warning: --env AY_SHIM_ARGS has no --z3-mode, so ay runs in its native mode, whose "
                "reason-unknown words AIR does not accept (the shim's default is -q --z3-mode)")
    verus_z3 = args.verus / "source/target-verus/debug/z3"
    if (not shim_runs_z3 and "no-solver-version-check" not in args.verus_extra_args
            and not (verus_z3.exists() and solver.resolve() == verus_z3.resolve())):
        log("warning: the solver is not Verus's own z3 and --verus-extra-args has no "
            "`-V no-solver-version-check`; Verus rejects a solver that does not report z3 4.12.5")


# --------------------------------------------------------------------------- trust-vc scoring, ledger

RECORDED_Z3 = suite_common.REPO / "evals/verus/upstream-suite/runs/z3/results.csv"


def read_outcomes(results_csv):
    """(binary, test) -> outcome from a run's results.csv."""
    if not results_csv.is_file():
        return None
    with open(results_csv, newline="") as f:
        return {(r["binary"], r["test_name"]): r["outcome"] for r in csv.DictReader(f)}


def score_trust_vc(label_dir, rows, verus_src, reference_dir):
    """Score a trust-vc run (trust_vc_score.py), write score.csv, and return the
    summary lines and the totals."""
    ref_outcomes = read_outcomes(reference_dir / "results.csv") if reference_dir else None
    scored, totals = trust_vc_score.score_run(rows, label_dir / "verdicts", label_dir / "logs", verus_src,
                                              reference_dir, ref_outcomes)
    with open(label_dir / "score.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=trust_vc_score.SCORE_FIELDS)
        w.writeheader()
        w.writerows(scored)
    lines = trust_vc_score.summary_lines(scored, totals)
    if reference_dir is None:
        lines.insert(1, "No --reference: no verified function could be cross-checked.\n")
    else:
        recorded = read_outcomes(RECORDED_Z3) or {}
        ran = {(r["binary"], r["test_name"]) for r in rows}
        differ = sorted(k for k in ran if k in recorded and (ref_outcomes or {}).get(k) != recorded[k])
        totals["reference_differs_from_recorded_z3"] = len(differ)
        lines.insert(1, f"Reference: `{suite_common.display_path(reference_dir)}`. Its outcome differs from the "
                        f"recorded z3 run (`evals/verus/upstream-suite/runs/z3/results.csv`) on {len(differ)} "
                        f"of the {len(ran)} tests run here"
                        + (": " + ", ".join(f"{b}::{t}" for b, t in differ[:20]) if differ else "") + ".\n")
    return lines, totals


LEDGER_FIELDS = ["finished", "label", "frontend", "git_head", "rust_verify_sha256", "solver", "binaries",
                 "tests", "ok", "FAILED", "ignored", "timeout", "crashed", "not-run",
                 "live", "pass", "refused", "vacuous", "refused_but_harness_ok", "false_pass", "false_pass_ref",
                 "bad_record", "untagged_fail", "verified_fns", "unchecked_verified_fns",
                 "reference", "reference_differs_from_recorded_z3", "scored_ok"]


def git_head(ledger=None):
    """HEAD of this repository, with "-dirty" when a tracked file other than the
    ledger itself has changes."""
    r = owned.run(["git", "-C", str(suite_common.REPO), "rev-parse", "--short=12", "HEAD"],
                       capture_output=True, text=True)
    head = r.stdout.strip() or "unknown"
    cmd = ["git", "-C", str(suite_common.REPO), "status", "--porcelain", "--untracked-files=no"]
    if ledger is not None and str(ledger).startswith(str(suite_common.REPO) + os.sep):
        cmd += ["--", ".", f":(exclude){os.path.relpath(ledger, suite_common.REPO)}"]
    d = owned.run(cmd, capture_output=True, text=True)
    return head + ("-dirty" if d.stdout.strip() else "")


def append_ledger(path, meta, tot, per_bin, score_totals, reference_dir):
    """One line per run: what ran, its outcome totals, and the trust-vc score."""
    row = {k: "" for k in LEDGER_FIELDS}
    row.update({
        "finished": dt.datetime.now().isoformat(timespec="seconds"),
        "label": meta.get("label", ""),
        "frontend": meta.get("frontend", "verus"),
        "git_head": git_head(path),
        "rust_verify_sha256": meta.get("rust_verify_sha256", "")[:16],
        "solver": suite_common.display_path(meta.get("solver") or ""),
        "binaries": sum(1 for b in per_bin.values() if not b.get("excluded")),
        "tests": sum(tot.values()),
        **{o: tot[o] for o in OUTCOMES},
    })
    if score_totals is not None:
        for k in ("live", "pass", "refused", "vacuous", "refused_but_harness_ok", "false_pass", "false_pass_ref",
                  "bad_record", "untagged_fail", "verified_fns", "unchecked_verified_fns",
                  "reference_differs_from_recorded_z3"):
            row[k] = score_totals.get(k, "")
        row["reference"] = suite_common.display_path(reference_dir) if reference_dir else ""
        row["scored_ok"] = score_totals["ok"]
    path.parent.mkdir(parents=True, exist_ok=True)
    rows = []
    if path.exists():
        with open(path, newline="") as f:
            reader = csv.DictReader(f)
            if reader.fieldnames != LEDGER_FIELDS:
                # a ledger written before a column was added: rewrite it under the
                # current header, the old lines keeping an empty cell for the new column
                rows = [{k: r.get(k, "") or "" for k in LEDGER_FIELDS} for r in reader]
    if rows or not path.exists():
        with open(path, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=LEDGER_FIELDS)
            w.writeheader()
            w.writerows(rows)
    with open(path, "a", newline="") as f:
        csv.DictWriter(f, fieldnames=LEDGER_FIELDS).writerow(row)
    return row


def clear_test_outputs(label_dir, name, discovery):
    """Drop the verdict records and captures an earlier invocation left for the
    tests of binary `name`: both are appended to, one run after another."""
    if name == "examples":
        keys = None  # example-<stem>: not derivable from the test name alone
    else:
        keys = {f"{name}-{t}" for t in discovery}
    for f in (label_dir / "verdicts").glob("*.jsonl"):
        if (keys is None and f.stem.startswith("example-")) or (keys is not None and f.stem in keys):
            f.unlink()
    for d in (label_dir / "diags").glob("*"):
        if d.is_dir() and ((keys is None and d.name.startswith("example-")) or (keys is not None and d.name in keys)):
            shutil.rmtree(d)


def argument_parser(*, frontend_action="store"):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--owned-stdin", action="store_true", help=argparse.SUPPRESS)
    ap.add_argument("--prepared-sdk-request", type=Path, default=None,
                    help="consume this live coordinator request's complete pre-staged SDK inventory; "
                         "requires its inherited native request channel, --owned-stdin, "
                         "--threads 1 and --parallel-bins 1")
    ap.add_argument("--solver", help="path used as VERUS_Z3_PATH (kept as given, symlinks are not resolved)")
    ap.add_argument("--label", required=True)
    ap.add_argument("--verus", "--verus-path", dest="verus", default=None,
                    help="Verus checkout, read only (default: TRUST_VC_VERUS_PATH, VERUS_PATH, ../verus)")
    ap.add_argument("--dyld", default=None,
                    help="driver library directory: native Trust requires an explicit directory "
                         "(or VERUS_SUITE_DYLD) matching actual selected Mach-O load commands; "
                         "oracle lookup retains its pinned rustup default")
    ap.add_argument("--out-root", type=Path, default=None,
                    help="where runs/<label>/ goes (default: VERUS_SUITE_OUT_ROOT, else .verus-suite/ at the repo root)")
    ap.add_argument("--verus-extra-args", default="", help="VERUS_EXTRA_ARGS (e.g. '-V no-solver-version-check')")
    ap.add_argument("--env", action="append", default=[], help="extra K=V for the test processes (repeatable)")
    ap.add_argument("--threads", type=int, default=3, help="--test-threads per binary")
    ap.add_argument("--parallel-bins", type=int, default=3, help="binaries run at once")
    ap.add_argument("--bin-wall", type=int, default=5400, help="per-binary wall limit, seconds")
    ap.add_argument("--test-stall", type=int, default=900, help="kill a binary when one test runs longer than this, seconds")
    ap.add_argument("--max-attempts", type=int, default=200, help="libtest launches per binary (reruns after kills)")
    ap.add_argument("--only", default="", help="comma-separated binary names to (re)run")
    ap.add_argument("--exclude", default=None, help="comma-separated binary names to skip (default: cargo)")
    ap.add_argument("--include-ignored", action="store_true",
                    help="execute ignored cases too; declaration alone never establishes a test result")
    ap.add_argument("--full-suite", action="store_true",
                    help="all manifest roots and binaries, with --include-ignored; no selection/summary-only")
    ap.add_argument("--force", action="store_true", help="re-run binaries that already have cached results")
    ap.add_argument("--summarize-only", action="store_true")
    ap.add_argument("--frontend", choices=["verus", "trust-vc"], default=None,
                    help="whose rust_verify the harness starts (default: verus, or what the label's run.json says)")
    ap.add_argument("--rust-verify", type=Path, default=None, action=frontend_action,
                    help="trust-vc: the rust_verify binary to stage (trust-vc-rustc, feature rustc)")
    ap.add_argument("--verus-driver", type=Path, default=None, action=frontend_action,
                    help="trust-vc: genuine native verus build output, staged beside cargo-verus")
    ap.add_argument("--cargo-verus", type=Path, default=None, action=frontend_action,
                    help="trust-vc: genuine upstream cargo-verus build output (required with --verus-driver)")
    ap.add_argument("--execution-lender", type=Path, default=None, action=frontend_action,
                    help="trust-vc: actual source-built zero-token execution lender under fixed admission; "
                         "requires --threads 1 --parallel-bins 1")
    ap.add_argument("--builtins", type=Path, default=None,
                    help="trust-vc: directory holding the trustc-built " + ", ".join(BUILTIN_ARTIFACTS)
                         + " (build_verus_builtins.sh)")
    ap.add_argument("--reference", type=Path, default=None,
                    help="trust-vc: a runs/<label> directory of a Verus+z3 run made with --capture-diagnostics; "
                         "every function trust-vc calls verified is checked against its errors")
    ap.add_argument("--capture-diagnostics", action="store_true",
                    help="copy every rust_verify run's stderr to runs/<label>/diags/<test dir>/")
    ap.add_argument("--ledger", type=Path, default=None,
                    help="CSV that gets one line per run (default: <out-root>/runs.csv)")
    return ap


def main():
    ap = argument_parser()
    args = ap.parse_args()
    check_resource_handoff(os.environ)
    if args.full_suite and (not args.include_ignored or args.only or args.exclude or args.summarize_only):
        ap.error("--full-suite requires --include-ignored and forbids --only/--exclude/--summarize-only")

    args.verus = suite_common.resolve_verus(args.verus)
    out_root = (Path(os.path.abspath(args.out_root.expanduser())) if args.out_root
                else suite_common.default_out_root())
    label_dir = out_root / "runs" / args.label
    args.label_dir = label_dir
    if args.prepared_sdk_request is not None and (not args.owned_stdin or args.summarize_only):
        ap.error("--prepared-sdk-request needs --owned-stdin and an actual run")
    meta_path = label_dir / "run.json"
    meta = json.loads(meta_path.read_text()) if meta_path.exists() else {"invocations": []}
    if args.frontend is None:
        args.frontend = meta.get("frontend", "verus")
    elif meta.get("invocations") and meta.get("frontend", "verus") != args.frontend:
        raise SystemExit(f"label {args.label} holds a {meta.get('frontend', 'verus')} run; use another label")
    if args.reference is None and meta.get("reference") and args.frontend == "trust-vc":
        args.reference = Path(meta["reference"])
    args.execution_lender_inputs = execution_lender_inputs(args)
    if args.execution_lender:
        args.execution_lender = Path(os.path.abspath(args.execution_lender.expanduser()))
    if args.reference is not None:
        args.reference = Path(os.path.abspath(args.reference.expanduser()))
        if not (args.reference / "diags").is_dir():
            raise SystemExit(f"--reference {args.reference} has no diags/: make it with --capture-diagnostics")
    solver = None
    if not args.summarize_only:
        if args.frontend == "trust-vc":
            if args.solver:
                raise SystemExit("--solver does not apply to --frontend trust-vc: it starts no solver process")
            if not args.rust_verify or not args.builtins:
                raise SystemExit("--frontend trust-vc needs --rust-verify and --builtins")
            args.rust_verify = Path(os.path.abspath(args.rust_verify.expanduser()))
            args.builtins = Path(os.path.abspath(args.builtins.expanduser()))
            if not os.access(args.rust_verify, os.X_OK):
                raise SystemExit(f"rust_verify not executable: {args.rust_verify}")
            missing = [a for a in BUILTIN_ARTIFACTS if not (args.builtins / a).is_file()]
            if missing:
                raise SystemExit(f"--builtins {args.builtins} lacks {missing}; build them with build_verus_builtins.sh")
            if args.reference is None:
                log("warning: no --reference: no function trust-vc calls verified can be cross-checked, "
                    "so the run cannot be scored ok")
        else:
            if args.rust_verify or args.builtins:
                raise SystemExit("--rust-verify and --builtins apply to --frontend trust-vc only")
            if not args.solver:
                raise SystemExit("--solver is required unless --summarize-only or --frontend trust-vc")
            solver = Path(args.solver).expanduser().absolute()
            if not os.access(solver, os.X_OK):
                raise SystemExit(f"solver not executable: {solver}")
            preflight(args, solver)
        if args.frontend == "verus":
            args.dyld = suite_common.resolve_dyld(args.dyld)

    verus_src = suite_common.require_verus(args.verus) / "source"
    (label_dir / "bins").mkdir(parents=True, exist_ok=True)
    (label_dir / "logs").mkdir(parents=True, exist_ok=True)
    owned.CURRENT.record_path = label_dir / "child-lifetimes.json"

    bins, extras_paths = discover_binaries(verus_src)
    if args.full_suite:
        excluded = {}
    elif args.exclude is None:
        excluded = dict(DEFAULT_EXCLUDE)
    else:
        excluded = {n: "excluded by --exclude" for n in args.exclude.split(",") if n}
    extras = {n: describe_extra(p, verus_src) for n, p in extras_paths.items()}
    selected_bins = {n: p for n, p in bins.items()
                     if n not in excluded and (not args.only or n in args.only.split(","))}
    args.native_cli_inputs = (native_cli_inputs(args, selected_bins)
                              if not args.summarize_only else {})
    check_native_cli_inputs(args.native_cli_inputs)
    prepared = prepared_sdk_inventory(args, label_dir / "stage/source/target-verus/debug")
    args.native_runtime_inventory = None
    if not args.summarize_only and args.frontend == "trust-vc":
        native_paths = [args.rust_verify, *selected_bins.values(),
                        *(Path(item["path"]) for item in args.native_cli_inputs.values())]
        if args.execution_lender_inputs:
            native_paths.append(args.execution_lender)
        if prepared is not None:
            native_paths.append(Path(prepared.links["vstd_sdk_client"][0]))
        args.native_runtime_inventory = native_runtime.resolve(
            args.dyld or os.environ.get(suite_common.DYLD_ENV), native_paths)
        args.dyld = Path(args.native_runtime_inventory["directory"])

    if args.summarize_only:
        rows, per_bin = load_results(label_dir, bins, extras, excluded)
        score_lines = []
        if args.frontend == "trust-vc":
            score_lines, _ = score_trust_vc(label_dir, rows, verus_src, args.reference)
        write_reports(label_dir, args.label, rows, per_bin, bins, extras, excluded, meta, score_lines)
        print((label_dir / "summary.md").read_text()[:3000])
        return

    policy = {"test_roots": [p.as_posix() for p in test_roots()],
              "include_ignored": args.include_ignored, "full_suite": args.full_suite}
    if meta.get("invocations") and meta.get("coverage_policy") != policy:
        raise SystemExit("coverage policy changed (test roots/ignored/full suite); use a new label")
    internal_skips = cargo_internal_skips(verus_src) if "cargo" in bins and "cargo" not in excluded else {}
    helpers = {name: cargo_helpers(path, verus_src / binary_source(name))
               for name, path in bins.items() if name.startswith("cargo-verus.") and name not in excluded}

    lock = label_dir / ".lock"
    try:
        fd = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
        os.write(fd, str(os.getpid()).encode())
        os.close(fd)
    except FileExistsError:
        pid = lock.read_text().strip()
        try:
            os.kill(int(pid), 0)
            raise SystemExit(f"label {args.label} is locked by running pid {pid}")
        except (ProcessLookupError, ValueError):
            lock.write_text(str(os.getpid()))

    try:
        marker = label_dir / ".run-start"
        marker.write_text(dt.datetime.now().isoformat())
        time.sleep(1.1)  # find -newer has 1 s granularity on some filesystems
        root, src, staged, staged_tv = stage(label_dir, verus_src,
                                             {n: p for n, p in bins.items() if n not in excluded}, args)
        check_prepared_sdk(args)
        env = child_env(args, src)
        staged_inputs = {}
        stage_frontends = []
        if args.frontend == "trust-vc":
            expected_target = str(src / "target-verus/debug")
            if env.get("VARGO_TARGET_DIR") != expected_target:
                raise SystemExit("native suite runtime must use its selected staged frontend")
            stage_frontends = [src / "target-verus/debug" / name for name in staged_tv]
            staged_inputs = native_runtime.snapshot_files([*staged.values(), *stage_frontends])
            for name, path in staged.items():
                if staged_inputs[str(path.absolute())]["sha256"] != sha256(bins[name], {}):
                    raise RuntimeError(f"staged harness differs from its selected input: {name}")
            for name, wanted in staged_tv.items():
                path = src / "target-verus/debug" / name
                if staged_inputs[str(path.absolute())]["sha256"] != wanted:
                    raise RuntimeError(f"staged frontend differs from its selected input: {name}")
            (label_dir / "staged-consumed-inputs.json").write_text(json.dumps(staged_inputs, indent=1))

        only = {n for n in args.only.split(",") if n}
        # excluded test binaries still get one row per test (outcome not-run, with the reason);
        # listing a libtest binary runs no test and writes nothing
        for name, why in excluded.items():
            if name not in bins:
                continue
            disc = list_tests(bins[name], env, binary_cwd(name, src))
            res = {n: {"outcome": "not-run", "exec_time": "", "attempt": 0,
                       "message": "excluded: " + why, "detail": ""} for n in disc}
            (label_dir / "bins" / f"{name}.json").write_text(json.dumps(
                {"binary": name, "excluded": True, "wall_s": 0, "attempts": [], "results": res,
                 "discovery": disc, "binary_path": str(bins[name]), "coverage_policy": policy}, indent=1))

        todo = []
        for name in sorted(staged):
            cached = label_dir / "bins" / f"{name}.json"
            if only and name not in only:
                continue
            if cached.exists() and not args.force and not only and not args.full_suite:
                cached_data = json.loads(cached.read_text())
                if (not cached_data.get("excluded") and cached_data.get("coverage_policy") == policy
                        and cached_data.get("binary_sha256") == sha256(bins[name], {})
                        and cached_data.get("compiled_helpers") == helpers.get(name)
                        and cached_data.get("native_cli_inputs", {}) == args.native_cli_inputs
                        and cached_data.get("execution_lender_inputs", {}) == args.execution_lender_inputs
                        and cached_data.get("staged_target_verus_sha256") == staged_tv
                        and cached_data.get("native_driver") == (
                            args.native_runtime_inventory["driver"] if args.native_runtime_inventory else None)
                        and cached_data.get("internal_skips", {}) == (internal_skips if name == "cargo" else {})):
                    continue
            todo.append(name)

        # Listed concurrently: each fresh clone's first launch waits for macOS's
        # scan of it (about a minute each under load), and the scans overlap.
        discoveries = dict(zip(todo, owned.parallel_map(
            lambda n: list_tests(staged[n], env, binary_cwd(n, src)), todo, 16)))
        if args.full_suite and any(not d for d in discoveries.values()):
            raise SystemExit("full-suite has an empty harness discovery; build the required test features")
        # biggest first so the long files do not form the tail
        todo.sort(key=lambda n: -len(discoveries[n]))
        total = sum(len(d) for d in discoveries.values())
        log(f"label={args.label} solver={solver} binaries={len(todo)} tests={total} "
            f"parallel={args.parallel_bins}x{args.threads}")

        inv = {"start": dt.datetime.now().isoformat(timespec="seconds"), "binaries": todo,
               "argv": sys.argv, "env": env, "threads": args.threads, "parallel_bins": args.parallel_bins}
        t0 = time.monotonic()

        def work(name):
            check_prepared_sdk(args)
            native_runtime.check_files(staged_inputs, [staged[name], *stage_frontends]
                                       if staged_inputs else None)
            check_native_cli_inputs(args.native_cli_inputs)
            native_runtime.check_files(args.execution_lender_inputs)
            native_runtime.check(args.native_runtime_inventory,
                                 [bins[name], args.rust_verify] if args.native_runtime_inventory else None)
            clear_test_outputs(label_dir, name, discoveries[name])
            check_cargo_helpers(helpers.get(name))
            res = run_binary(name, staged[name], env, binary_cwd(name, src), args, label_dir / "logs", discoveries[name])
            check_prepared_sdk(args)
            check_cargo_helpers(helpers.get(name))
            check_native_cli_inputs(args.native_cli_inputs)
            native_runtime.check_files(args.execution_lender_inputs)
            native_runtime.check(args.native_runtime_inventory,
                                 [bins[name], args.rust_verify] if args.native_runtime_inventory else None)
            native_runtime.check_files(staged_inputs, [staged[name], *stage_frontends]
                                       if staged_inputs else None)
            res["discovery"] = discoveries[name]
            res["binary_path"] = str(bins[name])
            res["binary_sha256"] = sha256(bins[name], {})
            res["coverage_policy"] = policy
            res["compiled_helpers"] = helpers.get(name)
            res["native_cli_inputs"] = args.native_cli_inputs
            res["execution_lender_inputs"] = args.execution_lender_inputs
            res["staged_target_verus_sha256"] = staged_tv
            res["native_driver"] = (args.native_runtime_inventory["driver"]
                                    if args.native_runtime_inventory else None)
            res["internal_skips"] = internal_skips if name == "cargo" else {}
            res["finished"] = dt.datetime.now().isoformat(timespec="seconds")
            (label_dir / "bins" / f"{name}.json").write_text(json.dumps(res, indent=1))
            c = {}
            for r in res["results"].values():
                c[r["outcome"]] = c.get(r["outcome"], 0) + 1
            log(f"{name}: {res['wall_s']} s {c}")
            return name

        owned.parallel_map(work, todo, args.parallel_bins)

        check_native_cli_inputs(args.native_cli_inputs)
        native_runtime.check_files(args.execution_lender_inputs)
        native_runtime.check(args.native_runtime_inventory)
        native_runtime.check_files(staged_inputs)
        inv["wall_s"] = round(time.monotonic() - t0, 1)
        inv["end"] = dt.datetime.now().isoformat(timespec="seconds")
        meta.update({"label": args.label, "solver": str(solver), "verus_extra_args": args.verus_extra_args,
                     "threads": args.threads, "parallel_bins": args.parallel_bins,
                     "bin_wall": args.bin_wall, "test_stall": args.test_stall,
                     "excluded": excluded, "extras": extras, "coverage_policy": policy,
                     "compiled_helpers": helpers, "internal_skips": {"cargo": internal_skips},
                     "native_cli_inputs": args.native_cli_inputs,
                     "execution_lender_inputs": args.execution_lender_inputs,
                     "native_runtime_inventory": args.native_runtime_inventory,
                      "staged_consumed_inputs": staged_inputs})
        if prepared is not None:
            meta["prepared_sdk_inventory"] = {
                "request": str(prepared.request), "sdk": str(prepared.root),
                "entries": prepared.staged, "permission_from_inventory": False}
        if args.frontend != "verus" or args.capture_diagnostics:
            meta.update({"frontend": args.frontend, "capture_diagnostics": args.capture_diagnostics,
                         "staged_target_verus_sha256": staged_tv})
        if args.frontend == "trust-vc":
            version = args.builtins / "trustc-version.txt"
            meta.update({"solver": None, "rust_verify": str(args.rust_verify),
                         "rust_verify_sha256": sha256(args.rust_verify), "builtins": str(args.builtins),
                         "builtins_compiler": version.read_text().strip() if version.is_file() else "",
                         "reference": str(args.reference) if args.reference else None})
        inv["verus_write_check"] = verus_write_check(args.verus, marker)
        meta["verus_write_check"] = inv["verus_write_check"]
        if todo:
            meta["invocations"].append(inv)
        meta_path.write_text(json.dumps(meta, indent=1))
        rows, per_bin = load_results(label_dir, bins, extras, excluded)
        if args.full_suite and (set(per_bin) != set(bins) or any(not b["discovery"] for b in per_bin.values())):
            raise SystemExit("full-suite lacks positive discovered results for every manifest test target")
        score_lines, score_totals = [], None
        if args.frontend == "trust-vc":
            score_lines, score_totals = score_trust_vc(label_dir, rows, verus_src, args.reference)
            meta["score"] = score_totals
            meta_path.write_text(json.dumps(meta, indent=1))
        tot = write_reports(label_dir, args.label, rows, per_bin, bins, extras, excluded, meta, score_lines)
        log(f"done in {inv['wall_s']} s: {tot}; Verus checkout: {meta['verus_write_check']}")
        if todo:
            ledger = (Path(os.path.abspath(args.ledger.expanduser())) if args.ledger else out_root / "runs.csv")
            row = append_ledger(ledger, meta, tot, per_bin, score_totals, args.reference)
            log(f"ledger {ledger}: " + ",".join(str(row[k]) for k in LEDGER_FIELDS))
        if score_totals is not None:
            log("trust-vc score: " + ", ".join(f"{k}={v}" for k, v in score_totals.items()
                                                 if k not in ("tags", "compiler_commits")))
        if args.full_suite and any(count for outcome, count in tot.items() if outcome != "ok"):
            raise SystemExit(1)
    finally:
        try:
            check_prepared_sdk(args)
        finally:
            try:
                lock.unlink()
            except FileNotFoundError:
                pass


if __name__ == "__main__":
    try:
        with owned.scope(owned_stdin="--owned-stdin" in sys.argv[1:],
                         native_channel=_NATIVE_CHANNEL):
            main()
    finally:
        if _NATIVE_CHANNEL is not None:
            _NATIVE_CHANNEL.close()
