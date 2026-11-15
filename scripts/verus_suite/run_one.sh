#!/bin/bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
#
# Run ONE Verus test (or a few, space separated) outside the suite runner, in the
# stage of an existing label, with shim event logs and SMT transcripts on.
#
#   run_one.sh <stage-label> <solver: ay|z3> <outdir> <binary> <test-name> [more test names]
#
# The environment is the one run_suite.py builds (README.md). Output:
#   <outdir>/libtest.jsonl   libtest JSON, with --show-output (stdout of passing tests too)
#   <outdir>/events/         shim event log per test
#   <outdir>/transcripts/    exact bytes sent to / received from the solver, per process
#
# Settings, from this environment:
#   VERUS_SUITE_OUT_ROOT  holds runs/<stage-label>/stage (default: .verus-suite/ at the repo root)
#   AY_BIN                the ay binary; REQUIRED for solver ay, no default
#   SHIM                  VERUS_Z3_PATH (default: ay_z3shim.py next to this script)
#   VERUS_SUITE_DYLD      directory holding librustc_driver-eea6b8737cd03a8e.dylib, the exact
#                         file the prebuilt binaries load (default: rustup's 1.95.0 lib/)
#   VERUS_EXTRA_ARGS      default: "-V no-solver-version-check" for ay, unset for z3
#   AY_SHIM_ARGS          default "-q --z3-mode"; AY_SHIM_QUERY_WALL_S default 60
#   every other AY_SHIM_* and TOP3_* variable that is set passes through unchanged, so a shim
#   gets every setting it reads, including ones this script does not know: ay's
#   fix-simulation shim (ay-z3shim-top3) exits at once without TOP3_Z3, and a solver that
#   ends the session at AIR's first contact makes rust_verify abort with SIGABRT.
#   AY_SHIM_EVENT_DIR and AY_SHIM_TRANSCRIPT_DIR are always <outdir>/events and
#   <outdir>/transcripts, and SHIM_SOLVER is never passed through (the solver argument
#   decides it), so an ay run cannot silently measure z3.
# The environment of the test binary is built from scratch (env -i). DYLD_LIBRARY_PATH is
# set on that final exec, never inherited: macOS strips DYLD_* variables whenever they pass
# through a protected binary such as /bin/bash.
# Exit status: 2 when this script refuses (usage, AY_BIN, stage, library, rustup), 0 once
# the test binary has run, whatever the tests did; the drivers stop on a refusal.
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
repo=$(cd "$here/../.." && pwd)
root=${VERUS_SUITE_OUT_ROOT:-$repo/.verus-suite}
die() { echo "run_one.sh: $*" >&2; exit 2; }
[ $# -ge 5 ] || die "usage: run_one.sh <stage-label> <ay|z3> <outdir> <binary> <test-name> [more test names]"
label=$1; solver=$2; out=$3; bin=$4; shift 4
case $solver in
  ay) [ -n "${AY_BIN:-}" ] || die "AY_BIN is required for solver ay and has no default: set it to the ay binary to measure (a default path once measured a stale build without saying so)"
      [ -x "$AY_BIN" ] && [ -f "$AY_BIN" ] || die "AY_BIN=$AY_BIN is not an executable file" ;;
  z3) ;;
  *) die "solver must be ay or z3, not '$solver'" ;;
esac
stage=$root/runs/$label/stage/source
[ -d "$stage/rust_verify_test" ] || die "no stage at $stage: run run_suite.py --label $label (with this out root) first"
dyld=${VERUS_SUITE_DYLD:-}
if [ -z "$dyld" ]; then
  # STOCK-AS-ORACLE (docs/rulings.md: kept, pinned, never a blocker): upstream
  # Verus's PREBUILT binaries link stock rustc 1.95.0's librustc_driver-eea6b8737cd03a8e;
  # this only locates that dylib to run the third-party baseline, and builds no ALab
  # code. It is never installed: without RUSTUP_AUTO_INSTALL=0 `rustup which` on a
  # missing toolchain downloads it (measured, rustup 1.29).
  rustc_path=$(RUSTUP_AUTO_INSTALL=0 rustup which --toolchain 1.95.0 rustc 2>/dev/null) || die "NOT RUN: oracle rustc 1.95.0 not installed; set VERUS_SUITE_DYLD to a directory holding librustc_driver-eea6b8737cd03a8e.dylib"
  dyld=$(cd "$(dirname "$rustc_path")/../lib" && pwd)
fi
driver=librustc_driver-eea6b8737cd03a8e.dylib
[ -f "$dyld/$driver" ] || die "no $driver in $dyld: the prebuilt Verus binaries load exactly that file and dyld halts them at launch without it (set VERUS_SUITE_DYLD)"
mkdir -p "$out/events" "$out/transcripts"
out=$(cd "$out" && pwd)
env_common=(
  VERUS_IN_VARGO=1 RUSTC_BOOTSTRAP=1 RUST_MIN_STACK=20971520
  VARGO_TARGET_DIR=$stage/target-verus/debug
  DYLD_LIBRARY_PATH=$dyld
  VERUS_Z3_PATH=${SHIM:-$here/ay_z3shim.py}
  AY_SHIM_EVENT_DIR=$out/events AY_SHIM_TRANSCRIPT_DIR=$out/transcripts
  AY_SHIM_QUERY_WALL_S=${AY_SHIM_QUERY_WALL_S:-60}
  AY_SHIM_ARGS="${AY_SHIM_ARGS:--q --z3-mode}"
)
[ -z "${AY_BIN:-}" ] || env_common+=(AY_BIN=$AY_BIN)
for v in $(compgen -e); do
  case $v in
    AY_SHIM_EVENT_DIR|AY_SHIM_TRANSCRIPT_DIR|AY_SHIM_QUERY_WALL_S|AY_SHIM_ARGS) ;;  # set above
    AY_SHIM_*|TOP3_*) env_common+=("$v=${!v}") ;;
  esac
done
if [ "$solver" = z3 ]; then
  env_common+=(SHIM_SOLVER=z3:$stage/target-verus/debug/z3)
  if [ -n "${VERUS_EXTRA_ARGS+x}" ]; then env_common+=(VERUS_EXTRA_ARGS="$VERUS_EXTRA_ARGS"); fi
else
  env_common+=(VERUS_EXTRA_ARGS="${VERUS_EXTRA_ARGS:--V no-solver-version-check}")
fi
case "$bin" in
  cargo-verus.*) cd "$stage/cargo-verus" ;;
  *) cd "$stage/rust_verify_test" ;;
esac
env -i PATH="$PATH" HOME="$HOME" USER="$USER" TMPDIR="${TMPDIR:-/tmp}" "${env_common[@]}" \
  "$stage/target.noindex/debug/deps/$bin" -Z unstable-options --format json --report-time \
  --show-output --test-threads 1 --include-ignored --exact "$@" > "$out/libtest.jsonl" 2> "$out/libtest.stderr" || true
python3 - "$out/libtest.jsonl" <<'EOF'
import json, sys
for l in open(sys.argv[1]):
    try: e = json.loads(l)
    except Exception: continue
    if e.get("type") == "test" and e.get("event") in ("ok", "failed", "ignored"):
        print(e["event"], e["name"], e.get("exec_time", ""))
EOF
