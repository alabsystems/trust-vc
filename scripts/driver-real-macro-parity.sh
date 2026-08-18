#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# The FIRST positive real-macro driver-vs-syn PARITY WITNESS, made repeatable.
#
# WHAT THIS PROVES
#   The rustc-driver front end (`trust-vc-driver`) and the trusted **syn** path
#   agree, per function, on a fixture built from REAL `#[trust_vc::contract(..)]`
#   macros — not hand-written marker shims. `inc`/`double` VERIFY on both;
#   `inc_bad` (a deliberately FALSE postcondition) is REFUTED on both. The driver
#   is a NON-authoritative, parallel VC producer: syn stays authoritative, and
#   the script HARD-FAILS if the driver ever reports Verified where syn does not
#   (a driver soundness bug — the driver proving more than syn). This is a
#   distinct evidence record, NEVER a manifest flip or a promotion.
#
# WHY THIS PATH (and not `targo trust-vc check --frontend=driver`)
#   The cargo `--frontend=driver` wiring (fb16545) drives the same comparison,
#   but its cargo-verus forwarding rebuilds the fixture's whole dependency graph
#   under a distinct `verus` lib-metadata (ay included) — a from-scratch build
#   that TIMES OUT. This script instead reuses the workspace's already-built
#   (Trust-toolchain) `trust_vc` proc-macro dylib + `trust_vc_core` rlib as the
#   driver's `--extern`s and scans the same source with the syn path, so the ONLY
#   heavy step is building the nightly driver bin itself (unavoidable, and cached
#   after the first `scripts/build-trust-vc-driver.sh bin`).
#
# OUTPUT (identical wire format to the cargo `--frontend=driver` witness)
#   TRUST_VC_DRIVER_SYN_PARITY\t<fn>\tdriver=<v>\tsyn=<v>\t{agree|differ}
#   TRUST_VC_DRIVER_SYN_PARITY_SUMMARY\tcompared=<N>\tagree=<M>\tskipped_unsupported=<K>
#
# EXIT STATUS
#   0  iff compared > 0 AND every compared function agrees AND the driver never
#      proved more than syn (the witness is positive).
#   1  otherwise (no in-fragment targets, a disagreement, or a soundness
#      violation) — a red witness must never be recorded as green.
#
# USAGE
#   scripts/driver-real-macro-parity.sh
#     Builds/locates the driver bin, then runs the witness.
#   TRUST_VC_DRIVER_BIN=... TRUST_VC_DRIVER_DYLD=... scripts/driver-real-macro-parity.sh
#     Reuses a prebuilt bin (skips the heavy build) — the paths printed by
#     `scripts/build-trust-vc-driver.sh bin`.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

FIXTURE_DIR="$REPO_ROOT/crates/trust-vc-driver-parity-fixture"
FIXTURE_SRC="$FIXTURE_DIR/src/lib.rs"
FIXTURE_CRATE_NAME="trust_vc_driver_parity_fixture"
DEPS_DIR="$REPO_ROOT/target/debug/deps"

die() { echo "driver-real-macro-parity: $*" >&2; exit 1; }

[ -f "$FIXTURE_SRC" ] || die "fixture source missing: $FIXTURE_SRC"
command -v rustc >/dev/null 2>&1 || die "rustc not found on PATH"
command -v python3 >/dev/null 2>&1 || die "python3 not found on PATH"

# --- 1. Driver bin + its runtime dylib search path ---------------------------
# Reuse a prebuilt bin if the caller exported one; otherwise build it (the heavy,
# but incremental-after-first, step). `build-trust-vc-driver.sh bin` prints the
# resolved BIN + DYLD as `TRUST_VC_DRIVER_BIN=`/`TRUST_VC_DRIVER_DYLD=` lines.
if [ -n "${TRUST_VC_DRIVER_BIN:-}" ] && [ -x "${TRUST_VC_DRIVER_BIN}" ]; then
  DRIVER_BIN="$TRUST_VC_DRIVER_BIN"
  DRIVER_DYLD="${TRUST_VC_DRIVER_DYLD:-}"
  echo "==> driver bin (prebuilt): $DRIVER_BIN"
else
  echo "==> building driver bin via scripts/build-trust-vc-driver.sh bin ..."
  BUILD_OUT="$(bash "$REPO_ROOT/scripts/build-trust-vc-driver.sh" bin)"
  echo "$BUILD_OUT" | sed 's/^/    /'
  DRIVER_BIN="$(printf '%s\n' "$BUILD_OUT" | sed -n 's/^TRUST_VC_DRIVER_BIN=//p' | tail -1)"
  DRIVER_DYLD="$(printf '%s\n' "$BUILD_OUT" | sed -n 's/^TRUST_VC_DRIVER_DYLD=//p' | tail -1)"
fi
[ -x "$DRIVER_BIN" ] || die "driver bin not found/executable: ${DRIVER_BIN:-<empty>}"

# --- 2. targo-trust-vc bin (the trusted syn path) ----------------------------
# The package is `targo-trust-vc`; it ships the Trust-native `targo-trust-vc`
# bin and a back-compat `cargo-trust-vc` alias bin (same shim). Prefer the
# native bin, fall back to the alias, honor the override.
if [ -n "${CARGO_TRUST_VC_BIN:-}" ]; then
  CARGO_TRUST_VC="$CARGO_TRUST_VC_BIN"
elif [ -x "$REPO_ROOT/target/debug/targo-trust-vc" ]; then
  CARGO_TRUST_VC="$REPO_ROOT/target/debug/targo-trust-vc"
else
  CARGO_TRUST_VC="$REPO_ROOT/target/debug/cargo-trust-vc"
fi
if [ ! -x "$CARGO_TRUST_VC" ]; then
  echo "==> targo-trust-vc bin missing; building it ..."
  cargo build -p targo-trust-vc >/dev/null 2>&1 \
    || die "failed to build targo-trust-vc (needed for the authoritative syn path)"
fi
[ -x "$CARGO_TRUST_VC" ] || die "targo-trust-vc bin not found: $CARGO_TRUST_VC"

# --- 3. Real-macro externs from the already-built workspace artifacts ---------
# The driver bin compiles the fixture's REAL macros, so it needs the `trust_vc`
# proc-macro dylib and the `trust_vc_core` rlib (whose `__driver_markers` the
# `--cfg trust_vc_driver` expansion targets). Pick the newest of each; `-L
# dependency` resolves their transitive deps by exact hash. These are the SAME
# rustc build as the bin's sysroot (default == +trust toolchain), so they load.
[ -d "$DEPS_DIR" ] || die "workspace deps dir missing: $DEPS_DIR (run \`targo build\` first)"
PROC_MACRO="$(ls -t "$DEPS_DIR"/libtrust_vc-*.dylib 2>/dev/null | head -1)"
CORE_RLIB="$(ls -t "$DEPS_DIR"/libtrust_vc_core-*.rlib 2>/dev/null | head -1)"
[ -n "$PROC_MACRO" ] || die "no libtrust_vc-*.dylib in $DEPS_DIR (run \`targo build\` first)"
[ -n "$CORE_RLIB" ]  || die "no libtrust_vc_core-*.rlib in $DEPS_DIR (run \`targo build\` first)"
SYSROOT="$(rustc --print sysroot)"

WORK="$(mktemp -d "${TMPDIR:-/tmp}/trust_vc_driver_parity.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT
DRIVER_TSV="$WORK/driver.tsv"
SYN_JSON="$WORK/syn.json"

echo "==> proc-macro extern : $PROC_MACRO"
echo "==> trust_vc_core rlib : $CORE_RLIB"
echo "==> sysroot            : $SYSROOT"

# --- 4. Driver verdicts (NON-authoritative, parallel producer) ---------------
echo "==> running the rustc-driver front end on the real-macro fixture ..."
RUSTC_BOOTSTRAP=1 \
DYLD_FALLBACK_LIBRARY_PATH="${DRIVER_DYLD:-$SYSROOT/lib}" \
"$DRIVER_BIN" \
  "$FIXTURE_SRC" \
  --edition=2021 --crate-type=lib --crate-name="$FIXTURE_CRATE_NAME" \
  --emit=metadata --out-dir="$WORK/out" \
  --sysroot "$SYSROOT" \
  -L dependency="$DEPS_DIR" \
  --extern trust_vc="$PROC_MACRO" \
  --extern trust_vc_core="$CORE_RLIB" \
  -Awarnings \
  >"$DRIVER_TSV" 2>"$WORK/driver.stderr" || true
if ! grep -q '^TRUST_VC_DRIVER_RESULT' "$DRIVER_TSV"; then
  echo "---- driver stderr ----" >&2
  sed 's/^/    /' "$WORK/driver.stderr" >&2 || true
  die "driver bin emitted no TRUST_VC_DRIVER_RESULT records (compile failure?)"
fi

# --- 5. Authoritative syn verdicts (source scan; no dep rebuild) -------------
echo "==> running the trusted syn path (targo trust-vc check) on the fixture ..."
# `check` exits non-zero when a target is refuted (inc_bad is intentionally so),
# which is expected here — we consume the JSON verdicts, not the exit status.
( cd "$FIXTURE_DIR" && "$CARGO_TRUST_VC" check --json . ) >"$SYN_JSON" 2>"$WORK/syn.stderr" || true
python3 -c 'import json,sys; json.load(open(sys.argv[1]))' "$SYN_JSON" 2>/dev/null \
  || { echo "---- syn stderr ----" >&2; sed 's/^/    /' "$WORK/syn.stderr" >&2 || true; \
       die "targo trust-vc check did not emit valid JSON"; }

# --- 6. Compare + emit the witness (same wire format as --frontend=driver) ---
python3 - "$DRIVER_TSV" "$SYN_JSON" <<'PY'
import json, sys

driver_tsv, syn_json = sys.argv[1], sys.argv[2]

# Driver verdicts: function -> verdict (Verified/Refuted/Unknown/Error/Unsupported*)
driver = {}
with open(driver_tsv) as fh:
    for line in fh:
        cols = line.rstrip("\n").split("\t")
        if cols and cols[0] == "TRUST_VC_DRIVER_RESULT" and len(cols) >= 3:
            driver[cols[1]] = cols[2]

# Syn verdicts, mapped into the driver's coarse vocabulary (matches
# cargo-trust-vc's syn_verdict_word).
SYN_MAP = {
    "verified": "Verified",
    "counterexample": "Refuted",
    "unknown": "Unknown",
    "error": "Error",
    "skipped": "Skipped",
}
report = json.load(open(syn_json))
syn = {}
for f in report.get("functions", []):
    syn[f["name"]] = SYN_MAP.get(f.get("result", ""), f.get("result", "?"))

UNSUPPORTED = {"UnsupportedType", "UnsupportedContract"}
compared = agree = proves_more = skipped = 0
records = []
for fn in sorted(driver):
    dv = driver[fn]
    if dv in UNSUPPORTED:
        skipped += 1
        continue
    sv = syn.get(fn, "Absent")
    ok = (dv == sv)
    pm = (dv == "Verified" and sv != "Verified")   # the UNSOUND direction
    compared += 1
    agree += 1 if ok else 0
    proves_more += 1 if pm else 0
    records.append((fn, dv, sv, ok, pm))
    print(f"TRUST_VC_DRIVER_SYN_PARITY\t{fn}\tdriver={dv}\tsyn={sv}\t{'agree' if ok else 'differ'}")

print(f"TRUST_VC_DRIVER_SYN_PARITY_SUMMARY\tcompared={compared}\tagree={agree}\tskipped_unsupported={skipped}")

# --- Gate ---
if proves_more:
    bad = ", ".join(f"{fn} (driver=Verified, syn={sv})" for fn, dv, sv, ok, pm in records if pm)
    print(f"FAIL: driver proved MORE than syn for: {bad}. This is a driver soundness "
          f"bug — the driver must never report Verified where syn does not. "
          f"NOT a witness; NOT a manifest flip.", file=sys.stderr)
    sys.exit(1)
if compared == 0:
    print("FAIL: compared=0 — the driver classified no fixture function as an "
          "in-fragment target, so there is no parity witness to record.", file=sys.stderr)
    sys.exit(1)
if agree != compared:
    diffs = ", ".join(f"{fn} (driver={dv}, syn={sv})" for fn, dv, sv, ok, pm in records if not ok)
    print(f"FAIL: driver-vs-syn disagreement for: {diffs}.", file=sys.stderr)
    sys.exit(1)

print(f"OK: positive real-macro driver-vs-syn parity witness — compared={compared}, "
      f"agree={agree}, skipped_unsupported={skipped}, driver_proves_more=0.")
PY
