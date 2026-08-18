#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Run the AY native-deductive proof harness on the STOCK toolchain — no Trust
# rustc-fork stage2 build required (minutes, not hours).
#
# WHY THIS WORKS WITHOUT THE FORK
#   The trust-vc verification ENGINE (`trust-vc-core` + the `trust_vc` proc
#   macros + the `ay` SMT solver crates) has NO `rustc_private` dependency and
#   NO `#![feature(...)]`: `verify_function_from_file` parses the fixture itself
#   and runs the AY engine + trust-vc-kernel, all pure Rust. Only the SEPARATE
#   `trust-vc-driver` rustc-driver links `rustc_private` and needs the fork; the
#   harness tests below do not use it.
#
# WHAT THIS SCRIPT HANDLES (the two blockers on stock rustc)
#   1. `rustc` RESOLUTION. Homebrew cargo carries no baked-in rustc path: it
#      resolves `rustc` from PATH, where `~/.cargo/bin/rustc` (the rustup shim)
#      shadows homebrew's. The shim honors rust-toolchain.toml's
#      channel="trust" pin, so while the fork is mid-rebuild every unit dies
#      with "'rustc' is not installed for the custom toolchain 'trust'" — even
#      though cargo itself was the stock one. The script therefore pins RUSTC
#      to the rustc that ships WITH the chosen cargo, so both halves of the
#      toolchain come from the same stock install.
#   2. `RUSTFLAGS=""` clears any ambient Trust-only flags for this invocation.
#      The committed .cargo/config.toml no longer sets `build.rustflags` (Targo
#      injects its own per-unit off-switch), so this is purely defensive: it
#      protects the run from a caller's exported Trust-only RUSTFLAGS, which
#      stock rustc would reject as unknown options.
#   Dependencies remain on the same exact, locked Git revisions used by normal
#   and downstream builds.  No local checkout patching is involved.
#
# A dedicated CARGO_TARGET_DIR (`target-stock`) keeps stock artifacts from
# thrashing the Trust-toolchain build cache in `target/`.
#
# USAGE
#   scripts/stock-harness.sh                # run the curated AY real-fixture suite
#   scripts/stock-harness.sh --all          # run EVERY ay_* native-proof driver (full corpus)
#   scripts/stock-harness.sh <test_target>  # run a single integration test target
#   scripts/stock-harness.sh --features proof-certificates <test_target>
#
# Extra args after a recognized test target (or any leading flags) are forwarded
# to `cargo test`.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

# Prefer the homebrew/stock cargo (ignores rust-toolchain.toml's channel="trust");
# fall back to a rustup `stable` toolchain via `+stable` if only rustup is present.
if [ -x /opt/homebrew/bin/cargo ]; then
  CARGO=(/opt/homebrew/bin/cargo)
  # See header item 1: without this, homebrew cargo finds the rustup rustc
  # shim on PATH and the channel="trust" pin kills the build.
  export RUSTC=/opt/homebrew/bin/rustc
elif command -v rustup >/dev/null 2>&1; then
  CARGO=(cargo +stable)
else
  CARGO=(cargo)
fi

# Curated AY real-body / soundness fixtures verified natively by the engine.
DEFAULT_TARGETS=(
  ay_eval_verdict_realbody
  ay_optimum_floor_realbody
  ay_incumbent_vig_realbody
  ay_incumbent_accept_composite     # the composite-return form
  ay_verdict_chain
)

ARGS=("$@")
if [ "${#ARGS[@]}" -ge 1 ] && { [ "${ARGS[0]}" = "--all" ] || [ "${ARGS[0]}" = "--full" ]; }; then
  # Comprehensive: auto-discover and run EVERY ay_* native-proof driver in one
  # cargo invocation (future-proof as drivers are added). The workspace lock is
  # the authoritative dependency graph for both curated and full runs.
  TEST_ARGS=()
  for f in crates/trust-vc-core/tests/ay_*.rs; do
    TEST_ARGS+=(--test "$(basename "$f" .rs)")
  done
  echo "==> stock harness (FULL): ${#TEST_ARGS[@]} discovered ay_* native-proof drivers"
  CARGO_TARGET_DIR="$REPO_ROOT/target-stock" RUSTFLAGS="" \
    "${CARGO[@]}" test --locked -p trust-vc-core "${TEST_ARGS[@]}"
elif [ "${#ARGS[@]}" -eq 0 ]; then
  set -- "${DEFAULT_TARGETS[@]}"
  TARGETS=("$@")
  echo "==> stock harness: running curated AY real-fixture suite (${#TARGETS[@]} targets)"
  for t in "${TARGETS[@]}"; do
    echo "----- $t -----"
    CARGO_TARGET_DIR="$REPO_ROOT/target-stock" RUSTFLAGS="" \
      "${CARGO[@]}" test --locked -p trust-vc-core --test "$t"
  done
else
  # A basename naming an integration-test source is a Cargo target, not a test
  # name filter. Preserve the caller's argument order while expanding that one
  # token to `--test <target>`; without this translation Cargo compiles every
  # integration target before applying the filter.
  CARGO_ARGS=()
  FOUND_TEST_TARGET=0
  for arg in "${ARGS[@]}"; do
    if [ "$FOUND_TEST_TARGET" -eq 0 ] && [ -f "crates/trust-vc-core/tests/$arg.rs" ]; then
      CARGO_ARGS+=(--test "$arg")
      FOUND_TEST_TARGET=1
    else
      CARGO_ARGS+=("$arg")
    fi
  done
  echo "==> stock harness: cargo test --locked -p trust-vc-core ${CARGO_ARGS[*]}"
  CARGO_TARGET_DIR="$REPO_ROOT/target-stock" RUSTFLAGS="" \
    "${CARGO[@]}" test --locked -p trust-vc-core "${CARGO_ARGS[@]}"
fi
