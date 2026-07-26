#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Build (and optionally test) the `rustc-driver` feature of `trust-vc-driver`
# against the **Trust toolchain's** rustc_private libraries.
#
# WHY A SCRIPT IS NEEDED
#   `trust-vc-driver`'s `driver` module is a real `rustc_driver::Callbacks`
#   front end: it does `extern crate rustc_{driver,hir,interface,middle}` behind
#   `feature = "rustc-driver"`. Those crates are NOT in the linked `trust`
#   toolchain's sysroot search path (rustc-dev is not installed as a rustup
#   component on a custom-linked toolchain), so a bare `cargo build
#   --features rustc-driver` fails with E0463 "can't find crate for rustc_*".
#
#   trust-vc is a submodule of Trust (the rustc fork). The fork's bootstrap
#   already compiles the rustc_private rlibs/rmetas and the matching host
#   proc-macro dylibs while building its own rustc_private tools (clippy, miri,
#   the trust-vc-trust-engine, ...). This script locates those artifacts in the
#   Trust `build/` tree and puts them on rustc's search path with `-L`, exactly
#   as bootstrap's rustc wrapper does via RUSTC_ADDITIONAL_SYSROOT_PATHS. Nothing
#   is stubbed or weakened: this builds the real driver against the real
#   compiler internals.
#
# WHAT GETS DISCOVERED (all derived from `rustc +trust --print sysroot`)
#   * stage2-rustc deps dir   — librustc_*.{rlib,rmeta} + librustc_driver.dylib
#   * rustc-private-sysroot   — host/ proc-macro dylibs (rustc_macros, …),
#                               selected by matching the librustc_middle build
#                               hash so it lines up with the deps dir above
#   * LLVM lib dir            — from Trust's bootstrap.toml `llvm-config --libdir`
#                               (Polly/PollyISL/… that linking rustc_driver pulls)
#   * zstd lib dir            — `brew --prefix zstd` (rustc_driver links -lzstd)
#
# USAGE
#   scripts/build-trust-vc-driver.sh                 # build the lib (rlib; no link)
#   scripts/build-trust-vc-driver.sh build [args…]   # same; extra args -> cargo rustc
#   scripts/build-trust-vc-driver.sh test  [args…]   # build + RUN the feature tests
#   scripts/build-trust-vc-driver.sh check [args…]   # type-check only (--emit=metadata)
#   scripts/build-trust-vc-driver.sh bin   [args…]   # build the `trust-vc-driver` BIN
#
#   `build`/`check` scope the rustc_private `-L` flags to the driver crate only
#   (via `cargo rustc -- <flags>`), so the dependency graph is NOT rebuilt and
#   the shared `target/` cache is left clean. `test` and `bin` must put the flags
#   on global RUSTFLAGS (they have to reach both the lib and the final linked
#   artifact — a test binary or the driver bin — that links it), so they rebuild
#   the dep graph under those flags — the heavier path. `bin` additionally prints
#   the resolved binary path plus the runtime dylib search path (DYLD_*), so a
#   caller (e.g. cargo-trust-vc's `--frontend=driver` wiring) can invoke the bin
#   standalone with the right `RUSTC_BOOTSTRAP=1` + DYLD environment.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

TOOLCHAIN="${TRUST_VC_TOOLCHAIN:-trust}"

die() { echo "build-trust-vc-driver: $*" >&2; exit 1; }

command -v rustc >/dev/null 2>&1 || die "rustc/rustup not found on PATH"
SYSROOT="$(rustc "+${TOOLCHAIN}" --print sysroot 2>/dev/null)" \
  || die "toolchain '${TOOLCHAIN}' not installed (link the Trust stage2: scripts/rustup-link-trust.sh)"

BUILD_TRIPLE_DIR="$(dirname "$SYSROOT")"                 # …/build/<host-triple>
HOST="$(rustc "+${TOOLCHAIN}" -vV | awk '/^host:/{print $2}')"
DEPS="$BUILD_TRIPLE_DIR/stage2-rustc/$HOST/release/deps"
[ -d "$DEPS" ] || die "stage2-rustc deps dir not found: $DEPS (build Trust's stage2 rustc first)"

# librustc_middle's build hash identifies this exact rustc build; use it to pick
# the rustc-private-sysroot whose collected host proc-macro dylibs match.
MIDDLE_HASH="$(ls "$DEPS"/librustc_middle-*.rmeta 2>/dev/null \
  | sed -E 's#.*/librustc_middle-([0-9a-f]+)\.rmeta#\1#' | head -1)"
[ -n "$MIDDLE_HASH" ] || die "no librustc_middle-*.rmeta in $DEPS"

PRIV_HOST=""
for d in "$BUILD_TRIPLE_DIR"/rustc-private-sysroots/*/; do
  if [ -e "$d$HOST/librustc_middle-$MIDDLE_HASH.rmeta" ] \
     && ls "$d"host/librustc_macros-*.dylib >/dev/null 2>&1; then
    PRIV_HOST="${d}host"
    break
  fi
done
[ -n "$PRIV_HOST" ] \
  || die "no rustc-private-sysroot host/ matching librustc_middle-$MIDDLE_HASH (re-run Trust's tool build)"

# LLVM lib dir: ask the same llvm-config Trust was configured with.
LLVM_CONFIG="$(grep -hE '^[[:space:]]*llvm-config' \
  "$(dirname "$BUILD_TRIPLE_DIR")"/../bootstrap.toml \
  "$(dirname "$BUILD_TRIPLE_DIR")"/../config.toml 2>/dev/null \
  | head -1 | sed -E 's/.*=[[:space:]]*"?([^"#]*)"?.*/\1/' | xargs 2>/dev/null || true)"
if [ -n "${LLVM_CONFIG:-}" ] && [ -x "$LLVM_CONFIG" ]; then
  LLVM_LIBDIR="$("$LLVM_CONFIG" --libdir)"
elif command -v llvm-config >/dev/null 2>&1; then
  LLVM_LIBDIR="$(llvm-config --libdir)"
else
  LLVM_LIBDIR="/opt/homebrew/opt/llvm@21/lib"
fi
[ -e "$LLVM_LIBDIR/libPolly.a" ] || [ -e "$LLVM_LIBDIR/libLLVM.dylib" ] \
  || echo "build-trust-vc-driver: warning: LLVM libs not found under $LLVM_LIBDIR" >&2

# zstd (rustc_driver links -lzstd).
ZSTD_PREFIX="$(brew --prefix zstd 2>/dev/null || true)"
ZSTD_LIBDIR="${ZSTD_PREFIX:+$ZSTD_PREFIX/lib}"
[ -n "$ZSTD_LIBDIR" ] && [ -d "$ZSTD_LIBDIR" ] || ZSTD_LIBDIR="/opt/homebrew/lib"

LFLAGS=(-L "$DEPS" -L "$PRIV_HOST" -L "native=$LLVM_LIBDIR" -L "native=$ZSTD_LIBDIR")

echo "==> Trust toolchain : $TOOLCHAIN ($SYSROOT)"
echo "==> rustc_* deps    : $DEPS"
echo "==> proc-macro host : $PRIV_HOST"
echo "==> LLVM libdir     : $LLVM_LIBDIR"
echo "==> zstd libdir     : $ZSTD_LIBDIR"

MODE="${1:-build}"; [ $# -gt 0 ] && shift || true

export RUSTUP_TOOLCHAIN="$TOOLCHAIN"
export RUSTC_BOOTSTRAP=1   # permit #![feature(rustc_private)] on the fork rustc

case "$MODE" in
  build)
    # Scope the rustc_private -L flags to the driver crate only; deps stay cached.
    exec cargo rustc -p trust-vc-driver --features rustc-driver --lib "$@" -- "${LFLAGS[@]}"
    ;;
  check)
    exec cargo rustc -p trust-vc-driver --features rustc-driver --lib "$@" -- \
      "${LFLAGS[@]}" --emit=metadata
    ;;
  test)
    # Test binaries link the feature-on lib, so the flags must be global. Also
    # export a runtime lib path so the test exes find librustc_driver.dylib + LLVM.
    #
    # `-C prefer-dynamic`: the `-L $DEPS` search path exposes the stage2 rustc's
    # own precompiled std/core/alloc rlibs, which collide with the test binary's
    # sysroot std ("cannot satisfy dependencies so `std` only shows up once").
    # Linking std dynamically (the dylib is canonical) resolves the duplication;
    # the std/LLVM dylibs are then found at run time via DYLD_FALLBACK_LIBRARY_PATH.
    export RUSTFLAGS="-Zno-trust-verify -Cprefer-dynamic ${LFLAGS[*]}"
    export DYLD_FALLBACK_LIBRARY_PATH="$DEPS:$LLVM_LIBDIR:$ZSTD_LIBDIR:$SYSROOT/lib:/opt/homebrew/lib"
    # --tests skips doctests (the linked `trust` toolchain ships no rustdoc).
    exec cargo test -p trust-vc-driver --features rustc-driver --tests "$@"
    ;;
  bin)
    # The `trust-vc-driver` bin is a final linked artifact that pulls in
    # librustc_driver.dylib, so — exactly like `test` — the flags must be global
    # and std must link dynamically to avoid the stage2-std/sysroot-std collision.
    export RUSTFLAGS="-Zno-trust-verify -Cprefer-dynamic ${LFLAGS[*]}"
    RUNTIME_DYLD="$DEPS:$LLVM_LIBDIR:$ZSTD_LIBDIR:$SYSROOT/lib:/opt/homebrew/lib"
    export DYLD_FALLBACK_LIBRARY_PATH="$RUNTIME_DYLD"
    cargo build -p trust-vc-driver --features rustc-driver \
      --bin trust-vc-driver "$@"
    # Emit machine-readable pointers so a caller can run the bin standalone.
    PROFILE_DIR="debug"
    for a in "$@"; do [ "$a" = "--release" ] && PROFILE_DIR="release"; done
    BIN_PATH="$REPO_ROOT/target/$PROFILE_DIR/trust-vc-driver"
    echo "==> driver bin      : $BIN_PATH"
    echo "==> runtime DYLD    : $RUNTIME_DYLD"
    echo "TRUST_VC_DRIVER_BIN=$BIN_PATH"
    echo "TRUST_VC_DRIVER_DYLD=$RUNTIME_DYLD"
    ;;
  *)
    die "unknown mode '$MODE' (expected: build | check | test | bin)"
    ;;
esac
