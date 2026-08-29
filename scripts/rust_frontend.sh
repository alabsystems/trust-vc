#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Resolve the cargo-frontend subcommand binary for the TOOLCHAIN THAT IS PINNED,
# then exec the requested gate with it. Nothing here relaxes a check: the same
# `fmt --all --check` / `tippy ... -D warnings` runs, under whatever name the
# pinned toolchain ships it as.
#
# WHY THIS EXISTS. `rust-toolchain.toml` pins `channel = "trust"` — the
# self-hosted Trust stage build, a rustc fork — and that fork ships its
# frontends under RENAMED binaries, so the stock spelling cannot dispatch.
# Measured 2026-08-22 against the linked `trust` sysroot
# (~/.rustup/toolchains/trust -> .../build/aarch64-apple-darwin/stage1):
#
#   $ ls "$(rustc --print sysroot)"/bin
#   ay cargo clean rustc rustdoc targo targo-fmt targo-miri targo-tippy
#   targo-trust tippy tippy-driver trust-analyzer trust-miri trustc trustd
#   trustdoc trustfmt ty
#
# There is no `cargo-fmt` and no `cargo-clippy` in that list; cargo resolves
# `cargo <sub>` by looking for a `cargo-<sub>` sibling, so `cargo fmt` and
# `cargo clippy` both die at component lookup. The frontends are there under
# `targo-fmt` / `targo-tippy`, and reached as `targo fmt` (trustfmt 1.9.0-trust)
# and `targo tippy` (tippy 0.1.0) — both measured on the same date at 52e0a7031.
#
# THE SILENT-FALLBACK HOLE THIS CLOSES. `rustc` only honours the pin through the
# rustup shim. `~/.cargo/bin` is not on the default PATH on this machine, so with
# an ordinary `PATH=/opt/homebrew/bin:/usr/bin:/bin` the pin is not read by
# anything: measured the same day,
#
#   $ rustc --version                  -> rustc 1.96.0 (ac68faa20) (Homebrew)
#   $ ls "$(rustc --print sysroot)"/bin -> cargo cargo-clippy cargo-fmt
#                                          clippy-driver ... rustfmt
#
# so the stock passthrough below WOULD fire and a `-D warnings` gate would run a
# DIFFERENT LINT SET, against a different rustc, under the same name — and report
# clean. That is exactly how six `-D warnings` violations accumulated unnoticed on
# main in the sibling `clean` repo (scripts/rust_frontend.sh there, 2026-08-22).
# The pin check below refuses instead, with the remedy.
#
# WHAT IS GATED TODAY, and what is not. `fmt --all --check` IS the gate: it is
# green on this branch, and it was not before — the guarded run surfaced exactly
# one violation invisible to everything in this repo until now (a doubled blank
# line at crates/trust-vc-core/src/ir_lowering/dispatch/macros.rs:909, fixed in
# the commit that added this file). `clippy` is NOT yet a `-D warnings` gate.
# Measured through this script on 2026-08-22 at cbf061cb7,
# `clippy --workspace --all-targets` emits 109 finding lines (lib/lib-test
# duplicates included): 100 in trust-vc-core, 7 in trust-vc-trust-engine, and 2 in
# the `[patch]`ed sibling `../ay` working tree, which is outside this repository
# entirely (a trailing `-D warnings` reaches only selected packages, so those two
# cannot fail the gate — but they cannot be fixed from here either). Turning that
# red into a gate is a campaign, not a guard, and asserting a gate that cannot
# pass is what teaches the bypass.
# Run it through THIS script anyway — the point of the guard is that a clippy run
# either uses the pinned frontend or refuses, never quietly a third thing.
#
# Usage:  scripts/rust_frontend.sh fmt --all --check
#         scripts/rust_frontend.sh clippy --workspace --all-targets -- -D warnings
set -euo pipefail

if [ "$#" -lt 1 ]; then
  echo "usage: rust_frontend.sh <fmt|clippy> [args...]" >&2
  exit 2
fi

sub="$1"; shift

case "$sub" in
  fmt)    candidates=("fmt") ;;
  clippy) candidates=("clippy" "tippy") ;;
  *)      candidates=("$sub") ;;
esac

sysroot="$(rustc --print sysroot)"
# Canonicalise: the Trust frontends refuse a sysroot reached through a symlink
# ("protected Trust toolchain directory ... traverses a symlink or non-canonical
# path"), and the linked `trust` toolchain IS a symlink into the build tree, so
# every path through rustup is non-canonical by construction.
if command -v python3 >/dev/null 2>&1; then
  sysroot="$(python3 -c 'import os,sys;print(os.path.realpath(sys.argv[1]))' "$sysroot")"
fi
bindir="$sysroot/bin"

# The pin must actually be the toolchain we resolved. `rust-toolchain.toml` names
# the channel, but `rustc` only honours it through the rustup shim: if that
# toolchain is not linked, or ~/.cargo/bin is not on PATH, `rustc` is some other
# installation and `$bindir/cargo-clippy` below exists — so the stock passthrough
# fires and the gate runs a DIFFERENT LINT SET under the same name. That is the
# one thing this script promises not to do ("Nothing here relaxes a check").
pinned_channel=""
repo_root="$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)"
if [ -f "$repo_root/rust-toolchain.toml" ]; then
  pinned_channel="$(sed -n 's/^[[:space:]]*channel[[:space:]]*=[[:space:]]*"\([^"]*\)".*/\1/p' \
    "$repo_root/rust-toolchain.toml" | head -n 1)"
fi
case "$pinned_channel" in
  ""|stable|beta|nightly|nightly-*|1.*) : ;;   # upstream channels: passthrough is correct
  *)
    if [ ! -x "$bindir/${pinned_channel}c" ] && [ ! -x "$bindir/$pinned_channel" ]; then
      echo "rust_frontend.sh: rust-toolchain.toml pins channel \"$pinned_channel\", but the" >&2
      echo "  resolved sysroot is not that toolchain:" >&2
      echo "    sysroot: $sysroot" >&2
      echo "  Running the gate here would silently use a different frontend and a" >&2
      echo "  different lint set. Refusing." >&2
      echo "  Fix: link the toolchain and put the rustup shim first on PATH, e.g." >&2
      echo "    rustup toolchain link $pinned_channel <path-to-stage1-or-stage2-sysroot>" >&2
      echo "    export PATH=\"\$HOME/.cargo/bin:\$PATH\"" >&2
      exit 2
    fi
    ;;
esac

# Try, in order: the stock `cargo <sub>`, then every (driver, subcommand) pair
# the pinned sysroot actually ships. The stock spelling comes FIRST so that on
# an ordinary upstream toolchain this script is a no-op passthrough.
for name in "${candidates[@]}"; do
  if [ -x "$bindir/cargo-$name" ]; then
    exec cargo "$name" "$@"
  fi
done

for driver in targo cargo; do
  [ -x "$bindir/$driver" ] || continue
  for name in "${candidates[@]}"; do
    if [ -x "$bindir/$driver-$name" ]; then
      exec "$bindir/$driver" "$name" "$@"
    fi
  done
done

echo "rust_frontend.sh: no frontend for '$sub' in $bindir" >&2
echo "  looked for: cargo-<n> and <targo|cargo>-<n> with n in: ${candidates[*]}" >&2
exit 127
