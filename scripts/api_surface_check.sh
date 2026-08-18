#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

# API snapshots are public-Rust surfaces, but their rustdoc JSON input is
# compiler-versioned.  Generate them with one pinned stock toolchain: the
# workspace's default `trust` toolchain enables verification, while
# rustdoc-json recursively invokes bare Cargo and cannot inherit Targo's
# process-local explicit-unverified authority on every host.
rustup_bin_dir="${CARGO_HOME:-$HOME/.cargo}/bin"
if [[ ! -x "$rustup_bin_dir/rustup" || ! -x "$rustup_bin_dir/cargo" ]]; then
    echo "error: API surface generation requires rustup and its Cargo proxy in $rustup_bin_dir" >&2
    exit 2
fi
export PATH="$rustup_bin_dir:$PATH"
export RUSTUP_TOOLCHAIN=1.97.1
export RUSTFLAGS=
export RUSTDOCFLAGS=
export CARGO_TARGET_DIR="$repo_root/target/api_surface_gate"
unset CARGO_ENCODED_RUSTFLAGS CARGO_ENCODED_RUSTDOCFLAGS
unset CARGO_BUILD_RUSTC CARGO_BUILD_RUSTC_WRAPPER RUSTC RUSTC_WRAPPER

case "${1:-}" in
    "")
        ;;
    --refresh)
        cargo run --locked \
            -p trust-vc-merge-contract \
            --bin generate_api_surface_fixtures
        ;;
    *)
        echo "usage: $0 [--refresh]" >&2
        exit 2
        ;;
esac

cargo test --locked \
    -p trust-vc-merge-contract \
    --lib \
    api_surface::tests::checked_in_snapshot_matches_fresh_generation \
    -- \
    --test-threads=1
