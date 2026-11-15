#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

# API snapshots are public-Rust surfaces generated from rustdoc JSON, which the
# Trust toolchain's trustdoc emits (`targo --unverified rustdoc ... -- -Z
# unstable-options --output-format json`; crates/trust-vc-merge-contract/src/
# api_surface.rs). The JSON is compiler-versioned: when trustdoc's
# `format_version` moves, bump `rustdoc-types` in Cargo.toml to match and
# refresh the baselines. Owner directive 2026-09-28: Trust only, no stock
# toolchain and no fallback — refuse unless `targo` is the Trust targo.
if ! targo --unverified --version >/dev/null 2>&1; then
    echo "error: API surface generation requires the Trust toolchain's targo on PATH" >&2
    echo "       (\`targo --unverified --version\` failed; upstream cargo rejects that flag)" >&2
    exit 2
fi
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$repo_root/target/api_surface_gate}"
unset RUSTFLAGS RUSTDOCFLAGS CARGO_ENCODED_RUSTFLAGS CARGO_ENCODED_RUSTDOCFLAGS
unset CARGO_BUILD_RUSTC CARGO_BUILD_RUSTC_WRAPPER RUSTC RUSTC_WRAPPER

case "${1:-}" in
    "")
        ;;
    --refresh)
        targo --unverified run --locked \
            -p trust-vc-merge-contract \
            --bin generate_api_surface_fixtures
        ;;
    *)
        echo "usage: $0 [--refresh]" >&2
        exit 2
        ;;
esac

targo --unverified test --locked \
    -p trust-vc-merge-contract \
    --lib \
    api_surface::tests::checked_in_snapshot_matches_fresh_generation \
    -- \
    --test-threads=1
