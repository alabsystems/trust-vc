#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Build one false-Verified fuzz target on the Trust toolchain and run it under
# libFuzzer. This is the Trust spelling of `cargo fuzz run <target> -- <args>`.
#
# Why not `targo fuzz run`: cargo-fuzz 0.13.2 spawns a bare `cargo` from PATH
# (src/project.rs, `Command::new("cargo")`), not `$CARGO`. Under targo the fuzz
# build would therefore run on whatever stock `cargo` PATH resolves, not on a
# Targo lane. So this script does cargo-fuzz's build step itself on the
# explicit UNVERIFIED lane (fuzz binaries are test harnesses and carry no proof
# claim), with the same instrumentation flags `cargo fuzz build -s none` uses.
# No sanitizer: the Trust aarch64-apple-darwin sysroot ships no ASan runtime.
#
# Usage: fuzz/run.sh <target> [libFuzzer args...]
#   TARGO / TRUSTC name the Trust frontend and compiler (default: from PATH).
#   fuzz/run.sh ensures_false -max_total_time=60
set -euo pipefail

if [ $# -lt 1 ]; then
    echo "usage: fuzz/run.sh <target> [libFuzzer args...]" >&2
    exit 2
fi
target=$1
shift

here=$(cd "$(dirname "$0")" && pwd -P)
: "${TARGO:=targo}"
# The host triple comes from the Trust compiler itself; no guessed default.
triple=$("${TRUSTC:-trustc}" -vV 2>/dev/null | sed -n 's/^host: //p') || triple=
if [ -z "$triple" ]; then
    echo "fuzz/run.sh: \`${TRUSTC:-trustc} -vV\` named no host triple (set TRUSTC to the Trust compiler)" >&2
    exit 2
fi

# --target keeps these flags off build scripts and proc macros, as cargo-fuzz does.
RUSTFLAGS="${RUSTFLAGS:-} -Cpasses=sancov-module \
-Cllvm-args=-sanitizer-coverage-level=4 \
-Cllvm-args=-sanitizer-coverage-inline-8bit-counters \
-Cllvm-args=-sanitizer-coverage-pc-table \
-Cllvm-args=-sanitizer-coverage-trace-compares \
--cfg fuzzing -Cdebug-assertions -Coverflow-checks" \
    "$TARGO" --unverified build --manifest-path "$here/Cargo.toml" \
    --release --target "$triple" --bin "$target"

# Same corpus and crash-artifact layout cargo-fuzz uses (both gitignored).
corpus="$here/corpus/$target"
artifacts="$here/artifacts/$target"
mkdir -p "$corpus" "$artifacts"
exec "$here/target/$triple/release/$target" -artifact_prefix="$artifacts/" "$corpus" "$@"
