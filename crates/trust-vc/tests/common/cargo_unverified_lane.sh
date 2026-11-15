#!/bin/sh
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# `CARGO` shim for trybuild scratch builds: names the UNVERIFIED lane on the
# nested Targo compile commands trybuild spawns, and passes every other
# subcommand through untouched.
#
# Why it exists: rust-toolchain.toml pins `channel = "trust"`, so `$CARGO` in a
# test process is Targo, and Targo has exactly two lanes and refuses a
# lane-less compile:
#
#     error: `targo check` refuses to create an implicitly unverified artifact.
#
# trybuild (1.0.120, `src/cargo.rs`) spawns `$CARGO` directly — `check`/`build`
# for the scratch project, plus `clean`, `run`, `generate-lockfile` and
# `metadata` — with no way to inject a flag, so every trybuild harness in this
# repo failed on that refusal under the sealed toolchain (measured 2026-09-11:
# four harnesses, the refusal text arriving in place of the expected-stderr
# fixture). Targo's own nested-lane broker (TRUST_TARGO_NESTED_UNVERIFIED_BROKER)
# does not cross the process boundary on this platform — targo says so itself:
# "nested explicit-unverified Targo propagation is unavailable on this platform
# ... recursive `$CARGO` invocations must select their own lane". This shim is
# that selection, made explicit: the scratch builds are compile-diagnostic
# fixtures and carry NO proof claim, which is exactly what `--unverified` says.
# `--unverified` is only valid on a compilation command, so the flag is added
# for those and for nothing else.
#
# Invoked by trybuild as: $CARGO <subcommand> <args...>
set -eu

if [ -z "${TRUST_VC_NESTED_CARGO:-}" ]; then
    echo "cargo_unverified_lane.sh: TRUST_VC_NESTED_CARGO is unset" >&2
    exit 127
fi

# The subcommand is NOT always the first argument: trybuild passes the global
# options first (`--offline --config=build.rustflags=[..] --config=target...`)
# and the subcommand after them, so the lane decision has to scan past the
# leading options — and past the ones that take a SEPARATE value, or their
# value would be read as the subcommand.
subcommand=""
skip_value=0
for arg in "$@"; do
    if [ "$skip_value" -eq 1 ]; then
        skip_value=0
        continue
    fi
    case "$arg" in
        --color|--config|--explain|-C|-Z)
            skip_value=1
            ;;
        -*)
            ;;
        *)
            subcommand="$arg"
            break
            ;;
    esac
done

case "$subcommand" in
    build|b|check|c|test|t|bench|run|r|rustc|doc|d)
        exec "$TRUST_VC_NESTED_CARGO" --unverified "$@"
        ;;
    *)
        exec "$TRUST_VC_NESTED_CARGO" "$@"
        ;;
esac
