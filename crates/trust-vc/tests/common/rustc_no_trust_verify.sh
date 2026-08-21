#!/bin/sh
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# RUSTC_WRAPPER shim for trybuild scratch builds: appends `-Ztrust-verify=off`
# to EVERY rustc invocation, host and target units alike.
#
# Why rustflags are not enough: trybuild passes `--target <host-triple>` to its
# scratch cargo (trybuild 1.0.116 `src/cargo.rs` `fn target()`), and when
# `--target` is set cargo applies NO extra rustflags — not RUSTFLAGS, not
# CARGO_ENCODED_RUSTFLAGS, not `build.rustflags`, not `target.<t>.rustflags` —
# to HOST units (build scripts, proc macros, and their transitive deps).
# `trust_vc` is a proc-macro crate that depends on `trust-vc-core` (and thus
# the entire ay solver stack), so the whole solver graph compiles as HOST
# units in every trybuild scratch build. Without this shim the Trust
# toolchain's default fail-closed verification churns for many minutes to
# hours on those unflagged host deps (observed: `autocfg` alone >9 min at
# 100% CPU). A RUSTC_WRAPPER is the only stable cargo mechanism that reaches
# every compiler invocation on both sides; trybuild only `env_remove`s
# RUSTFLAGS, so the wrapper set in the test process is inherited.
#
# Invoked by cargo as: $RUSTC_WRAPPER <rustc> <args...>
exec "$@" -Ztrust-verify=off
