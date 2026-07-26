// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Compile-fail tests for trust_vc proc macros.
//!
//! Uses trybuild to verify that invalid macro usage produces
//! helpful compile errors.

const GENERAL_COMPILE_FAIL_GLOBS: &[&str] = &[
    "tests/compile-fail/all_*.rs",
    "tests/compile-fail/ambiguous_*.rs",
    "tests/compile-fail/auto_*.rs",
    "tests/compile-fail/broadcast_unexpected_args.rs",
    "tests/compile-fail/decreases_*.rs",
    "tests/compile-fail/exec_*.rs",
    "tests/compile-fail/external_*.rs",
    "tests/compile-fail/liveness_*.rs",
    "tests/compile-fail/memoize_*.rs",
    "tests/compile-fail/proof_calls_*.rs",
    "tests/compile-fail/proof_recursive_without_decreases.rs",
    "tests/compile-fail/proof_unexpected_args.rs",
    "tests/compile-fail/returns_*.rs",
    "tests/compile-fail/spec_*.rs",
    "tests/compile-fail/trigger_*.rs",
    "tests/compile-fail/via_fn_*.rs",
];

#[path = "common/trybuild_env.rs"]
mod trybuild_env;

#[test]
fn compile_fail_tests() {
    trybuild_env::pin_no_trust_verify();
    let t = trybuild::TestCases::new();
    for pattern in GENERAL_COMPILE_FAIL_GLOBS {
        t.compile_fail(pattern);
    }
}
