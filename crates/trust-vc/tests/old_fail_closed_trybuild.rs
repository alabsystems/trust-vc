// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Compile-fail coverage for `old!()` expressions that must fail closed in
//! `ensures!()` postconditions.

#[path = "common/trybuild_env.rs"]
mod trybuild_env;

#[test]
fn old_complex_expression_compile_fail_tests() {
    trybuild_env::pin_no_trust_verify();
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/compile-fail/old_*.rs");
}
