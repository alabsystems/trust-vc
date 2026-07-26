// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Compile-fail coverage for unsupported `#[trust_vc::proof]` and
//! `#[trust_vc::broadcast]` parameter patterns from #1753.

#[path = "common/trybuild_env.rs"]
mod trybuild_env;

#[test]
fn unsupported_param_patterns_fail_closed() {
    trybuild_env::pin_no_trust_verify();
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/compile-fail/*_param_fail_closed.rs");
}
