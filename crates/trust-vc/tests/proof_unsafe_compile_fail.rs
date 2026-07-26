// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

#[path = "common/trybuild_env.rs"]
mod trybuild_env;

#[test]
fn proof_unsafe_compile_fail_tests() {
    trybuild_env::pin_no_trust_verify();
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/compile-fail/proof_unsafe_fn.rs");
}
