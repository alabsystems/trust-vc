// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Compile-fail regression for public verification API must_use contracts.

#[path = "../../trust-vc/tests/common/trybuild_env.rs"]
mod trybuild_env;

#[test]
fn must_use_api_contract() {
    trybuild_env::pin_no_trust_verify();
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/ui/must_use_api_contract.rs");
}
