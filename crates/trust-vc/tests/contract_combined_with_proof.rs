// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Compile-fail coverage for requires-only `#[trust_vc::contract]` on empty
//! `#[trust_vc::proof]` functions.

#[path = "common/trybuild_env.rs"]
mod trybuild_env;

#[test]
fn contract_combined_with_proof_emits_clear_diagnostic() {
    trybuild_env::pin_no_trust_verify();
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/compile-fail/contract_combined_with_proof.rs");
}
