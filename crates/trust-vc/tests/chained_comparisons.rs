// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Proc-macro integration tests for chained comparison normalization.

mod common;

#[test]
fn test_proof_macros_accept_chained_comparisons() {
    let _ = common::verify_should_pass(|| {
        #[trust_vc::proof]
        fn chained_contracts(i: i32, n: i32, lo: i32, mid: i32, hi: i32) {
            trust_vc::requires!(0 <= i < n);
            trust_vc::requires!(hi >= mid > lo);

            trust_vc::assert!(0 <= i < n);
            trust_vc::assert!(hi >= mid > lo);

            trust_vc::ensures!(0 <= i < n);
            trust_vc::ensures!(hi >= mid > lo);
        }

        chained_contracts(3, 10, 1, 5, 10);
    });
}
