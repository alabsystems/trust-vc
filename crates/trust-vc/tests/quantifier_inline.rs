// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Proc-macro integration tests for Verus-style inline quantifier syntax.

mod common;

#[test]
fn inline_forall_int_in_assert_verifies() {
    let _ = common::verify_should_pass(|| {
        #[trust_vc::proof]
        fn inline_forall_int_reflexive() {
            trust_vc::assert!(forall|i: int| i == i);
        }

        inline_forall_int_reflexive();
    });
}

#[test]
fn inline_exists_nat_in_assert_verifies_with_witness() {
    let _ = common::verify_should_pass(|| {
        #[trust_vc::proof]
        fn inline_exists_nat_witness() {
            trust_vc::assert!(exists|i: nat| i == 0);
        }

        inline_exists_nat_witness();
    });
}

#[test]
fn inline_exists_nat_in_assert_rejects_negative_witness() {
    let _ = common::verify_should_fail(|| {
        #[trust_vc::proof]
        fn inline_exists_nat_negative() {
            trust_vc::assert!(exists|i: nat| i < 0);
        }

        inline_exists_nat_negative();
    });
}
