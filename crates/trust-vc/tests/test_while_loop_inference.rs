// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! End-to-end coverage for basic `while` loop invariant normal-exit facts.

#![allow(
    clippy::assign_op_pattern,
    clippy::never_loop,
    clippy::while_immutable_condition
)]

mod common;

#[test]
fn test_while_loop_without_invariant_establishes_final_assertion() {
    let _ = common::verify_should_pass(|| {
        #[trust_vc::proof]
        fn while_loop_without_invariant_establishes_final_assertion() {
            let mut i: u64 = trust_vc::arbitrary!(u64);
            let limit: u64 = 10u64;

            while i < limit {
                i = i + 1u64;
            }

            trust_vc::assert!(i >= 10u64);
        }

        while_loop_without_invariant_establishes_final_assertion();
    });
}

#[test]
fn test_while_loop_invariant_establishes_final_assertion() {
    let _ = common::verify_should_pass(|| {
        #[trust_vc::proof]
        fn while_loop_invariant_establishes_final_assertion() {
            let mut i: u64 = trust_vc::arbitrary!(u64);
            let limit: u64 = 10u64;

            while i < limit {
                trust_vc::invariant!(limit == 10u64);
                i = i + 1u64;
            }

            trust_vc::assert!(i >= 10u64);
        }

        while_loop_invariant_establishes_final_assertion();
    });
}

#[test]
fn test_while_loop_with_break_does_not_assume_normal_exit() {
    let _ = common::verify_should_fail(|| {
        #[trust_vc::proof]
        fn while_loop_with_break_does_not_assume_normal_exit() {
            let mut i: u64 = 0u64;

            while i < 10u64 {
                break;
            }

            trust_vc::assert!(i >= 10u64);
        }

        while_loop_with_break_does_not_assume_normal_exit();
    });
}

#[test]
fn test_while_loop_with_impure_guard_does_not_assume_normal_exit() {
    let _ = common::verify_should_fail(|| {
        #[trust_vc::proof]
        fn while_loop_with_impure_guard_does_not_assume_normal_exit() {
            let mut i: u64 = 0u64;

            while {
                i = i + 1u64;
                i < 10u64
            } {}

            trust_vc::assert!(i >= 10u64);
        }

        while_loop_with_impure_guard_does_not_assume_normal_exit();
    });
}
