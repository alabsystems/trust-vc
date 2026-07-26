// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Proc-macro collection coverage for loop extension macros (#2417).

#![allow(
    clippy::assign_op_pattern,
    clippy::never_loop,
    clippy::while_immutable_condition
)]

use trust_vc::{invariant_except_break, loop_ensures};
use trust_vc_core::vc::ObligationKind;

mod common;

#[test]
fn test_invariant_except_break_macro_collects_obligation() {
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_variable("i".to_string(), "i32".to_string());

        let mut i = 0;
        while i < 1 {
            invariant_except_break!(i >= 0);
            i += 1;
        }

        let context = trust_vc_core::verify_macro::get_context()
            .expect("invariant_except_break should collect");
        assert!(
            context.obligations().iter().any(|obligation| {
                obligation.kind() == ObligationKind::InvariantExceptBreak
                    && obligation.condition().contains("i >= 0")
            }),
            "expected InvariantExceptBreak obligation, got: {:?}",
            context.obligations()
        );
    });
}

#[test]
fn test_invariant_except_break_macro_collects_obligation_on_break_loop() {
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_variable("i".to_string(), "i32".to_string());

        let mut i = 9;
        loop {
            invariant_except_break!(i <= 9);
            i += 1;
            if i == 10 {
                break;
            }
        }

        let context = trust_vc_core::verify_macro::get_context()
            .expect("invariant_except_break should collect before break");
        assert!(
            context.obligations().iter().any(|obligation| {
                obligation.kind() == ObligationKind::InvariantExceptBreak
                    && obligation.condition().contains("i <= 9")
            }),
            "expected break-loop InvariantExceptBreak obligation, got: {:?}",
            context.obligations()
        );
    });
}

#[test]
fn test_loop_ensures_macro_collects_obligation() {
    common::with_clean_verification(|| {
        trust_vc_core::verify_macro::collect_variable("i".to_string(), "i32".to_string());

        let mut i = 0;
        while i < 1 {
            loop_ensures!(i <= 1);
            i += 1;
        }

        let context =
            trust_vc_core::verify_macro::get_context().expect("loop_ensures should collect");
        assert!(
            context.obligations().iter().any(|obligation| {
                obligation.kind() == ObligationKind::LoopEnsures
                    && obligation.condition().contains("i <= 1")
            }),
            "expected LoopEnsures obligation, got: {:?}",
            context.obligations()
        );
    });
}

#[test]
fn test_upstream_while_b_bool_guard_normal_exit_verifies() {
    let _ = common::verify_should_pass(|| {
        #[trust_vc::proof]
        fn while_b(b: bool) {
            while b {}

            trust_vc::assert!(!b);
        }

        while_b(false);
    });
}

#[test]
fn test_upstream_while_b2_inner_break_keeps_outer_normal_exit() {
    let _ = common::verify_should_pass(|| {
        #[trust_vc::proof]
        fn while_b2(b: bool) {
            while b {
                while b {
                    break;
                }
            }

            trust_vc::assert!(!b);
        }

        while_b2(false);
    });
}

#[test]
fn test_upstream_while_b2_y_labeled_inner_break_keeps_outer_normal_exit() {
    let _ = common::verify_should_pass(|| {
        #[trust_vc::proof]
        fn while_b2_y(b: bool) {
            while b {
                'y: while b {
                    break 'y;
                }
            }

            trust_vc::assert!(!b);
        }

        while_b2_y(false);
    });
}

#[test]
fn test_upstream_loop_break_regular_invariant_uses_loop_metadata() {
    let _ = common::verify_should_pass(|| {
        #[trust_vc::proof]
        fn loop_break_regular_invariant() {
            let mut i: u64 = 0u64;
            let limit: u64 = 10u64;

            loop {
                trust_vc::invariant!(limit == 10u64);

                i = i + 1u64;
                if i == 1u64 {
                    break;
                }
            }

            trust_vc::assert!(limit == 10u64);
        }

        loop_break_regular_invariant();
    });
}
