// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for calc! macro — calculational proof blocks.
//!
//! VERIFICATION LEVEL: VERIFY
//! Tests in this file invoke ay verification through VerificationPipeline.
//!
//! Part of #2413.

use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

mod common;

const SEQ_ONE_U8: &str = "trust_vc_types::Seq::<u8>::empty().push(1u8)";
const SEQ_TWO_U8: &str = "trust_vc_types::Seq::<u8>::empty().push(2u8)";

/// Single-step equality: calc! { 2 + 3; == {} 5; }
#[test]
fn test_calc_single_step_equality() {
    common::with_clean_verification(|| {
        trust_vc::calc! {
            2 + 3;
            == {}
            5;
        };

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "calc! single step 2+3 == 5 should verify: {:?}",
            result
        );
    })
}

/// Two-step equality chain with transitive conclusion.
#[test]
fn test_calc_two_step_equality_chain() {
    common::with_clean_verification(|| {
        trust_vc::calc! {
            1 + 2;
            == {}
            3;
            == {}
            4 - 1;
        };

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "calc! chain 1+2 == 3 == 4-1 should verify: {:?}",
            result
        );
    })
}

/// Upstream-style Seq equality chain using `+` concatenation and assert_seqs_equal! proofs.
#[test]
fn test_calc_seq_concat_assert_seqs_equal_chain() {
    common::with_clean_verification(|| {
        verify_macro::collect_variable("a".to_string(), "Seq<u8>".to_string());
        verify_macro::collect_let_binding(
            "a".to_string(),
            "trust_vc_types::Seq::<u8>::empty().push(1u8).push(2u8)".to_string(),
        );
        verify_macro::collect_variable("b".to_string(), "Seq<u8>".to_string());
        verify_macro::collect_let_binding(
            "b".to_string(),
            "trust_vc_types::Seq::<u8>::empty().push(1u8)".to_string(),
        );
        verify_macro::collect_variable("c".to_string(), "Seq<u8>".to_string());
        verify_macro::collect_let_binding(
            "c".to_string(),
            "trust_vc_types::Seq::<u8>::empty().push(2u8)".to_string(),
        );
        verify_macro::collect_variable("d".to_string(), "Seq<u8>".to_string());
        verify_macro::collect_let_binding(
            "d".to_string(),
            "trust_vc_types::Seq::<u8>::empty().push(1u8).push(2u8)".to_string(),
        );

        let a: trust_vc_types::Seq<u8> = trust_vc_types::seq![1u8, 2u8];
        let b: trust_vc_types::Seq<u8> = trust_vc_types::seq![1u8];
        let c: trust_vc_types::Seq<u8> = trust_vc_types::seq![2u8];
        let d: trust_vc_types::Seq<u8> = trust_vc_types::seq![1u8, 2u8];
        let _ = (&a, &b, &c, &d);

        trust_vc::calc! {
            (==)
            a;
            { trust_vc::assert_seqs_equal!(a == b + c); }
            b + c;
            { trust_vc::assert_seqs_equal!(b + c == d); }
            d;
        };

        trust_vc::assert!(a == d);

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "calc! Seq concat chain should verify deterministically: {:?}",
            result
        );
    })
}

#[test]
fn test_calc_local_let_binding_does_not_leak_into_later_seq_assert() {
    common::with_clean_verification(|| {
        verify_macro::collect_variable("a".to_string(), "Seq<u8>".to_string());
        verify_macro::collect_ext_eq_obligation(
            ObligationKind::Assume,
            "outer_a_is_seq_one".to_string(),
            "a".to_string(),
            SEQ_ONE_U8.to_string(),
            true,
            None,
        );

        let a: trust_vc_types::Seq<u8> = trust_vc_types::seq![1u8];
        let _ = &a;

        trust_vc::calc! {
            (==)
            a;
            {
                verify_macro::collect_variable("a".to_string(), "Seq<u8>".to_string());
                verify_macro::collect_let_binding("a".to_string(), SEQ_TWO_U8.to_string());
                let a: trust_vc_types::Seq<u8> = trust_vc_types::seq![2u8];
                let _ = &a;
                trust_vc::assert_seqs_equal!(a == trust_vc_types::Seq::<u8>::empty().push(2u8));
            }
            a;
        };

        trust_vc::assert_seqs_equal!(a == trust_vc_types::Seq::<u8>::empty().push(1u8));

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "calc proof-block local let should not leak into later Seq equality: {:?}",
            result
        );
    })
}

#[test]
fn test_calc_shadowed_local_let_restores_outer_binding_for_later_seq_assert() {
    common::with_clean_verification(|| {
        verify_macro::collect_variable("s".to_string(), "Seq<u8>".to_string());
        verify_macro::collect_let_binding("s".to_string(), SEQ_ONE_U8.to_string());

        let s: trust_vc_types::Seq<u8> = trust_vc_types::seq![1u8];
        let _ = &s;

        trust_vc::calc! {
            (==)
            s;
            {
                verify_macro::collect_variable("s".to_string(), "Seq<u8>".to_string());
                verify_macro::collect_let_binding("s".to_string(), SEQ_TWO_U8.to_string());
                let s: trust_vc_types::Seq<u8> = trust_vc_types::seq![2u8];
                let _ = &s;
                trust_vc::assert_seqs_equal!(s == trust_vc_types::Seq::<u8>::empty().push(2u8));
            }
            s;
        };

        trust_vc::assert_seqs_equal!(s == trust_vc_types::Seq::<u8>::empty().push(1u8));

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "calc proof-block shadowed let should restore outer binding for later Seq equality: {:?}",
            result
        );
    })
}

/// Inequality chain with literals: 1 <= 2 <= 3.
#[test]
fn test_calc_inequality_transitivity() {
    common::with_clean_verification(|| {
        trust_vc::calc! {
            1;
            <= {}
            2;
            <= {}
            3;
        };

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "calc! chain 1 <= 2 <= 3 should verify: {:?}",
            result
        );
    })
}

/// Mixed == and <= chain: overall operator is <=.
#[test]
fn test_calc_mixed_eq_le() {
    common::with_clean_verification(|| {
        trust_vc::calc! {
            5;
            == {}
            5;
            <= {}
            10;
        };

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "calc! mixed == and <= should verify: {:?}",
            result
        );
    })
}

/// Implication chain: x>=10 ==> x>=5 ==> x>=0, overall x>=10 ==> x>=0.
#[test]
fn test_calc_implies_chain_verifies() {
    common::with_clean_verification(|| {
        verify_macro::collect_variable("x".to_string(), "u64".to_string());
        let x: u64 = 10;
        let _ = x;
        trust_vc::calc! {
            x >= 10u64;
            ==> {}
            x >= 5u64;
            ==> {}
            x >= 0u64;
        };

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "calc! implies chain x>=10 ==> x>=5 ==> x>=0 should verify: {:?}",
            result
        );
    })
}

/// A FALSE implication step must NOT verify (cardinal): x>=3 ==> x>=5 is false.
#[test]
fn test_calc_implies_false_step_not_verified() {
    common::with_clean_verification(|| {
        verify_macro::collect_variable("x".to_string(), "u64".to_string());
        let x: u64 = 3;
        let _ = x;
        trust_vc::calc! {
            x >= 3u64;
            ==> {}
            x >= 5u64;
        };

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            !matches!(result, VerifyResult::Verified),
            "CARDINAL: calc! with false implication x>=3 ==> x>=5 must NOT verify: {:?}",
            result
        );
    })
}

/// Biconditional step: x==5 <==> 5==x (equality symmetry).
#[test]
fn test_calc_iff_step_verifies() {
    common::with_clean_verification(|| {
        verify_macro::collect_variable("x".to_string(), "u64".to_string());
        let x: u64 = 5;
        let _ = x;
        trust_vc::calc! {
            x == 5u64;
            <==> {}
            5u64 == x;
        };

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "calc! iff x==5 <==> 5==x should verify: {:?}",
            result
        );
    })
}

/// Wrong step should fail verification.
#[test]
fn test_calc_wrong_step_fails() {
    common::with_clean_verification(|| {
        trust_vc::calc! {
            10;
            == {}
            5;
        };

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "calc! with wrong step 10 == 5 should be counterexample: {:?}",
            result
        );
    })
}
