// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Integration tests for `trust_vc::arbitrary!()` — nondeterministic expressions.
//!
//! Tests that `arbitrary!(T)` produces unconstrained symbolic values in the
//! verification context, and that constraints can be added via `assume!`.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests in this file invoke ay verification through VerificationPipeline.
//!
//! Part of #2518.

mod common;

/// An unconstrained arbitrary value should NOT verify positive assertions.
/// `x` could be any i32 (including negative), so `x > 0` is unprovable.
#[test]
fn test_arbitrary_unconstrained_fails() {
    let result = common::verify_and_get_result(|| {
        #[trust_vc::proof]
        fn unconstrained_positive() {
            let x: i32 = trust_vc::arbitrary!(i32);
            trust_vc::assert!(x > 0);
        }
        unconstrained_positive();
    });

    assert!(
        matches!(
            result,
            trust_vc_core::VerifyResult::Counterexample { .. }
                | trust_vc_core::VerifyResult::Unknown { .. }
        ),
        "unconstrained arbitrary proof should not verify, got {result:?}"
    );
}

/// An arbitrary value with assume constraints should verify.
/// `assume!(x > 0 && x < 100)` constrains x, then `x > 0` is provable.
#[test]
fn test_arbitrary_constrained_passes() {
    let _ = common::verify_should_pass(|| {
        #[trust_vc::proof]
        fn constrained_positive() {
            let x: i32 = trust_vc::arbitrary!(i32);
            trust_vc::assume!(x > 0);
            trust_vc::assume!(x < 100);
            trust_vc::assert!(x + 1 > 0);
        }
        constrained_positive();
    });
}
