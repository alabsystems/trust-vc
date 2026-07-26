// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `assert_by_contradiction!` proof blocks.

use trust_vc::assert_by_contradiction;
use trust_vc_core::vc::ObligationKind;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

mod common;

#[test]
fn test_assert_by_contradiction_injects_negated_assumption() {
    common::with_clean_verification(|| {
        assert_by_contradiction!(5 > 0, {});

        let pipeline = VerificationPipeline::collect_from_macros();
        let scopes = pipeline.context().assert_by_scopes();
        assert_eq!(scopes.len(), 1, "expected one contradiction proof scope");

        let scoped = scopes
            .values()
            .next()
            .expect("assert_by_contradiction should create a scoped proof");
        assert_eq!(scoped.len(), 1, "empty proof block should only inject !P");
        assert_eq!(scoped[0].kind(), ObligationKind::Assume);
        assert!(
            scoped[0].condition().contains("5 > 0"),
            "negated assumption should mention the original condition, got {:?}",
            scoped[0]
        );

        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "true condition should verify by contradiction, got {:?}",
            result
        );
    })
}

#[test]
fn test_assert_by_contradiction_preserves_user_proof_block() {
    common::with_clean_verification(|| {
        assert_by_contradiction!(5 > 0, {
            trust_vc::assume!(true);
        });

        let pipeline = VerificationPipeline::collect_from_macros();
        let scoped = pipeline
            .context()
            .assert_by_scopes()
            .values()
            .next()
            .expect("expected contradiction proof scope");
        assert_eq!(
            scoped.len(),
            2,
            "wrapper should keep the injected !P assumption and the user proof step"
        );

        let result = pipeline.verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "proof block should remain active inside contradiction scope, got {:?}",
            result
        );
    })
}

#[test]
fn test_assert_by_contradiction_false_goal_without_contradiction_fails() {
    common::with_clean_verification(|| {
        assert_by_contradiction!(5 == 10, {});

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "false goal without a derived contradiction must fail, got {:?}",
            result
        );
    })
}

#[test]
fn test_assert_by_contradiction_assumption_stays_scoped() {
    common::with_clean_verification(|| {
        assert_by_contradiction!(5 > 0, {});
        trust_vc::assert!(5 == 10);

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "the contradiction helper must not leak !P into outer obligations, got {:?}",
            result
        );
    })
}
