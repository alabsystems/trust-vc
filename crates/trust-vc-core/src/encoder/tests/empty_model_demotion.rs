//! Tests for the SAT + empty-model demotion guard on quantified assertions.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::encoder::verification::test_hooks::FORCE_EMPTY_MODEL;

/// DISCRIMINATING: a forced empty model on a non-skolemized quantifier
/// demotes SAT to Unknown(EmptyModel) instead of reporting a counterexample.
#[test]
fn test_empty_model_demotes_non_skolemized_exists_to_unknown() {
    let mut ctx = VerificationContext::new();
    // False existential: verification reaches the SAT/counterexample branch
    // where the empty-model guard can demote the solver result to Unknown.
    ctx.push_obligation(ProofObligation::assert(
        "exists_false",
        "exists(|x: i32| x != x)",
    ));

    let baseline = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &baseline,
        "false existential must not verify before forcing empty-model demotion",
    );

    let result = {
        let _flag = ForcedFlagGuard::new(&FORCE_EMPTY_MODEL);
        AYEncoder::verify(&ctx)
    };

    assert_eq!(
        result.unknown_category(),
        Some(UnknownCategory::EmptyModel),
        "forced empty model should classify as EmptyModel, got: {:?}",
        result
    );

    match result {
        VerifyResult::Unknown { reason, .. } => {
            assert!(
                reason.contains("empty model"),
                "forced empty-model demotion should mention empty model, got: {reason}"
            );
            assert!(
                reason.contains("exists_false"),
                "forced empty-model demotion should name the assertion, got: {reason}"
            );
        }
        other => panic!(
            "forced empty model should demote non-skolemized exists to Unknown, got: {:?}",
            other
        ),
    }
}

/// DISCRIMINATING: the empty-model guard must stay off for trigger-less forall
/// assertions, which `has_non_skolemized_quantifier()` treats as skolemized.
#[test]
fn test_empty_model_guard_skips_skolemized_forall() {
    let mut ctx = VerificationContext::new();
    // False trigger-less forall: still reaches the SAT/counterexample branch,
    // but `has_non_skolemized_quantifier()` keeps the empty-model guard off.
    ctx.push_obligation(ProofObligation::assert(
        "forall_false",
        "forall(|x: i32| x != x)",
    ));

    let baseline = AYEncoder::verify(&ctx);
    expect_counterexample(
        &baseline,
        "false trigger-less forall should take the normal counterexample path before forcing empty-model hook",
    );

    let result = {
        let _flag = ForcedFlagGuard::new(&FORCE_EMPTY_MODEL);
        AYEncoder::verify(&ctx)
    };

    assert_ne!(
        result.unknown_category(),
        Some(UnknownCategory::EmptyModel),
        "forced empty-model hook must not affect skolemized forall, got: {:?}",
        result
    );
    expect_counterexample(
        &result,
        "false universal should remain on the counterexample path under forced empty-model hook",
    );
}

/// DISCRIMINATING: statically impossible finite-domain existential assertions
/// are concrete counterexamples, not CEGQI empty-model Unknowns.
#[test]
fn test_empty_model_guard_skips_statically_refuted_finite_exists() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "exists_above_u8_max",
        "exists(|x: u8| x > 255)",
    ));

    let result = {
        let _flag = ForcedFlagGuard::new(&FORCE_EMPTY_MODEL);
        AYEncoder::verify(&ctx)
    };

    assert_ne!(
        result.unknown_category(),
        Some(UnknownCategory::EmptyModel),
        "statically refuted finite exists must bypass empty-model demotion, got: {:?}",
        result
    );
    expect_counterexample(
        &result,
        "exists(|x: u8| x > 255) should remain a counterexample under forced empty-model hook",
    );
}

#[test]
fn test_forced_empty_model_guard_resets_after_panic() {
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _flag = ForcedFlagGuard::new(&FORCE_EMPTY_MODEL);
        panic!("simulated test panic");
    }));
    assert!(result.is_err(), "guard regression test should panic");
    FORCE_EMPTY_MODEL.with(|flag| {
        assert!(
            !flag.get(),
            "forced empty-model flag must reset during unwind"
        )
    });
}
