// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! End-to-end quantifier verification tests (Issue #1470, #1500)
//!
//! These tests verify that forall!/exists! macros, when used with the
//! VerificationPipeline, correctly collect obligations and send them through
//! the encoder to ay for SMT verification.
//!
//! **Current state:** quantifier outcomes are backend-dependent. Simple
//! trigger-less formulas often verify through the encoder's skolemized path,
//! but some valid formulas still return `Unknown` on public/staged solver
//! paths. That is not a soundness hole — `Unknown` remains the conservative
//! "I couldn't decide" answer. The actual soundness hole was the macros
//! returning `true` without any verification (#1221).
//!
//! **Test discrimination strategy (#1589):** tests that exercise soundness
//! boundaries reject unsound `Verified` outcomes exactly. Positive quantifier
//! cases assert either `Verified` or `Unknown` when solver completeness varies
//! across backends, while still rejecting `Counterexample`/`Error`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::verify_macro;
use trust_vc_core::VerifyResult;

// ========================================================================
// Pipeline tests: verify that quantifiers go through the full pipeline
// ========================================================================

#[test]
fn test_forall_reflexivity_through_pipeline() {
    common::with_clean_verification(|| {
        // forall x: i32. x == x — tautology
        let _ = trust_vc::forall!(|x: i32| x == x);

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // ay-dpll now verifies simple quantified tautologies (#1589 resolved).
        // The empty-model guard correctly identifies x == x as a ground-formula
        // tautology. Update per #1589: "tighten to assert Verified."
        assert!(
            matches!(result, VerifyResult::Verified),
            "forall(|x| x == x) should verify — ay-dpll now handles tautologies, got: {:?}",
            result
        );
    })
}

#[test]
fn test_exists_witness_through_pipeline() {
    common::with_clean_verification(|| {
        // exists x: i32. x == 0 — trivially satisfiable
        let _ = trust_vc::exists!(|x: i32| x == 0);

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // ay-dpll now handles witness instantiation for existentials (#1589).
        assert!(
            matches!(result, VerifyResult::Verified),
            "exists(|x| x == 0) should verify — ay-dpll handles existentials, got: {:?}",
            result
        );
    })
}

#[test]
fn test_forall_commutativity_through_pipeline() {
    common::with_clean_verification(|| {
        // forall x, y: i32. x + y == y + x — addition commutativity
        let _ = trust_vc::forall!(|x: i32, y: i32| x + y == y + x);

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Encoder-level Skolemization (#2187): trigger-less forall produces a
        // ground formula. Some backends prove commutativity directly; others
        // conservatively return Unknown. Both are acceptable here as long as we
        // do not regress to Counterexample/Error.
        assert!(
            matches!(result, VerifyResult::Verified | VerifyResult::Unknown { .. }),
            "forall commutativity should be Verified or Unknown under staged/public backends, got: {:?}",
            result
        );
    })
}

// ========================================================================
// Negative tests: contradictions must NOT be Verified
// ========================================================================

#[test]
fn test_forall_contradiction_not_verified_through_pipeline() {
    common::with_clean_verification(|| {
        // forall x: i32. x != x — contradiction
        let _ = trust_vc::forall!(|x: i32| x != x);

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Must NOT be Verified — this is the key soundness property.
        // Counterexample or Unknown are both acceptable safe answers.
        assert!(
            !matches!(result, VerifyResult::Verified),
            "forall(|x| x != x) must NOT verify (contradiction), got: {:?}",
            result
        );
    })
}

#[test]
fn test_forall_not_all_positive_not_verified_through_pipeline() {
    common::with_clean_verification(|| {
        // forall x: i32. x > 0 — false (x = 0 is a counterexample)
        let _ = trust_vc::forall!(|x: i32| x > 0);

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            !matches!(result, VerifyResult::Verified),
            "forall(|x| x > 0) must NOT verify (false for x=0), got: {:?}",
            result
        );
    })
}

#[test]
fn test_exists_contradiction_not_verified_through_pipeline() {
    common::with_clean_verification(|| {
        // exists x: i32. x != x — impossible
        let _ = trust_vc::exists!(|x: i32| x != x);

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            !matches!(result, VerifyResult::Verified),
            "exists(|x| x != x) must NOT verify (impossible), got: {:?}",
            result
        );
    })
}

// ========================================================================
// Implication test
// ========================================================================

#[test]
fn test_forall_implication_through_pipeline() {
    common::with_clean_verification(|| {
        // x > 5 implies x > 0 (encoded as !(x > 5) || x > 0)
        #[allow(clippy::nonminimal_bool)]
        let _ = trust_vc::forall!(|x: i32| !(x > 5) || x > 0);

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Encoder-level Skolemization (#2187): trigger-less forall produces a
        // ground formula. x > 5 => x > 0 is valid, so this verifies directly.
        assert!(
            matches!(result, VerifyResult::Verified),
            "forall implication should verify with Skolemization, got: {:?}",
            result
        );
    })
}

// ========================================================================
// Obligation collection tests: verify macros produce correct conditions
// ========================================================================

#[test]
fn test_forall_macro_collects_obligation() {
    common::with_clean_verification(|| {
        let _ = trust_vc::forall!(|x: i32| x == x);

        let ctx = verify_macro::get_context();
        assert!(ctx.is_some(), "Should have a verification context");
        let ctx = ctx.unwrap();
        assert!(
            !ctx.obligations().is_empty(),
            "Should have collected at least one obligation"
        );

        let condition = &ctx.obligations()[0].condition();
        assert!(
            condition.starts_with("forall("),
            "Obligation condition should start with 'forall(', got: {}",
            condition
        );
    })
}

#[test]
fn test_exists_macro_collects_obligation() {
    common::with_clean_verification(|| {
        let _ = trust_vc::exists!(|x: i32| x > 0);

        let ctx = verify_macro::get_context();
        assert!(ctx.is_some(), "Should have a verification context");
        let ctx = ctx.unwrap();
        assert!(
            !ctx.obligations().is_empty(),
            "Should have collected at least one obligation"
        );

        let condition = &ctx.obligations()[0].condition();
        assert!(
            condition.starts_with("exists("),
            "Obligation condition should start with 'exists(', got: {}",
            condition
        );
    })
}

// ========================================================================
// Encoder error tests: quantifier strings must not cause parse errors
// ========================================================================

#[test]
fn test_forall_no_encoder_error_through_pipeline() {
    common::with_clean_verification(|| {
        let _ = trust_vc::forall!(|x: i32| x > 0 && x < 100);

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // Encoder-level Skolemization (#2187): trigger-less forall produces a
        // ground formula. forall x. x > 0 && x < 100 is INVALID (x=0 violates),
        // so ay correctly finds Counterexample.
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "forall(|x| x > 0 && x < 100) should be Counterexample (invalid universal), got: {:?}",
            result
        );
    })
}

#[test]
fn test_exists_multi_var_no_encoder_error() {
    common::with_clean_verification(|| {
        let _ = trust_vc::exists!(|x: i32, y: i32| x + y == 0);

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // The encoder must parse multi-var exists without error. Backend
        // completeness varies here: some solvers prove the witness exists,
        // others conservatively return Unknown. Both are acceptable as long as
        // we do not regress to Counterexample/Error.
        assert!(
            matches!(result, VerifyResult::Verified | VerifyResult::Unknown { .. }),
            "exists(|x, y| x + y == 0) should be Verified or Unknown without encoder failure, got: {:?}",
            result
        );
    })
}

// ========================================================================
// u64 upper bound soundness tests (Regression: #1660)
//
// Before the fix, unsigned_upper_bound() returned i64::MAX for u64/u128/usize,
// restricting the quantifier domain to [0, i64::MAX) instead of [0, 2^64).
// For forall, this was unsound: proving P for [0, i64::MAX) does not prove P
// for [0, 2^64). These tests verify the fix uses correct BigInt bounds.
// ========================================================================

#[test]
fn test_forall_u64_less_than_i64_max_not_verified() {
    // forall |x: u64| x < i64::MAX is FALSE: x = i64::MAX is a valid u64
    // counterexample. Before #1660 fix, the domain was [0, i64::MAX) so this
    // would falsely verify. With correct [0, 2^64) domain, this must NOT verify.
    common::with_clean_verification(|| {
        let _ = trust_vc::forall!(|x: u64| x < 9223372036854775807u64);

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            !matches!(result, VerifyResult::Verified),
            "forall(|x: u64| x < i64::MAX) must NOT verify — x = i64::MAX is a counterexample, got: {:?}",
            result
        );
    })
}

#[test]
fn test_forall_u64_contradiction_not_verified() {
    // forall |x: u64| x != x is a contradiction — no u64 satisfies it.
    // Must NOT verify. Tests that u64 quantifiers correctly reject contradictions.
    common::with_clean_verification(|| {
        let _ = trust_vc::forall!(|x: u64| x != x);

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        assert!(
            !matches!(result, VerifyResult::Verified),
            "forall(|x: u64| x != x) must NOT verify (contradiction), got: {:?}",
            result
        );
    })
}

#[test]
fn test_forall_u64_reflexivity_does_not_error() {
    // forall |x: u64| x == x — tautology with u64 type.
    // Fixed: register_quantifier_bound_var now propagates u64 → Uint{64}
    // to lookup_var_type, so the body's variable reference gets the correct type.
    common::with_clean_verification(|| {
        let _ = trust_vc::forall!(|x: u64| x == x);

        let pipeline = VerificationPipeline::collect_from_macros();
        let result = pipeline.verify();

        // With the type fix, this tautology should verify (not error).
        assert!(
            matches!(result, VerifyResult::Verified),
            "forall(|x: u64| x == x) should verify after type fix, got: {:?}",
            result
        );
    })
}
