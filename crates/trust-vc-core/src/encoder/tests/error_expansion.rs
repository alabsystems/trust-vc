//! Error expansion tests — assertion splitting for localized diagnostics.
//!
//! Tests that compound assertions which fail produce per-sub-assertion
//! pass/fail status in the counterexample model, via the splitting logic
//! in `verification/split.rs`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Part of #2485.

use super::*;
use crate::encoder::verification::split::split_assertion;
use crate::ir::TrustVcType;
use crate::ir_expr::{LogicOp, QuantifierKind, TrustVcExpr};

/// Failing conjunction identifies which conjunct fails.
///
/// x == 5 assumed, assert x > 0 && x > 10 && x < 20.
/// Conjunct 1 (x > 0) passes, conjunct 2 (x > 10) fails, conjunct 3 (x < 20) passes.
/// The localized model should contain [PASS] and [FAIL] markers.
#[test]
fn test_conjunction_split_identifies_failing_conjunct() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assert(
        "compound",
        "x > 0 && x > 10 && x < 20",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "x == 5 violates x > 10 conjunct");

    if let VerifyResult::Counterexample { model, .. } = &result {
        let model_str = model.as_ref().expect("split should produce model");
        assert!(
            model_str.contains("[FAIL]"),
            "model should contain [FAIL] marker, got: {model_str}"
        );
        assert!(
            model_str.contains("[PASS]"),
            "model should contain [PASS] marker (passing conjuncts), got: {model_str}"
        );
    }
}

/// Deep conjunction (4 conjuncts) — first and last pass, middle two fail.
///
/// x == 5, y == 15; assert x > 0 && y < 10 && x > 10 && y > 0.
/// Conjuncts 1 and 4 pass, conjuncts 2 and 3 fail.
/// The structured model should show 2x [FAIL] and 2x [PASS].
#[test]
fn test_conjunction_split_four_conjuncts_mixed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 15"));
    // x > 0 passes, y < 10 fails, x > 10 fails, y > 0 passes
    ctx.push_obligation(ProofObligation::assert(
        "four_parts",
        "x > 0 && y < 10 && x > 10 && y > 0",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "y == 15 > 10 violates y < 10");

    if let VerifyResult::Counterexample { model, .. } = &result {
        let model_str = model.as_ref().expect("split should produce model");
        let pass_count = model_str.matches("[PASS]").count();
        let fail_count = model_str.matches("[FAIL]").count();
        assert!(
            pass_count >= 2,
            "expected >=2 [PASS] markers, got {pass_count} in: {model_str}"
        );
        assert!(
            fail_count >= 2,
            "expected >=2 [FAIL] markers, got {fail_count} in: {model_str}"
        );
    }
}

/// Passing assertion has zero overhead — no splitting occurs.
///
/// x == 5 assumed, assert x > 0 && x < 10. Both conjuncts pass,
/// so the result is Verified with no splitting attempt.
#[test]
fn test_passing_conjunction_no_split_overhead() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assert("both_pass", "x > 0 && x < 10"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x == 5 satisfies x > 0 && x < 10");
}

/// Single (atomic) assertion failure is NOT split — returns normal counterexample.
///
/// x == 5 assumed, assert x > 10. No compound expression to split.
#[test]
fn test_atomic_assertion_not_split() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assert("simple", "x > 10"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "x == 5 violates x > 10");

    // Atomic assertion should NOT produce split markers.
    if let VerifyResult::Counterexample {
        model: Some(model_str),
        ..
    } = &result
    {
        assert!(
            !model_str.contains("[PASS]") && !model_str.contains("[FAIL]"),
            "atomic assertion should not be split, got: {model_str}"
        );
    }
}

/// Mixed pass/fail conjunction with variables produces structured output.
///
/// x == 3, y == 7; assert (x < 5) && (y < 5) && (x + y < 20).
/// Conjunct 1 (x < 5) passes, conjunct 2 (y < 5) fails, conjunct 3 passes.
#[test]
fn test_conjunction_split_two_variables() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 3"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 7"));
    ctx.push_obligation(ProofObligation::assert(
        "multi_var",
        "x < 5 && y < 5 && x + y < 20",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "y == 7 violates y < 5");

    if let VerifyResult::Counterexample { model, .. } = &result {
        let model_str = model.as_ref().expect("split should produce model");
        // Should have per-conjunct results
        assert!(
            model_str.contains("conjunct"),
            "model should contain 'conjunct' labels, got: {model_str}"
        );
    }
}

/// All conjuncts fail — every sub-assertion marked [FAIL].
#[test]
fn test_conjunction_all_fail() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    // x < 0 fails, x > 100 fails
    ctx.push_obligation(ProofObligation::assert("all_fail", "x < 0 && x > 100"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "both conjuncts fail");

    if let VerifyResult::Counterexample { model, .. } = &result {
        let model_str = model.as_ref().expect("split should produce model");
        // Count [FAIL] markers — should be 2
        let fail_count = model_str.matches("[FAIL]").count();
        assert!(
            fail_count >= 2,
            "both conjuncts should fail, got {fail_count} [FAIL] markers in: {model_str}"
        );
    }
}

// ─── split_assertion unit tests (non-parser patterns: Implies, Ite, Forall) ──

fn bool_var(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.into(),
        ty: TrustVcType::Bool,
    }
}

fn and(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(left),
        right: Box::new(right),
    }
}

/// split_assertion on Implies with compound consequent splits into per-consequent parts.
#[test]
fn test_split_assertion_implies_compound_consequent() {
    let expr = TrustVcExpr::Implies {
        premise: Box::new(bool_var("p")),
        conclusion: Box::new(and(bool_var("a"), bool_var("b"))),
    };

    let parts = split_assertion(&expr).expect("should split implies with compound consequent");
    assert_eq!(parts.len(), 2);
    assert!(parts[0].label.contains("implication consequent"));
    assert!(parts[1].label.contains("implication consequent"));
}

/// split_assertion on Implies with atomic consequent returns None.
#[test]
fn test_split_assertion_implies_atomic_consequent_no_split() {
    let expr = TrustVcExpr::Implies {
        premise: Box::new(bool_var("p")),
        conclusion: Box::new(bool_var("q")),
    };
    assert!(split_assertion(&expr).is_none());
}

/// split_assertion on Ite splits into then-branch and else-branch.
#[test]
fn test_split_assertion_ite_produces_two_branches() {
    let expr = TrustVcExpr::Ite {
        cond: Box::new(bool_var("c")),
        then_branch: Box::new(bool_var("a")),
        else_branch: Box::new(bool_var("b")),
        ty: TrustVcType::Bool,
    };

    let parts = split_assertion(&expr).expect("should split ite");
    assert_eq!(parts.len(), 2);
    assert_eq!(parts[0].label, "then branch");
    assert_eq!(parts[1].label, "else branch");
}

/// split_assertion on Forall with compound body splits per-conjunct.
#[test]
fn test_split_assertion_forall_compound_body() {
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".into(), TrustVcType::Int { width: 32 })],
        body: Box::new(and(bool_var("a"), and(bool_var("b"), bool_var("c")))),
        triggers: None,
        trigger_inference_mode: None,
    };

    let parts = split_assertion(&expr).expect("should split forall with compound body");
    assert_eq!(parts.len(), 3);
    assert!(parts[0].label.contains("forall conjunct"));
}

/// split_assertion on atomic expression returns None.
#[test]
fn test_split_assertion_atomic_returns_none() {
    assert!(split_assertion(&bool_var("a")).is_none());
    assert!(split_assertion(&TrustVcExpr::BoolLit(true)).is_none());
}

// ─── Proof-step localization: display label in counterexample output (#2652) ─

/// A failing assert_by with ProofStepMeta uses the display label in the
/// counterexample obligation_name, not the internal scope key.
#[test]
fn test_step_meta_display_label_in_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));

    // Create an assert_by that will fail, with step_meta
    let scoped = vec![];
    ctx.add_assert_by("calc_line_7_step_2", "x > 10", scoped);
    if let Some(last) = ctx.obligations.last_mut() {
        last.step_meta = Some(crate::vc::ProofStepMeta::new(
            "calc_line_7_step_2",
            "calc step 2 of 3",
        ));
        last.location = Some("src/test.rs:7:1".to_string());
    }

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "assert_by with step_meta should fail");

    if let VerifyResult::Counterexample {
        obligation_name, ..
    } = &result
    {
        assert!(
            obligation_name.contains("calc step 2 of 3"),
            "obligation_name should contain display label 'calc step 2 of 3', got: {obligation_name}"
        );
        assert!(
            obligation_name.contains("src/test.rs:7:1"),
            "obligation_name should contain location, got: {obligation_name}"
        );
    }
}

/// A failing compound regular assertion with step_meta produces
/// [PASS]/[FAIL] split markers AND uses the display label in obligation_name.
/// Split localization runs for regular Assert obligations (typed_assertions.rs),
/// not for AssertBy obligations which use a separate verification path.
#[test]
fn test_step_meta_compound_conjunction_shows_label_and_split() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));

    // Regular Assert with compound condition: x > 0 passes, x > 10 fails.
    // Attach step_meta to verify display_name() flows through split.rs.
    let mut ob = ProofObligation::assert("assert_line_15_col_5", "x > 0 && x > 10");
    ob.step_meta = Some(crate::vc::ProofStepMeta::new(
        "assert_line_15_col_5",
        "calc step 1 of 2",
    ));
    ctx.push_obligation(ob);

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "compound assertion should fail on x > 10");

    if let VerifyResult::Counterexample {
        obligation_name,
        model,
        ..
    } = &result
    {
        // The obligation_name from split.rs should use the display label
        assert!(
            obligation_name.contains("calc step 1 of 2"),
            "obligation_name should use display label, got: {obligation_name}"
        );

        // The split model should contain localization markers
        if let Some(model_str) = model {
            assert!(
                model_str.contains("[FAIL]") || model_str.contains("[PASS]"),
                "compound assertion should have split markers in model, got: {model_str}"
            );
        }
    }
}

/// Two obligations on the same line but with different step_meta keys
/// produce distinct counterexample names.
#[test]
fn test_same_line_different_step_meta_distinct_names() {
    use crate::vc::VerificationContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::MathInt);

    // First assert_by — provable
    let scoped1 = vec![ProofObligation::assume("helper1", "x > 100")];
    ctx.add_assert_by("assert_by_line_42_col_5", "x > 0", scoped1);

    // Second assert_by — unprovable
    let scoped2 = vec![];
    ctx.add_assert_by("assert_by_line_42_col_30", "x > 200", scoped2);
    if let Some(last) = ctx.obligations.last_mut() {
        last.location = Some("test.rs:42:30".to_string());
    }

    let result = ctx.verify();
    // The first assert_by should pass, the second should fail.
    match &result {
        VerifyResult::Counterexample {
            obligation_name, ..
        } => {
            // The failing obligation should reference col_30, not col_5
            assert!(
                obligation_name.contains("assert_by_line_42_col_30")
                    || obligation_name.contains("42:30"),
                "failing obligation should identify the col_30 call site, got: {obligation_name}"
            );
        }
        other => panic!("expected Counterexample for unprovable second assert_by, got: {other:?}"),
    }
}
