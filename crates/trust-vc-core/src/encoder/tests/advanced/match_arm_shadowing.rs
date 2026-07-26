//! Match-arm shadowing regressions for trigger inference and explicit triggers.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::ir::{CompareOp, MatchArm, MatchPattern, TrustVcExpr, TrustVcType};
use crate::trigger_inference::infer_triggers;
use crate::vc::ProofObligation;

fn bool_ty() -> TrustVcType {
    TrustVcType::Bool
}

fn var(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty: u32_ty(),
    }
}

fn int_lit(value: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value,
        ty: u32_ty(),
    }
}

fn fn_call(name: &str, args: Vec<TrustVcExpr>) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: name.to_string(),
        args,
        return_ty: u32_ty(),
    }
}

fn compare_gt(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: CompareOp::Gt,
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn bound_vars(names: &[&str]) -> Vec<(String, TrustVcType)> {
    names
        .iter()
        .map(|name| ((*name).to_string(), u32_ty()))
        .collect()
}

#[test]
fn test_infer_triggers_match_arm_constructor_shadowing_excludes_candidate() {
    let body = TrustVcExpr::Match {
        scrutinee: Box::new(var("foo")),
        arms: vec![
            MatchArm::new(
                MatchPattern::Constructor {
                    variant_name: "Some".to_string(),
                    bindings: vec!["x".to_string()],
                    has_rest: false,
                },
                compare_gt(fn_call("f", vec![var("x")]), int_lit(0)),
            ),
            MatchArm::new(MatchPattern::Wildcard, TrustVcExpr::BoolLit(true)),
        ],
        ty: bool_ty(),
    };

    let result = infer_triggers(&bound_vars(&["x"]), &body);
    assert!(
        result.is_empty(),
        "constructor-bound x inside a match arm must not count as the outer quantifier x"
    );
}

#[test]
fn test_infer_triggers_match_arm_ident_shadowing_excludes_candidate() {
    let body = TrustVcExpr::Match {
        scrutinee: Box::new(var("foo")),
        arms: vec![MatchArm::new(
            MatchPattern::Ident("x".to_string()),
            compare_gt(fn_call("f", vec![var("x")]), int_lit(0)),
        )],
        ty: bool_ty(),
    };

    let result = infer_triggers(&bound_vars(&["x"]), &body);
    assert!(
        result.is_empty(),
        "ident-bound x inside a match arm must not count as the outer quantifier x"
    );
}

/// String-based trigger patterns bypass `expr_references_any_name` validation
/// (they go through `encode_trigger_typed` → `lower_syn_expr` → direct Term
/// encoding). The match-arm `x` is treated as the solver variable `x` rather
/// than being recognized as a shadowing binding. TrustVcExpr-based triggers
/// DO catch this — see `test_infer_triggers_match_arm_*` tests above.
#[test]
fn test_broadcast_string_trigger_match_arm_shadowing_encodes_without_scoping_check() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("scrutinee", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(
        ProofObligation::broadcast_assume("match_shadowed_trigger", "x == x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["match scrutinee { x => x }".to_string()]]),
    );
    ctx.push_obligation(crate::vc::ProofObligation::assert("check", "x == x"));

    let result = AYEncoder::verify(&ctx);
    // Known limitation: string trigger path treats arm-bound x as the quantifier x.
    // The trigger references the solver variable, so the quantifier encodes and
    // the assertion is verified. See encode_trigger_typed in eval.rs.
    expect_verified(
        &result,
        "string trigger path does not scope-check match arms",
    );
}

#[test]
fn test_broadcast_trigger_match_arm_unshadowed_name_still_encodes() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("scrutinee", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(
        ProofObligation::broadcast_assume("match_unshadowed_trigger", "x == x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["match scrutinee { y => x }".to_string()]]),
    );
    ctx.push_obligation(crate::vc::ProofObligation::assert("check", "x == x"));

    let result = AYEncoder::verify(&ctx);
    expect_encodes_without_error(
        &result,
        "match-arm triggers that still mention the outer x should encode without validation errors",
    );
}
