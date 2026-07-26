//! Discriminating tests for inline quantifier trigger inference (#2461).
//!
//! These tests verify that the `trigger_inference_mode` field on
//! `TrustVcExpr::Quantifier` is:
//! 1. Captured from the thread-local mode at construction time
//! 2. Threaded through to `encode_quantifier`
//! 3. Produces different trigger counts for conservative vs aggressive mode
//! 4. Does not override explicit user triggers
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Part of #2461 Slice 3.

use super::*;
use crate::ir::TrustVcType;
use crate::ir_expr::{ArithOp, CompareOp, LogicOp, QuantifierKind, TrustVcExpr};
use crate::trigger_inference::TriggerInferenceMode;

fn i32_var(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty: i32_ty(),
    }
}

fn i32_lit(value: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value,
        ty: i32_ty(),
    }
}

fn fn_call_i32(name: &str, args: Vec<TrustVcExpr>) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: name.to_string(),
        args,
        return_ty: i32_ty(),
    }
}

// MathInt-typed helpers for encoder integration tests.
// Quantifier bound vars are encoded with Sort::Int (int mode), so functions
// must also use MathInt domain sorts to avoid sort mismatch.

fn mint_var(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty: TrustVcType::MathInt,
    }
}

fn mint_lit(value: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value,
        ty: TrustVcType::MathInt,
    }
}

fn fn_call_mint(name: &str, args: Vec<TrustVcExpr>) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: name.to_string(),
        args,
        return_ty: TrustVcType::MathInt,
    }
}

fn fn_call_bool_mint(name: &str, args: Vec<TrustVcExpr>) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: name.to_string(),
        args,
        return_ty: TrustVcType::Bool,
    }
}

/// Body with two eligible function-call triggers, each covering x.
/// `f(x) > 0 && g(x) > 0`
fn two_trigger_body() -> TrustVcExpr {
    TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(fn_call_i32("f", vec![i32_var("x")])),
            right: Box::new(i32_lit(0)),
        }),
        right: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(fn_call_i32("g", vec![i32_var("x")])),
            right: Box::new(i32_lit(0)),
        }),
    }
}

/// Pure arithmetic body with no eligible trigger candidates.
/// `x + 1 > 0`
fn pure_arith_body() -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: CompareOp::Gt,
        left: Box::new(TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(i32_var("x")),
            right: Box::new(i32_lit(1)),
            ty: i32_ty(),
        }),
        right: Box::new(i32_lit(0)),
    }
}

/// MathInt version of two_trigger_body for encoder integration tests.
fn two_trigger_body_mint() -> TrustVcExpr {
    TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(fn_call_mint("f", vec![mint_var("x")])),
            right: Box::new(mint_lit(0)),
        }),
        right: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(fn_call_mint("g", vec![mint_var("x")])),
            right: Box::new(mint_lit(0)),
        }),
    }
}

/// MathInt version of pure_arith_body for encoder integration tests.
fn pure_arith_body_mint() -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: CompareOp::Gt,
        left: Box::new(TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(mint_var("x")),
            right: Box::new(mint_lit(1)),
            ty: TrustVcType::MathInt,
        }),
        right: Box::new(mint_lit(0)),
    }
}

fn spec_fn(
    name: &str,
    params: &[(&str, TrustVcType)],
    return_ty: TrustVcType,
) -> crate::vc::FunctionContext {
    crate::vc::FunctionContext {
        name: name.to_string(),
        params: params
            .iter()
            .map(|(n, t)| (n.to_string(), t.clone()))
            .collect(),
        return_type: return_ty,
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    }
}

/// Encode a TrustVcExpr using a AYEncoder that has f, g, h registered.
///
/// Functions use MathInt params because quantifier-bound variables are
/// encoded with Sort::Int (int mode). Using Int{32} here would create
/// BV(32)-domain UFs which mismatch the Int-sorted bound vars.
fn encode_with_functions(quant: &TrustVcExpr) -> crate::error::TrustVcResult<ay_dpll::api::Term> {
    let mut encoder = AYEncoder::new();
    encoder
        .register_function_context(&spec_fn(
            "f",
            &[("x", TrustVcType::MathInt)],
            TrustVcType::MathInt,
        ))
        .expect("register f");
    encoder
        .register_function_context(&spec_fn(
            "g",
            &[("x", TrustVcType::MathInt)],
            TrustVcType::MathInt,
        ))
        .expect("register g");
    encoder
        .register_function_context(&spec_fn(
            "h",
            &[("x", TrustVcType::MathInt)],
            TrustVcType::Bool,
        ))
        .expect("register h");

    let variables = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut encoder.solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &encoder.fn_ctx.functions,
    );

    parser.encode_trust_vc_expr(quant)
}

// ========================================================================
// IR-level: trigger_inference_mode captured from thread-local
// ========================================================================

/// DISCRIMINATING: ir_builder::forall captures None when no thread-local mode is set.
#[test]
fn test_forall_captures_none_mode_by_default() {
    let expr =
        crate::ir_builder::forall(vec![("x".to_string(), i32_ty())], two_trigger_body(), None);
    match &expr {
        TrustVcExpr::Quantifier {
            trigger_inference_mode,
            ..
        } => {
            assert_eq!(
                *trigger_inference_mode, None,
                "default forall should capture None trigger_inference_mode"
            );
        }
        _ => panic!("ir_builder::forall must produce Quantifier"),
    }
}

/// DISCRIMINATING: ir_builder::forall captures Aggressive when thread-local is set.
#[test]
fn test_forall_captures_aggressive_mode_from_thread_local() {
    crate::broadcast_state::set_trigger_inference_mode(TriggerInferenceMode::Aggressive);
    let expr =
        crate::ir_builder::forall(vec![("x".to_string(), i32_ty())], two_trigger_body(), None);
    // Clean up thread-local.
    crate::broadcast_state::set_trigger_inference_mode(TriggerInferenceMode::Conservative);

    match &expr {
        TrustVcExpr::Quantifier {
            trigger_inference_mode,
            ..
        } => {
            assert_eq!(
                *trigger_inference_mode,
                Some(TriggerInferenceMode::Aggressive),
                "forall built while thread-local is Aggressive must capture that mode"
            );
        }
        _ => panic!("ir_builder::forall must produce Quantifier"),
    }
}

// ========================================================================
// Inference algorithm: conservative vs aggressive produce different results
// ========================================================================

/// DISCRIMINATING: conservative mode infers exactly 1 trigger group for a body
/// with two eligible function-call candidates.
#[test]
fn test_conservative_infers_one_trigger_group() {
    let body = two_trigger_body();
    let bvars = vec![("x".to_string(), i32_ty())];
    let result = crate::trigger_inference::infer_triggers_with_mode(
        &bvars,
        &body,
        TriggerInferenceMode::Conservative,
    );
    assert_eq!(
        result.len(),
        1,
        "conservative mode must return exactly 1 trigger group, got {}",
        result.len()
    );
}

/// DISCRIMINATING: aggressive mode infers 2 trigger groups for the same body
/// (one per eligible function call: f(x) and g(x)).
#[test]
fn test_aggressive_infers_two_trigger_groups() {
    let body = two_trigger_body();
    let bvars = vec![("x".to_string(), i32_ty())];
    let result = crate::trigger_inference::infer_triggers_with_mode(
        &bvars,
        &body,
        TriggerInferenceMode::Aggressive,
    );
    assert_eq!(
        result.len(),
        2,
        "aggressive mode must return 2 trigger groups for f(x) and g(x), got {}",
        result.len()
    );
}

/// DISCRIMINATING: pure arithmetic body produces no triggers regardless of mode.
#[test]
fn test_pure_arith_no_triggers_either_mode() {
    let body = pure_arith_body();
    let bvars = vec![("x".to_string(), i32_ty())];

    let conservative = crate::trigger_inference::infer_triggers_with_mode(
        &bvars,
        &body,
        TriggerInferenceMode::Conservative,
    );
    let aggressive = crate::trigger_inference::infer_triggers_with_mode(
        &bvars,
        &body,
        TriggerInferenceMode::Aggressive,
    );
    assert!(
        conservative.is_empty(),
        "pure arithmetic body must have no triggers in conservative mode"
    );
    assert!(
        aggressive.is_empty(),
        "pure arithmetic body must have no triggers in aggressive mode"
    );
}

// ========================================================================
// Encoder integration: mode threaded through encode_quantifier
// ========================================================================

/// DISCRIMINATING: encoder accepts quantifier with conservative (default) mode.
#[test]
fn test_encoder_conservative_mode_encodes_without_error() {
    let quant = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".to_string(), TrustVcType::MathInt)],
        body: Box::new(two_trigger_body_mint()),
        triggers: None,
        trigger_inference_mode: None,
    };
    let result = encode_with_functions(&quant);
    assert!(
        result.is_ok(),
        "quantifier with conservative trigger mode must encode: {:?}",
        result.err()
    );
}

/// DISCRIMINATING: encoder accepts quantifier with aggressive mode.
#[test]
fn test_encoder_aggressive_mode_encodes_without_error() {
    let quant = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".to_string(), TrustVcType::MathInt)],
        body: Box::new(two_trigger_body_mint()),
        triggers: None,
        trigger_inference_mode: Some(TriggerInferenceMode::Aggressive),
    };
    let result = encode_with_functions(&quant);
    assert!(
        result.is_ok(),
        "quantifier with aggressive trigger mode must encode: {:?}",
        result.err()
    );
}

/// DISCRIMINATING: explicit triggers override inference regardless of mode.
#[test]
fn test_explicit_triggers_override_inference() {
    let explicit_trigger = fn_call_bool_mint("h", vec![mint_var("x")]);
    let quant = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".to_string(), TrustVcType::MathInt)],
        body: Box::new(two_trigger_body_mint()),
        triggers: Some(vec![vec![explicit_trigger]]),
        trigger_inference_mode: Some(TriggerInferenceMode::Aggressive),
    };
    let result = encode_with_functions(&quant);
    assert!(
        result.is_ok(),
        "explicit triggers must override inference without error: {:?}",
        result.err()
    );
}

/// DISCRIMINATING: pure arithmetic body encodes without triggers regardless of mode.
#[test]
fn test_encoder_pure_arith_aggressive_no_triggers() {
    let quant = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".to_string(), TrustVcType::MathInt)],
        body: Box::new(pure_arith_body_mint()),
        triggers: None,
        trigger_inference_mode: Some(TriggerInferenceMode::Aggressive),
    };
    let result = encode_with_functions(&quant);
    assert!(
        result.is_ok(),
        "pure arithmetic quantifier must encode even with aggressive mode: {:?}",
        result.err()
    );
}
