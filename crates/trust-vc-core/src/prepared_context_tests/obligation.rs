//! Obligation-preparation tests for prepared_context.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::*;
use crate::ir::TrustVcType;
use crate::ir_lowering::COLLECTION_CONSTRUCTOR_PREFIX;
use crate::vc::{ConditionOrigin, ObligationKind, ProofObligation, TypedProofObligation};

#[test]
fn test_prepare_context_fails_on_parse_error() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("broken", "x +"));

    let result = prepare_context(&ctx);
    assert!(matches!(result, Err(TrustVcError::Encoding { .. })));

    let message = result.expect_err("must fail parse").to_string();
    assert!(message.contains("Failed to parse obligation 'broken'"));
}

#[test]
fn test_prepare_context_fails_on_lowering_error() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert("unresolved", "x > 0"));

    let result = prepare_context(&ctx);
    assert!(matches!(result, Err(TrustVcError::Encoding { .. })));

    let message = result.expect_err("must fail lowering").to_string();
    assert!(message.contains("Failed to lower obligation 'unresolved'"));
}

#[test]
fn test_prepare_context_fails_on_empty_function_return_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.function_context = Some(FunctionContext {
        name: "my_fn".to_string(),
        return_type: TrustVcType::Opaque("".to_string()),
        params: vec![],
        is_recursive: false,
        mode: crate::mode::FunctionMode::Exec,
        trait_bounds: vec![],
    });
    ctx.push_obligation(ProofObligation::assert("check", "x > 0"));

    let result = prepare_context(&ctx);
    assert!(matches!(result, Err(TrustVcError::Encoding { .. })));

    let message = result.expect_err("must fail").to_string();
    assert!(
        message.contains("invalid return type '' for function 'my_fn'"),
        "Error should identify the bad type and function, got: {}",
        message
    );
}

#[test]
fn test_prepare_context_fails_on_malformed_map_return_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.function_context = Some(FunctionContext {
        name: "bad_map_fn".to_string(),
        return_type: TrustVcType::Opaque("Map<i32>".to_string()),
        params: vec![],
        is_recursive: false,
        mode: crate::mode::FunctionMode::Exec,
        trait_bounds: vec![],
    });
    ctx.push_obligation(ProofObligation::assert("check", "x > 0"));

    let result = prepare_context(&ctx);
    assert!(matches!(result, Err(TrustVcError::Encoding { .. })));

    let message = result.expect_err("must fail").to_string();
    assert!(
        message.contains("invalid return type") && message.contains("bad_map_fn"),
        "Error should identify the bad type and function, got: {}",
        message
    );
}

#[test]
fn test_prepare_context_registers_helper_functions_in_type_env() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.declare_helper_function_typed("helper", TrustVcType::Int { width: 32 }, vec![]);
    ctx.push_obligation(ProofObligation::assert("check", "helper(x) > 0"));

    let prepared = prepare_context(&ctx);
    assert!(
        prepared.is_ok(),
        "prepare_context should succeed with helper function registered, got: {:?}",
        prepared.err()
    );
}

#[test]
fn test_prepare_context_lowers_trigger_patterns_to_prepared_metadata() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.declare_helper_function_typed(
        "f",
        TrustVcType::Bool,
        vec![("x".to_string(), TrustVcType::Int { width: 32 })],
    );
    ctx.declare_helper_function_typed(
        "g",
        TrustVcType::Bool,
        vec![("x".to_string(), TrustVcType::Int { width: 32 })],
    );
    ctx.obligations.push(
        ProofObligation::broadcast_assume("broadcast_fg", "x == x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["f(x)".to_string()], vec!["g(x)".to_string()]]),
    );

    let prepared = prepare_context(&ctx).expect("triggered broadcast should prepare");
    let obligation = prepared
        .obligations
        .first()
        .expect("prepared context should contain the broadcast");
    let groups = obligation
        .prepared_triggers
        .as_ref()
        .expect("from_legacy should populate prepared trigger metadata");

    assert_eq!(groups.len(), 2);
    assert_eq!(groups[0].len(), 1);
    assert_eq!(groups[0][0].source, "f(x)");
    assert_eq!(groups[0][0].head_symbol.as_deref(), Some("f"));
    assert!(matches!(
        groups[0][0].expr,
        TrustVcExpr::FnCall { ref name, .. } if name == "f"
    ));
    assert_eq!(
        obligation
            .trigger_head_symbols()
            .iter()
            .map(|symbol| symbol.as_ref())
            .collect::<Vec<_>>(),
        vec!["f", "g"]
    );
    assert_eq!(
        obligation
            .eager_seed_symbols()
            .iter()
            .map(|symbol| symbol.as_ref())
            .collect::<Vec<_>>(),
        vec!["f", "g"]
    );
}

#[test]
fn test_prepare_context_collects_collection_constructor_contexts() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "seq_empty",
        "trust_vc_types::Seq::<i32>::empty().push(1).len() == 1",
    ));

    let prepared = prepare_context(&ctx).expect("collection constructor chain should prepare");
    let constructor = prepared
        .helper_function_contexts
        .iter()
        .find(|func_ctx| func_ctx.name.starts_with(COLLECTION_CONSTRUCTOR_PREFIX))
        .expect("typed collection constructor should be registered as helper context");

    assert!(constructor.params.is_empty());
    assert_eq!(
        constructor.return_type,
        TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }))
    );
}

#[test]
#[allow(deprecated)]
fn test_prepare_context_fails_on_invalid_helper_return_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.declare_helper_function("bad_helper", "");
    ctx.push_obligation(ProofObligation::assert("check", "x > 0"));

    let result = prepare_context(&ctx);
    assert!(matches!(result, Err(TrustVcError::Encoding { .. })));

    let message = result.expect_err("must fail").to_string();
    assert!(
        message.contains("invalid return type")
            && message.contains("bad_helper")
            && message.contains("Empty type string"),
        "Error should identify the bad type and function, got: {}",
        message
    );
}

#[test]
fn test_prepare_context_rejects_cached_expr_over_depth_limit() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.declare_helper_function_typed("helper", TrustVcType::Int { width: 32 }, vec![]);

    let name = "cached_depth_limit";
    let condition = "helper(x)";
    ctx.push_obligation(ProofObligation::assert(name, condition));
    crate::obligation_collection::cache_pre_built_expr(
        name.to_string(),
        condition.to_string(),
        build_cached_fn_call_chain(crate::expr_depth::MAX_EXPR_DEPTH + 1),
    );

    let err = prepare_context(&ctx).expect_err("over-limit cached IR must fail closed");
    let message = err.to_string();
    assert!(
        message.contains("Failed to validate cached obligation 'cached_depth_limit'"),
        "expected cached-obligation validation failure, got: {message}",
    );
    assert!(
        message.contains("prepared-context cached expression repair"),
        "expected cached-expression stage in error, got: {message}",
    );
}

#[test]
fn test_prepare_context_preserves_condition_origin() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assert("typed_origin", "x > 0"));
    ctx.push_obligation(
        ProofObligation::assert("cached_origin", "x > 1")
            .with_condition_origin(ConditionOrigin::PreBuiltExprCache),
    );
    ctx.push_obligation(
        ProofObligation::assert("translated_origin", "x > 2")
            .with_condition_origin(ConditionOrigin::LegacyTranslatedString),
    );
    crate::obligation_collection::cache_pre_built_expr(
        "cached_origin".to_string(),
        "x > 1".to_string(),
        TrustVcExpr::Compare {
            op: crate::ir_expr::CompareOp::Gt,
            left: Box::new(TrustVcExpr::Var {
                name: "x".to_string(),
                ty: TrustVcType::Int { width: 32 },
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 1,
                ty: TrustVcType::Int { width: 32 },
            }),
        },
    );

    let prepared = prepare_context(&ctx).expect("origins should prepare cleanly");
    let origins = prepared
        .obligations
        .iter()
        .map(|obligation| (obligation.name.as_str(), obligation.condition_origin))
        .collect::<std::collections::HashMap<_, _>>();

    assert_eq!(
        origins.get("typed_origin"),
        Some(&ConditionOrigin::LoweredFromCondition)
    );
    assert_eq!(
        origins.get("cached_origin"),
        Some(&ConditionOrigin::PreBuiltExprCache)
    );
    assert_eq!(
        origins.get("translated_origin"),
        Some(&ConditionOrigin::LegacyTranslatedString)
    );
}

#[test]
fn test_prepare_context_uses_typed_obligation_without_parsing_condition_label() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    let typed_expr = TrustVcExpr::Compare {
        op: crate::ir::CompareOp::Gt,
        left: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::Int { width: 32 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::Int { width: 32 },
        }),
    };
    ctx.push_typed_obligation(TypedProofObligation::new(
        "typed_gt_zero",
        typed_expr.clone(),
        ObligationKind::Assert,
    ));

    let prepared = prepare_context(&ctx).expect("typed obligation should prepare");
    let obligation = prepared
        .obligations
        .first()
        .expect("prepared obligation should exist");

    assert_eq!(obligation.condition, "<typed:typed_gt_zero>");
    assert_eq!(
        obligation.condition_origin,
        ConditionOrigin::TypedTrustVcExpr
    );
    assert_eq!(obligation.expr, typed_expr);
}

fn build_cached_fn_call_chain(depth: usize) -> TrustVcExpr {
    let mut expr = TrustVcExpr::Var {
        name: "x".to_string(),
        ty: TrustVcType::Int { width: 32 },
    };

    for _ in 0..depth {
        expr = TrustVcExpr::FnCall {
            name: "helper".to_string(),
            args: vec![expr],
            return_ty: TrustVcType::Bool,
        };
    }

    expr
}
