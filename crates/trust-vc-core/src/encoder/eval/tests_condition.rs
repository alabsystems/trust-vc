// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::AYEncoder;
use crate::error::TrustVcError;
use crate::ir::{TrustVcExpr, TrustVcType};
use crate::vc::FunctionContext;
use ay_dpll::api::Sort;

#[test]
fn test_encode_trigger_typed_parse_failures_use_parse_variant() {
    let mut encoder = AYEncoder::new();

    let result = encoder.encode_trigger_typed("x +");

    match result {
        Err(TrustVcError::Parse { context, .. }) => {
            assert_eq!(context, "parse trigger");
        }
        other => panic!(
            "malformed trigger should surface as TrustVcError::Parse, got: {:?}",
            other
        ),
    }
}

#[test]
fn test_resolve_condition_typed_with_bindings_requires_bound_var_type() {
    let mut encoder = AYEncoder::new();
    let x = encoder.solver.declare_const("x", Sort::bitvec(32));
    let expr = TrustVcExpr::Var {
        name: "x".to_string(),
        ty: TrustVcType::Int { width: 32 },
    };

    let result = encoder.resolve_condition_typed_with_bindings(&expr, &[("x", x)]);

    match result {
        Err(TrustVcError::Internal { context, detail }) => {
            assert_eq!(context, "resolve typed condition with bindings");
            assert!(
                detail.contains("Missing type for bound variable 'x'"),
                "missing bound variable type detail should be preserved, got: {}",
                detail
            );
        }
        other => panic!(
            "missing bound variable type should surface as TrustVcError::Internal, got: {:?}",
            other
        ),
    }
}

/// Regression: zero-arity helper functions must be visible to trigger
/// lowering through the cached `lowering_env`. Before #2181, the env was
/// rebuilt per call so this worked implicitly; the cache must replicate
/// the dual-visibility (variable + function namespace) behavior.
#[test]
fn test_encode_trigger_typed_zero_arity_helper_via_cached_env() {
    let mut encoder = AYEncoder::new();

    // Register a zero-arity helper that returns i32.
    let func_ctx = FunctionContext {
        name: "magic_const".to_string(),
        params: vec![],
        return_type: TrustVcType::Int { width: 32 },
        is_recursive: false,
        mode: crate::mode::FunctionMode::Exec,
        trait_bounds: vec![],
    };
    encoder
        .register_function_context(&func_ctx)
        .expect("zero-arity registration should succeed");

    // Trigger expression referencing the zero-arity constant.
    let result = encoder.encode_trigger_typed("magic_const");
    assert!(
        result.is_ok(),
        "trigger encoding of zero-arity helper should succeed via cached env, got: {:?}",
        result
    );
}

/// Regression: Ite conditions with arithmetic comparisons must be
/// evaluable in Compute mode. Before this fix, try_reduce_to_int
/// called try_const_eval_typed (which can't reduce `2+3==5`) instead
/// of try_compute_eval (which can). Part of #2405.
#[test]
fn test_try_reduce_to_int_ite_with_arithmetic_condition() {
    use crate::ir::{ArithOp, CompareOp};

    // if (2 + 3 == 5) { 10 } else { 20 } → should reduce to 10
    let cond = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(TrustVcExpr::IntLit {
                value: 2,
                ty: TrustVcType::Int { width: 32 },
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 3,
                ty: TrustVcType::Int { width: 32 },
            }),
            ty: TrustVcType::Int { width: 32 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 5,
            ty: TrustVcType::Int { width: 32 },
        }),
    };
    let expr = TrustVcExpr::Ite {
        cond: Box::new(cond),
        then_branch: Box::new(TrustVcExpr::IntLit {
            value: 10,
            ty: TrustVcType::Int { width: 32 },
        }),
        else_branch: Box::new(TrustVcExpr::IntLit {
            value: 20,
            ty: TrustVcType::Int { width: 32 },
        }),
        ty: TrustVcType::Int { width: 32 },
    };

    let result = AYEncoder::try_reduce_to_int(&expr);
    assert_eq!(
        result,
        Some(10),
        "Ite with arithmetic condition (2+3==5) should reduce to then-branch"
    );
}
