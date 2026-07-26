//! Performance proofs for `prepare_context` hot paths.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! These tests cover the preparation boundary before solver work begins:
//! string parsing/lowering of obligations, scoped proof preparation, and the
//! cached-expression repair walk.

use super::*;

/// Maximum allowed ratio between T(4N) and T(N).
/// Linear = ~4x, quadratic = ~16x. We use 12x as the threshold.
const QUADRATIC_THRESHOLD: f64 = 12.0;

/// Minimum timing to avoid division by near-zero durations.
const MIN_MEASURABLE_US: u128 = 100;

/// `prepare_context` parses and lowers each obligation exactly once. With
/// fixed variable/function context and N obligations, the hot path should be
/// O(N), not O(N²).
#[test]
fn test_prepare_context_obligation_scaling_linear() {
    let small = 25;
    let large = 100;

    let t_small = measure_median(|| time_prepare_context_obligations(small, 10), 3);
    let t_large = measure_median(|| time_prepare_context_obligations(large, 10), 3);

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large as f64 / small as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "prepare_context obligation scaling appears quadratic: \
         T({})={}μs, T({})={}μs, ratio={:.1}x, normalized={:.1}x. \
         syn::parse_str or lowering may be re-walking prior obligations.",
        small,
        t_small,
        large,
        t_large,
        ratio,
        normalized,
    );
}

fn time_prepare_context_obligations(n_obligations: usize, iterations: usize) -> u128 {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_helper_function_typed(
        "helper",
        crate::ir::TrustVcType::parse_or_opaque("i32"),
        vec![],
    );

    for i in 0..n_obligations {
        ctx.push_obligation(ProofObligation::assert(
            format!("check_{}", i),
            format!("helper(x) + y >= {}", i % 4),
        ));
    }

    let start = std::time::Instant::now();
    for _ in 0..iterations {
        let prepared =
            crate::prepared_context::prepare_context(&ctx).expect("prepare_context should parse");
        assert_eq!(prepared.obligations.len(), n_obligations);
    }
    start.elapsed().as_micros()
}

/// `prepare_context` also reparses scoped proof obligations stored in
/// `assert_by_scopes`. With S scopes and fixed obligations per scope, that
/// nested preparation loop should stay O(S), not regress to O(S²).
#[test]
fn test_prepare_context_assert_by_scope_scaling_linear() {
    let small = 10;
    let large = 40;
    let iterations = 25;

    let t_small = measure_median(
        || time_prepare_context_assert_by_scopes(small, iterations),
        3,
    );
    let t_large = measure_median(
        || time_prepare_context_assert_by_scopes(large, iterations),
        3,
    );

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large as f64 / small as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "prepare_context assert_by scope scaling appears quadratic: \
         T({})={}μs, T({})={}μs, ratio={:.1}x, normalized={:.1}x. \
         nested scoped-obligation preparation should stay O(S) in scope count.",
        small,
        t_small,
        large,
        t_large,
        ratio,
        normalized,
    );
}

fn time_prepare_context_assert_by_scopes(n_scopes: usize, iterations: usize) -> u128 {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));

    for i in 0..n_scopes {
        ctx.assert_by_scopes
            .insert(format!("scope_{i}"), build_assert_by_scope_obligations(i));
    }

    let start = std::time::Instant::now();
    for _ in 0..iterations {
        let prepared =
            crate::prepared_context::prepare_context(&ctx).expect("prepare_context should parse");
        let scoped_obligation_count: usize = prepared
            .assert_by_scopes
            .values()
            .map(std::vec::Vec::len)
            .sum();
        assert_eq!(prepared.assert_by_scopes.len(), n_scopes);
        assert_eq!(scoped_obligation_count, n_scopes * 3);
        std::hint::black_box(prepared);
    }
    start.elapsed().as_micros()
}

fn build_assert_by_scope_obligations(i: usize) -> Vec<crate::vc::ProofObligation> {
    vec![
        crate::vc::ProofObligation::assume(format!("scope_{i}_eq"), "x == y"),
        crate::vc::ProofObligation::assume(format!("scope_{i}_bound"), "y >= 0"),
        crate::vc::ProofObligation::assert(format!("scope_{i}_goal"), "x >= 0"),
    ]
}

/// The pre-built-expression fast path in `prepare_context` still walks the
/// cached TrustVcExpr tree once to repair function call return types from the
/// TypeEnv. That walk should stay O(E) in tree size, not regress to O(E^2).
#[test]
fn test_prepare_context_cached_expr_repair_scales_linearly() {
    let small_depth = 40;
    let large_depth = 160;
    let iterations = 200;

    let fixed_small = prepare_cached_fn_call_chain(small_depth);
    let fixed_large = prepare_cached_fn_call_chain(large_depth);
    assert_fn_call_chain_fixed(&fixed_small.obligations[0].expr, small_depth);
    assert_fn_call_chain_fixed(&fixed_large.obligations[0].expr, large_depth);

    let t_small = measure_median(
        || time_prepare_context_cached_expr(small_depth, iterations),
        3,
    );
    let t_large = measure_median(
        || time_prepare_context_cached_expr(large_depth, iterations),
        3,
    );

    if t_small < MIN_MEASURABLE_US {
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = large_depth as f64 / small_depth as f64;
    let normalized = ratio / scale;

    assert!(
        normalized < QUADRATIC_THRESHOLD / scale,
        "prepare_context cached-expr repair appears quadratic: \
         T(D={})={}us, T(D={})={}us, ratio={:.1}x, normalized={:.1}x. \
         fix_fn_call_return_types should be O(E) in cached tree depth.",
        small_depth,
        t_small,
        large_depth,
        t_large,
        ratio,
        normalized,
    );
}

fn time_prepare_context_cached_expr(depth: usize, iterations: usize) -> u128 {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_helper_function_typed(
        "helper",
        crate::ir::TrustVcType::parse_or_opaque("i32"),
        vec![],
    );

    let name = format!("cached_chain_{}", depth);
    let condition = format!("helper({}", depth);
    ctx.push_obligation(ProofObligation::assert(&name, &condition));
    let expr = build_fn_call_chain_expr(depth);

    let start = std::time::Instant::now();
    for _ in 0..iterations {
        crate::obligation_collection::cache_pre_built_expr(
            name.clone(),
            condition.clone(),
            expr.clone(),
        );
        let prepared = crate::prepared_context::prepare_context(&ctx)
            .expect("prepare_context should consume cached expression");
        std::hint::black_box(prepared);
    }
    start.elapsed().as_micros()
}

fn prepare_cached_fn_call_chain(
    depth: usize,
) -> crate::prepared_context::PreparedVerificationContext {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_helper_function_typed(
        "helper",
        crate::ir::TrustVcType::parse_or_opaque("i32"),
        vec![],
    );

    let name = format!("cached_chain_{}", depth);
    let condition = format!("helper({}", depth);
    ctx.push_obligation(ProofObligation::assert(&name, &condition));
    crate::obligation_collection::cache_pre_built_expr(
        name,
        condition,
        build_fn_call_chain_expr(depth),
    );

    crate::prepared_context::prepare_context(&ctx)
        .expect("prepare_context should consume cached expression")
}

fn build_fn_call_chain_expr(depth: usize) -> crate::ir::TrustVcExpr {
    let mut expr = crate::ir::TrustVcExpr::Var {
        name: "x".to_string(),
        ty: crate::ir::TrustVcType::Int { width: 32 },
    };

    for _ in 0..depth {
        expr = crate::ir::TrustVcExpr::FnCall {
            name: "helper".to_string(),
            args: vec![expr],
            return_ty: crate::ir::TrustVcType::Bool,
        };
    }

    expr
}

fn assert_fn_call_chain_fixed(expr: &crate::ir::TrustVcExpr, depth: usize) {
    let mut current = expr;
    for level in 0..depth {
        match current {
            crate::ir::TrustVcExpr::FnCall {
                name,
                return_ty,
                args,
            } => {
                assert_eq!(name, "helper", "unexpected function name at level {level}");
                assert_eq!(
                    *return_ty,
                    crate::ir::TrustVcType::Int { width: 32 },
                    "FnCall return type should be repaired at level {level}"
                );
                assert_eq!(args.len(), 1, "expected unary helper at level {level}");
                current = &args[0];
            }
            other => panic!("expected FnCall at level {level}, got {other:?}"),
        }
    }

    match current {
        crate::ir::TrustVcExpr::Var { name, ty } => {
            assert_eq!(name, "x");
            assert_eq!(*ty, crate::ir::TrustVcType::Int { width: 32 });
        }
        other => panic!("expected Var leaf after {depth} FnCalls, got {other:?}"),
    }
}
