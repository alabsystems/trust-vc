// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for broadcast/helper pruning.
//!
//! Split from `pruning.rs` for the 500-line limit (#2621).

use super::*;
use crate::ir::{TrustVcExpr, TrustVcType};
use crate::prepared_context::PreparedObligation;
use crate::vc::{ObligationKind, VerificationContext};

fn make_obligation(name: &str, expr: TrustVcExpr) -> PreparedObligation {
    PreparedObligation {
        name: name.to_string(),
        kind: ObligationKind::Assert,
        location: None,
        condition_origin: crate::vc::ConditionOrigin::LoweredFromCondition,
        bound_vars: None,
        trigger_patterns: None,
        prepared_triggers: None,
        solver_mode: None,
        is_opaque: false,
        is_inline: false,
        broadcast_group: None,
        condition: String::new(),
        expr,
        invariant_namespace: None,
        trigger_inference_mode: None,
        broadcast_guard: None,
        raw_broadcast_guard_count: 0,
        step_meta: None,
    }
}

fn make_broadcast(
    name: &str,
    expr: TrustVcExpr,
    triggers: Option<Vec<Vec<String>>>,
) -> PreparedObligation {
    PreparedObligation {
        name: name.to_string(),
        kind: ObligationKind::BroadcastAssume,
        location: None,
        condition_origin: crate::vc::ConditionOrigin::LoweredFromCondition,
        bound_vars: Some(vec!["x".to_string()]),
        trigger_patterns: triggers,
        prepared_triggers: None,
        solver_mode: None,
        is_opaque: false,
        is_inline: false,
        broadcast_group: None,
        condition: String::new(),
        expr,
        invariant_namespace: None,
        trigger_inference_mode: None,
        broadcast_guard: None,
        raw_broadcast_guard_count: 0,
        step_meta: None,
    }
}

fn make_broadcast_with_bound_vars(
    name: &str,
    expr: TrustVcExpr,
    triggers: Option<Vec<Vec<String>>>,
    bound_vars: Vec<&str>,
) -> PreparedObligation {
    PreparedObligation {
        name: name.to_string(),
        kind: ObligationKind::BroadcastAssume,
        location: None,
        condition_origin: crate::vc::ConditionOrigin::LoweredFromCondition,
        bound_vars: Some(bound_vars.into_iter().map(str::to_string).collect()),
        trigger_patterns: triggers,
        prepared_triggers: None,
        solver_mode: None,
        is_opaque: false,
        is_inline: false,
        broadcast_group: None,
        condition: String::new(),
        expr,
        invariant_namespace: None,
        trigger_inference_mode: None,
        broadcast_guard: None,
        raw_broadcast_guard_count: 0,
        step_meta: None,
    }
}

fn fn_call(name: &str, args: Vec<TrustVcExpr>) -> TrustVcExpr {
    TrustVcExpr::FnCall {
        name: name.to_string(),
        args,
        return_ty: TrustVcType::Int { width: 32 },
    }
}

fn var(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty: TrustVcType::Int { width: 32 },
    }
}

fn int_lit(value: i128) -> TrustVcExpr {
    TrustVcExpr::IntLit {
        value,
        ty: TrustVcType::Int { width: 32 },
    }
}

fn eq(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: crate::ir::CompareOp::Eq,
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn ge(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: crate::ir::CompareOp::Ge,
        left: Box::new(left),
        right: Box::new(right),
    }
}

fn make_slices<'a>(
    ctx: &'a PreparedVerificationContext,
    assumptions: &'a [&'a PreparedObligation],
    broadcasts: &'a [&'a PreparedObligation],
    verified_invariants: &'a [&'a PreparedObligation],
    verified_assert_by: &'a [&'a PreparedObligation],
    scoped_assumptions: &'a [&'a PreparedObligation],
) -> super::super::VerificationSlices<'a> {
    super::super::VerificationSlices::new(
        ctx,
        assumptions,
        broadcasts,
        verified_invariants,
        verified_assert_by,
        scoped_assumptions,
    )
}

fn make_ctx() -> PreparedVerificationContext {
    PreparedVerificationContext {
        obligations: Vec::new(),
        variables: Vec::new(),
        function_context: None,
        trait_decls: Vec::new(),
        trait_impl_decls: Vec::new(),
        verification_mode: crate::vc::VerificationMode::default(),
        overflow_behavior: crate::vc::OverflowBehavior::default(),
        div0_behavior: crate::vc::Div0Behavior::default(),
        bitshift_behavior: crate::vc::BitshiftBehavior::default(),
        broadcast_use_groups: HashSet::new(),
        assert_by_scopes: HashMap::new(),
        forall_bound_vars: HashMap::new(),
        loop_guards: HashMap::new(),
        loop_modified_vars: HashMap::new(),
        has_collection_context: false,
        revealed_fns: HashSet::new(),
        helper_function_contexts: Vec::new(),
        struct_types: Vec::new(),
        type_invariants: HashMap::new(),
        invariant_mask: crate::vc::InvariantMask::default(),
        tracked_params: HashSet::new(),
        rlimit_ms: None,
        demand_inline: crate::vc::DemandInlineConfig::new(),
        counterexample_var_meta: HashMap::new(),
        ..Default::default()
    }
}

#[test]
fn test_prune_plan_keeps_reachable_broadcast() {
    let assertion = make_obligation("assert_foo", fn_call("foo", vec![var("x")]));
    let broadcast_foo = make_broadcast(
        "broadcast_foo",
        TrustVcExpr::Compare {
            op: crate::ir::CompareOp::Ge,
            left: Box::new(fn_call("foo", vec![var("x")])),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Int { width: 32 },
            }),
        },
        Some(vec![vec!["foo(x)".to_string()]]),
    );
    let broadcast_bar = make_broadcast(
        "broadcast_bar",
        TrustVcExpr::Compare {
            op: crate::ir::CompareOp::Ge,
            left: Box::new(fn_call("bar", vec![var("x")])),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Int { width: 32 },
            }),
        },
        Some(vec![vec!["bar(x)".to_string()]]),
    );

    let mut ctx = make_ctx();
    ctx.obligations = vec![assertion];
    let broadcasts: Vec<&PreparedObligation> = vec![&broadcast_foo, &broadcast_bar];

    let plan = build_prune_plan(&ctx, &broadcasts);

    assert!(
        plan.is_broadcast_reachable(&broadcast_foo),
        "broadcast_foo should be reachable — assertion calls foo"
    );
    assert!(
        !plan.is_broadcast_reachable(&broadcast_bar),
        "broadcast_bar should NOT be reachable — nothing calls bar"
    );
}

#[test]
fn test_prune_plan_keeps_triggerless_broadcasts() {
    let assertion = make_obligation("assert_x", var("x"));
    let triggerless = make_broadcast(
        "triggerless",
        TrustVcExpr::Compare {
            op: crate::ir::CompareOp::Ge,
            left: Box::new(fn_call("unknown", vec![var("x")])),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Int { width: 32 },
            }),
        },
        None,
    );

    let mut ctx = make_ctx();
    ctx.obligations = vec![assertion];
    let broadcasts: Vec<&PreparedObligation> = vec![&triggerless];

    let plan = build_prune_plan(&ctx, &broadcasts);

    assert!(
        plan.is_broadcast_reachable(&triggerless),
        "triggerless broadcasts should always be kept"
    );
}

#[test]
fn test_prune_plan_transitive_reachability_through_broadcast_bodies() {
    let assertion = make_obligation("assert_foo", fn_call("foo", vec![var("x")]));
    let broadcast_foo = make_broadcast(
        "broadcast_foo",
        TrustVcExpr::Compare {
            op: crate::ir::CompareOp::Eq,
            left: Box::new(fn_call("foo", vec![var("x")])),
            right: Box::new(fn_call("bar", vec![var("x")])),
        },
        Some(vec![vec!["foo(x)".to_string()]]),
    );
    let broadcast_bar = make_broadcast(
        "broadcast_bar",
        TrustVcExpr::Compare {
            op: crate::ir::CompareOp::Ge,
            left: Box::new(fn_call("bar", vec![var("x")])),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Int { width: 32 },
            }),
        },
        Some(vec![vec!["bar(x)".to_string()]]),
    );
    let broadcast_baz = make_broadcast(
        "broadcast_baz",
        TrustVcExpr::Compare {
            op: crate::ir::CompareOp::Ge,
            left: Box::new(fn_call("baz", vec![var("x")])),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Int { width: 32 },
            }),
        },
        Some(vec![vec!["baz(x)".to_string()]]),
    );

    let mut ctx = make_ctx();
    ctx.obligations = vec![assertion];
    let broadcasts: Vec<&PreparedObligation> = vec![&broadcast_foo, &broadcast_bar, &broadcast_baz];

    let plan = build_prune_plan(&ctx, &broadcasts);

    assert!(
        plan.is_broadcast_reachable(&broadcast_foo),
        "broadcast_foo should be reachable — assertion calls foo"
    );
    assert!(
        plan.is_broadcast_reachable(&broadcast_bar),
        "broadcast_bar should be reachable — foo's broadcast body calls bar"
    );
    assert!(
        !plan.is_broadcast_reachable(&broadcast_baz),
        "broadcast_baz should NOT be reachable — nothing calls baz"
    );
}

#[test]
fn test_prune_plan_helper_reachability() {
    let assertion = make_obligation("assert_helper", fn_call("helper_a", vec![var("x")]));
    let mut ctx = make_ctx();
    ctx.obligations = vec![assertion];

    let plan = build_prune_plan(&ctx, &[]);

    assert!(
        plan.is_helper_reachable("helper_a"),
        "helper_a should be reachable — directly called by assertion"
    );
    assert!(
        !plan.is_helper_reachable("helper_b"),
        "helper_b should NOT be reachable — never referenced"
    );
}

#[test]
fn test_prune_plan_seeds_from_primary_function() {
    let mut ctx = make_ctx();
    ctx.function_context = Some(crate::vc::FunctionContext {
        name: "primary_fn".to_string(),
        params: vec![],
        return_type: TrustVcType::Bool,
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    let broadcast = make_broadcast(
        "body_axiom_primary",
        fn_call("primary_fn", vec![var("x")]),
        Some(vec![vec!["primary_fn(x)".to_string()]]),
    );

    let broadcasts: Vec<&PreparedObligation> = vec![&broadcast];
    let plan = build_prune_plan(&ctx, &broadcasts);

    assert!(
        plan.is_broadcast_reachable(&broadcast),
        "primary function's body axiom should be reachable even with no obligations"
    );
}

/// Regression: a helper referenced only by a trait impl binding is
/// reachable. Without this, register_trait_impl fails because the
/// concrete function is pruned before registration. Part of #2557 Slice 1.
#[test]
fn test_prune_plan_seeds_from_trait_impl_bindings() {
    use crate::ir::TraitImplDecl;

    let assertion = make_obligation("assert_trivial", TrustVcExpr::BoolLit(true));
    let mut ctx = make_ctx();
    ctx.obligations = vec![assertion];
    ctx.trait_impl_decls = vec![TraitImplDecl {
        inherent_shadowed_methods: Default::default(),
        impl_group: Default::default(),
        trait_name: "MyTrait".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![("get_value".to_string(), "BoolImpl__get_value".to_string())],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    }];

    let plan = build_prune_plan(&ctx, &[]);

    assert!(
        plan.is_helper_reachable("BoolImpl__get_value"),
        "impl-linked helper should be reachable via trait_impl_decls binding"
    );
}

/// Regression: opaque-type trait impls should NOT seed reachability —
/// setup_from_prepared skips them entirely. Part of #2557 Slice 1.
#[test]
fn test_prune_plan_skips_opaque_trait_impl_bindings() {
    use crate::ir::TraitImplDecl;

    let assertion = make_obligation("assert_trivial", TrustVcExpr::BoolLit(true));
    let mut ctx = make_ctx();
    ctx.obligations = vec![assertion];
    ctx.trait_impl_decls = vec![TraitImplDecl {
        inherent_shadowed_methods: Default::default(),
        impl_group: Default::default(),
        trait_name: "MyTrait".to_string(),
        concrete_type: TrustVcType::Opaque("Widget".to_string()),
        method_bindings: vec![("get_value".to_string(), "WidgetImpl__get_value".to_string())],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    }];

    let plan = build_prune_plan(&ctx, &[]);

    assert!(
        !plan.is_helper_reachable("WidgetImpl__get_value"),
        "opaque impl-linked helper should NOT be reachable — impl is skipped"
    );
}

/// Integration test: `setup_from_prepared` with pruning active skips
/// unreachable helper function contexts and broadcasts. Part of #2520.
#[test]
fn test_setup_from_prepared_prunes_unreachable_helpers_and_broadcasts() {
    use crate::encoder::AYEncoder;
    use crate::vc::FunctionContext;

    let assertion = make_obligation(
        "assert_reachable",
        fn_call("helper_reachable", vec![var("x")]),
    );

    let broadcast_reachable = make_broadcast(
        "broadcast_reachable",
        TrustVcExpr::Compare {
            op: crate::ir::CompareOp::Ge,
            left: Box::new(fn_call("helper_reachable", vec![var("x")])),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Int { width: 32 },
            }),
        },
        Some(vec![vec!["helper_reachable(x)".to_string()]]),
    );

    let broadcast_unreachable = make_broadcast(
        "broadcast_unreachable",
        TrustVcExpr::Compare {
            op: crate::ir::CompareOp::Ge,
            left: Box::new(fn_call("helper_unreachable", vec![var("x")])),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Int { width: 32 },
            }),
        },
        Some(vec![vec!["helper_unreachable(x)".to_string()]]),
    );

    let mut ctx = make_ctx();
    ctx.obligations = vec![assertion.clone()];
    ctx.variables = vec![crate::vc::VariableDecl {
        bounded_len: false,
        name: "x".to_string(),
        ty: TrustVcType::Int { width: 32 },
    }];
    ctx.helper_function_contexts = vec![
        FunctionContext {
            name: "helper_reachable".to_string(),
            params: vec![("x".to_string(), TrustVcType::Int { width: 32 })],
            return_type: TrustVcType::Int { width: 32 },
            is_recursive: false,
            mode: crate::mode::FunctionMode::Spec,
            trait_bounds: vec![],
        },
        FunctionContext {
            name: "helper_unreachable".to_string(),
            params: vec![("x".to_string(), TrustVcType::Int { width: 32 })],
            return_type: TrustVcType::Int { width: 32 },
            is_recursive: false,
            mode: crate::mode::FunctionMode::Spec,
            trait_bounds: vec![],
        },
    ];

    let assumptions: Vec<&PreparedObligation> = vec![];
    let broadcasts: Vec<&PreparedObligation> = vec![&broadcast_reachable, &broadcast_unreachable];

    let slices =
        super::super::VerificationSlices::new(&ctx, &assumptions, &broadcasts, &[], &[], &[]);
    let encoder =
        AYEncoder::setup_from_prepared(&slices, false, None).expect("setup should succeed");

    assert!(
        encoder.fn_ctx.functions.contains_key("helper_reachable"),
        "reachable helper should be registered as a ay UF"
    );
    assert!(
        !encoder.fn_ctx.functions.contains_key("helper_unreachable"),
        "unreachable helper should be pruned from ay UF registration"
    );

    assert_eq!(
        encoder.state.broadcast_count, 1,
        "only 1 of 2 broadcasts should survive pruning"
    );
}

/// Integration test: triggerless broadcasts are always kept. Part of #2520.
/// Fixed in P1-581: register `unrelated_fn` as a helper so the encoder
/// can create a UF declaration for it (the original test omitted this,
/// causing an "Undefined function" encoding error).
#[test]
fn test_setup_from_prepared_keeps_triggerless_broadcasts() {
    use crate::encoder::AYEncoder;
    use crate::vc::FunctionContext;

    let assertion = make_obligation("assert_x", var("x"));

    let triggerless = make_broadcast(
        "triggerless_lemma",
        TrustVcExpr::Compare {
            op: crate::ir::CompareOp::Ge,
            left: Box::new(fn_call("unrelated_fn", vec![var("x")])),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Int { width: 32 },
            }),
        },
        None,
    );

    let mut ctx = make_ctx();
    ctx.obligations = vec![assertion];
    ctx.variables = vec![crate::vc::VariableDecl {
        bounded_len: false,
        name: "x".to_string(),
        ty: TrustVcType::Int { width: 32 },
    }];
    // Register unrelated_fn as a helper so the encoder can create a UF
    // declaration. Triggerless broadcasts expand the reachable set to
    // include unrelated_fn, so its helper context must be present.
    ctx.helper_function_contexts = vec![FunctionContext {
        name: "unrelated_fn".to_string(),
        params: vec![("x".to_string(), TrustVcType::Int { width: 32 })],
        return_type: TrustVcType::Int { width: 32 },
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    }];

    let assumptions: Vec<&PreparedObligation> = vec![];
    let broadcasts: Vec<&PreparedObligation> = vec![&triggerless];

    let slices =
        super::super::VerificationSlices::new(&ctx, &assumptions, &broadcasts, &[], &[], &[]);
    let encoder =
        AYEncoder::setup_from_prepared(&slices, false, None).expect("setup should succeed");

    assert_eq!(
        encoder.state.broadcast_count, 1,
        "triggerless broadcasts must always be retained"
    );
}

#[test]
fn test_setup_from_prepared_replays_assert_forall_by_triggers() {
    use crate::encoder::AYEncoder;

    let mut vc = VerificationContext::new();
    vc.declare_var_typed("y", TrustVcType::Int { width: 32 });
    vc.declare_helper_function_typed(
        "f",
        TrustVcType::Bool,
        vec![("arg".to_string(), TrustVcType::Int { width: 32 })],
    );
    vc.add_assert_forall_by_typed_with_trigger_patterns(
        "forall_k",
        "k == k",
        vec![("k", TrustVcType::Int { width: 32 })],
        vec![],
        vec![vec!["f(y)".to_string()]],
    );

    let prepared =
        crate::prepared_context::prepare_context(&vc).expect("assert_forall_by should prepare");
    let assert_by = prepared
        .obligations
        .iter()
        .find(|obligation| obligation.name == "forall_k")
        .expect("prepared assert_forall_by obligation should exist");
    assert!(
        assert_by.prepared_triggers.is_some(),
        "prepare_context should lower assert_forall_by trigger metadata"
    );

    let verified_assert_by = vec![assert_by];
    let slices =
        super::super::VerificationSlices::new(&prepared, &[], &[], &[], &verified_assert_by, &[]);
    let result = AYEncoder::setup_from_prepared(&slices, false, None);
    assert!(
        result.is_err(),
        "invalid trigger f(y) must be forwarded during assert_forall_by replay, not dropped"
    );
}

/// Integration test: opaque body axioms respect the reveal gate even when
/// reachable by trigger head. Part of #2520.
#[test]
fn test_setup_from_prepared_preserves_reveal_gate() {
    use crate::encoder::AYEncoder;
    use crate::vc::FunctionContext;

    let assertion = make_obligation("assert_opaque", fn_call("opaque_fn", vec![var("x")]));

    let mut opaque_broadcast = make_broadcast(
        "__body_axiom_opaque_fn",
        TrustVcExpr::Compare {
            op: crate::ir::CompareOp::Eq,
            left: Box::new(fn_call("opaque_fn", vec![var("x")])),
            right: Box::new(TrustVcExpr::IntLit {
                value: 42,
                ty: TrustVcType::Int { width: 32 },
            }),
        },
        Some(vec![vec!["opaque_fn(x)".to_string()]]),
    );
    opaque_broadcast.is_opaque = true;

    let mut ctx = make_ctx();
    ctx.obligations = vec![assertion];
    ctx.variables = vec![crate::vc::VariableDecl {
        bounded_len: false,
        name: "x".to_string(),
        ty: TrustVcType::Int { width: 32 },
    }];
    ctx.helper_function_contexts = vec![FunctionContext {
        name: "opaque_fn".to_string(),
        params: vec![("x".to_string(), TrustVcType::Int { width: 32 })],
        return_type: TrustVcType::Int { width: 32 },
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    }];

    let assumptions: Vec<&PreparedObligation> = vec![];
    let broadcasts: Vec<&PreparedObligation> = vec![&opaque_broadcast];

    let slices =
        super::super::VerificationSlices::new(&ctx, &assumptions, &broadcasts, &[], &[], &[]);
    let encoder =
        AYEncoder::setup_from_prepared(&slices, false, None).expect("setup should succeed");

    assert_eq!(
        encoder.state.broadcast_count, 0,
        "opaque body axiom should be filtered by reveal gate, not just pruning"
    );
}

// --- Per-assertion prune plan tests (Part of #2649) ---

#[test]
fn test_per_assertion_plan_is_subset_of_global() {
    let assertion_foo = make_obligation("assert_foo", fn_call("foo", vec![var("x")]));
    let assertion_bar = make_obligation("assert_bar", fn_call("bar", vec![var("x")]));

    let broadcast_foo = make_broadcast(
        "broadcast_foo",
        fn_call("foo", vec![var("x")]),
        Some(vec![vec!["foo(x)".to_string()]]),
    );
    let broadcast_bar = make_broadcast(
        "broadcast_bar",
        fn_call("bar", vec![var("x")]),
        Some(vec![vec!["bar(x)".to_string()]]),
    );

    let mut ctx = make_ctx();
    ctx.obligations = vec![assertion_foo.clone(), assertion_bar.clone()];
    let broadcasts: Vec<&PreparedObligation> = vec![&broadcast_foo, &broadcast_bar];

    let global_plan = build_prune_plan(&ctx, &broadcasts);
    let slices = make_slices(&ctx, &[], &broadcasts, &[], &[], &[]);
    let per_foo = build_per_assertion_prune_plan(&slices, &assertion_foo);

    // Global includes both foo and bar; per-assertion for foo excludes bar.
    assert!(global_plan.reachable_functions.contains("foo"));
    assert!(global_plan.reachable_functions.contains("bar"));
    assert!(per_foo.reachable_functions.contains("foo"));
    assert!(
        !per_foo.reachable_functions.contains("bar"),
        "per-assertion plan for foo should NOT include bar"
    );
    // Per-assertion must be a subset of global.
    for f in &per_foo.reachable_functions {
        assert!(
            global_plan.reachable_functions.contains(f),
            "per-assertion function {f} not in global plan"
        );
    }
}

#[test]
fn test_per_assertion_excludes_unrelated_broadcasts() {
    let assertion_foo = make_obligation("assert_foo", fn_call("foo", vec![var("x")]));

    let broadcast_foo = make_broadcast(
        "broadcast_foo",
        fn_call("foo", vec![var("x")]),
        Some(vec![vec!["foo(x)".to_string()]]),
    );
    let broadcast_bar = make_broadcast(
        "broadcast_bar",
        fn_call("bar", vec![var("x")]),
        Some(vec![vec!["bar(x)".to_string()]]),
    );
    let broadcast_baz = make_broadcast(
        "broadcast_baz",
        fn_call("baz", vec![var("x")]),
        Some(vec![vec!["baz(x)".to_string()]]),
    );

    let ctx = make_ctx();
    let broadcasts: Vec<&PreparedObligation> = vec![&broadcast_foo, &broadcast_bar, &broadcast_baz];

    let slices = make_slices(&ctx, &[], &broadcasts, &[], &[], &[]);
    let plan = build_per_assertion_prune_plan(&slices, &assertion_foo);

    assert!(plan.is_broadcast_reachable(&broadcast_foo));
    assert!(!plan.is_broadcast_reachable(&broadcast_bar));
    assert!(!plan.is_broadcast_reachable(&broadcast_baz));
}

#[test]
fn test_per_assertion_includes_assumptions() {
    let assertion = make_obligation("assert_result", fn_call("foo", vec![var("x")]));
    let assumption = make_obligation("assume_bar", fn_call("bar", vec![var("x")]));

    let broadcast_bar = make_broadcast(
        "broadcast_bar",
        fn_call("bar", vec![var("x")]),
        Some(vec![vec!["bar(x)".to_string()]]),
    );

    let ctx = make_ctx();
    let broadcasts: Vec<&PreparedObligation> = vec![&broadcast_bar];
    let assumptions: Vec<&PreparedObligation> = vec![&assumption];

    let slices = make_slices(&ctx, &assumptions, &broadcasts, &[], &[], &[]);
    let plan = build_per_assertion_prune_plan(&slices, &assertion);

    assert!(
        plan.is_broadcast_reachable(&broadcast_bar),
        "broadcast triggered by assumption should be reachable"
    );
}

#[test]
fn test_per_assertion_transitive_through_broadcasts() {
    let assertion = make_obligation("assert_foo", fn_call("foo", vec![var("x")]));

    // foo's broadcast body calls bar; bar's broadcast body calls baz.
    let broadcast_foo = make_broadcast(
        "broadcast_foo",
        fn_call("bar", vec![var("x")]),
        Some(vec![vec!["foo(x)".to_string()]]),
    );
    let broadcast_bar = make_broadcast(
        "broadcast_bar",
        fn_call("baz", vec![var("x")]),
        Some(vec![vec!["bar(x)".to_string()]]),
    );
    let broadcast_unrelated = make_broadcast(
        "broadcast_unrelated",
        fn_call("unrelated", vec![var("x")]),
        Some(vec![vec!["unrelated(x)".to_string()]]),
    );

    let ctx = make_ctx();
    let broadcasts: Vec<&PreparedObligation> =
        vec![&broadcast_foo, &broadcast_bar, &broadcast_unrelated];

    let slices = make_slices(&ctx, &[], &broadcasts, &[], &[], &[]);
    let plan = build_per_assertion_prune_plan(&slices, &assertion);

    assert!(plan.is_broadcast_reachable(&broadcast_foo));
    assert!(plan.is_broadcast_reachable(&broadcast_bar));
    assert!(
        !plan.is_broadcast_reachable(&broadcast_unrelated),
        "unrelated broadcast should not be transitively reachable"
    );
}

// --- Slice 4: Performance regression tests (Part of #2649) ---

/// 10 broadcasts across 3 disjoint function groups. Per-assertion plan for
/// group A should include only group A broadcasts, not B or C.
#[test]
fn test_per_assertion_disjoint_function_groups() {
    // Group A: a1, a2, a3 (assertion calls a1, broadcast chains a1→a2→a3)
    let assertion_a = make_obligation("assert_a", fn_call("a1", vec![var("x")]));

    let bc_a1 = make_broadcast(
        "bc_a1",
        fn_call("a2", vec![var("x")]),
        Some(vec![vec!["a1(x)".to_string()]]),
    );
    let bc_a2 = make_broadcast(
        "bc_a2",
        fn_call("a3", vec![var("x")]),
        Some(vec![vec!["a2(x)".to_string()]]),
    );
    let bc_a3 = make_broadcast("bc_a3", var("x"), Some(vec![vec!["a3(x)".to_string()]]));

    // Group B: b1, b2, b3
    let bc_b1 = make_broadcast(
        "bc_b1",
        fn_call("b2", vec![var("x")]),
        Some(vec![vec!["b1(x)".to_string()]]),
    );
    let bc_b2 = make_broadcast(
        "bc_b2",
        fn_call("b3", vec![var("x")]),
        Some(vec![vec!["b2(x)".to_string()]]),
    );
    let bc_b3 = make_broadcast("bc_b3", var("x"), Some(vec![vec!["b3(x)".to_string()]]));

    // Group C: c1, c2, c3, c4
    let bc_c1 = make_broadcast(
        "bc_c1",
        fn_call("c2", vec![var("x")]),
        Some(vec![vec!["c1(x)".to_string()]]),
    );
    let bc_c2 = make_broadcast(
        "bc_c2",
        fn_call("c3", vec![var("x")]),
        Some(vec![vec!["c2(x)".to_string()]]),
    );
    let bc_c3 = make_broadcast(
        "bc_c3",
        fn_call("c4", vec![var("x")]),
        Some(vec![vec!["c3(x)".to_string()]]),
    );
    let bc_c4 = make_broadcast("bc_c4", var("x"), Some(vec![vec!["c4(x)".to_string()]]));

    let ctx = make_ctx();
    let all_broadcasts: Vec<&PreparedObligation> = vec![
        &bc_a1, &bc_a2, &bc_a3, &bc_b1, &bc_b2, &bc_b3, &bc_c1, &bc_c2, &bc_c3, &bc_c4,
    ];

    let slices = make_slices(&ctx, &[], &all_broadcasts, &[], &[], &[]);
    let plan_a = build_per_assertion_prune_plan(&slices, &assertion_a);

    // Group A broadcasts reachable.
    assert!(plan_a.is_broadcast_reachable(&bc_a1));
    assert!(plan_a.is_broadcast_reachable(&bc_a2));
    assert!(plan_a.is_broadcast_reachable(&bc_a3));

    // Group B and C broadcasts NOT reachable.
    assert!(!plan_a.is_broadcast_reachable(&bc_b1));
    assert!(!plan_a.is_broadcast_reachable(&bc_b2));
    assert!(!plan_a.is_broadcast_reachable(&bc_b3));
    assert!(!plan_a.is_broadcast_reachable(&bc_c1));
    assert!(!plan_a.is_broadcast_reachable(&bc_c2));
    assert!(!plan_a.is_broadcast_reachable(&bc_c3));
    assert!(!plan_a.is_broadcast_reachable(&bc_c4));

    // Per-assertion reachable set is strictly smaller than global.
    let mut global_ctx = make_ctx();
    let assertion_b = make_obligation("assert_b", fn_call("b1", vec![var("x")]));
    let assertion_c = make_obligation("assert_c", fn_call("c1", vec![var("x")]));
    global_ctx.obligations = vec![assertion_a.clone(), assertion_b, assertion_c];
    let global_plan = build_prune_plan(&global_ctx, &all_broadcasts);

    assert!(
        plan_a.reachable_functions.len() < global_plan.reachable_functions.len(),
        "per-assertion plan ({}) should be strictly smaller than global ({})",
        plan_a.reachable_functions.len(),
        global_plan.reachable_functions.len(),
    );
}

/// Collection-type scenario: Seq-only assertion should not pull in
/// Map-triggered broadcasts, simulating the common case where a function
/// has both Seq and Map assertions but individual assertions touch only one type.
#[test]
fn test_per_assertion_collection_type_isolation() {
    // Seq-related broadcasts (triggered by seq_len, seq_push, etc.)
    let bc_seq_len = make_broadcast(
        "bc_seq_len",
        fn_call("seq_push", vec![var("x")]),
        Some(vec![vec!["seq_len(x)".to_string()]]),
    );
    let bc_seq_push = make_broadcast(
        "bc_seq_push",
        var("x"),
        Some(vec![vec!["seq_push(x)".to_string()]]),
    );

    // Map-related broadcasts (triggered by map_get, map_contains_key, etc.)
    let bc_map_get = make_broadcast(
        "bc_map_get",
        fn_call("map_contains_key", vec![var("x")]),
        Some(vec![vec!["map_get(x)".to_string()]]),
    );
    let bc_map_contains = make_broadcast(
        "bc_map_contains",
        var("x"),
        Some(vec![vec!["map_contains_key(x)".to_string()]]),
    );

    let seq_assertion = make_obligation("assert_seq", fn_call("seq_len", vec![var("x")]));
    let map_assertion = make_obligation("assert_map", fn_call("map_get", vec![var("x")]));

    let ctx = make_ctx();
    let all_broadcasts: Vec<&PreparedObligation> =
        vec![&bc_seq_len, &bc_seq_push, &bc_map_get, &bc_map_contains];

    // Seq-only assertion should NOT include Map broadcasts.
    let seq_slices = make_slices(&ctx, &[], &all_broadcasts, &[], &[], &[]);
    let seq_plan = build_per_assertion_prune_plan(&seq_slices, &seq_assertion);
    assert!(seq_plan.is_broadcast_reachable(&bc_seq_len));
    assert!(seq_plan.is_broadcast_reachable(&bc_seq_push));
    assert!(
        !seq_plan.is_broadcast_reachable(&bc_map_get),
        "Seq assertion should not pull in Map broadcasts"
    );
    assert!(!seq_plan.is_broadcast_reachable(&bc_map_contains));

    // Map-only assertion should NOT include Seq broadcasts.
    let map_slices = make_slices(&ctx, &[], &all_broadcasts, &[], &[], &[]);
    let map_plan = build_per_assertion_prune_plan(&map_slices, &map_assertion);
    assert!(
        !map_plan.is_broadcast_reachable(&bc_seq_len),
        "Map assertion should not pull in Seq broadcasts"
    );
    assert!(!map_plan.is_broadcast_reachable(&bc_seq_push));
    assert!(map_plan.is_broadcast_reachable(&bc_map_get));
    assert!(map_plan.is_broadcast_reachable(&bc_map_contains));
}

/// The global plan (used by shared-BV and invariant paths) should include
/// ALL obligations' function references, not just one assertion's.
#[test]
fn test_global_plan_includes_all_obligation_functions() {
    let assertion_foo = make_obligation("assert_foo", fn_call("foo", vec![var("x")]));
    let assertion_bar = make_obligation("assert_bar", fn_call("bar", vec![var("x")]));
    let assertion_baz = make_obligation("assert_baz", fn_call("baz", vec![var("x")]));

    let bc_foo = make_broadcast("bc_foo", var("x"), Some(vec![vec!["foo(x)".to_string()]]));
    let bc_bar = make_broadcast("bc_bar", var("x"), Some(vec![vec!["bar(x)".to_string()]]));
    let bc_baz = make_broadcast("bc_baz", var("x"), Some(vec![vec!["baz(x)".to_string()]]));

    let mut ctx = make_ctx();
    ctx.obligations = vec![assertion_foo, assertion_bar, assertion_baz];
    let broadcasts: Vec<&PreparedObligation> = vec![&bc_foo, &bc_bar, &bc_baz];

    let global = build_prune_plan(&ctx, &broadcasts);

    // Global plan must include all three — this is what shared-BV relies on.
    assert!(global.is_broadcast_reachable(&bc_foo));
    assert!(global.is_broadcast_reachable(&bc_bar));
    assert!(global.is_broadcast_reachable(&bc_baz));
}

#[test]
fn test_per_assertion_current_state_slice_fixed_point_across_fact_lanes() {
    let assertion = make_obligation("assert_x", ge(var("x"), int_lit(0)));
    let assume_xy = make_obligation("assume_xy", eq(var("x"), var("y")));
    let assume_true = make_obligation("assume_true", TrustVcExpr::BoolLit(true));
    let assume_w = make_obligation("assume_w", ge(var("w"), int_lit(0)));
    let inv_yz = make_obligation("inv_yz", eq(var("y"), var("z")));
    let assert_by_zu = make_obligation("assert_by_zu", eq(var("z"), var("u")));
    let scoped_uv = make_obligation("scoped_uv", eq(var("u"), var("v")));

    let ctx = make_ctx();
    let assumptions: Vec<&PreparedObligation> = vec![&assume_xy, &assume_true, &assume_w];
    let verified_invariants: Vec<&PreparedObligation> = vec![&inv_yz];
    let verified_assert_by: Vec<&PreparedObligation> = vec![&assert_by_zu];
    let scoped_assumptions: Vec<&PreparedObligation> = vec![&scoped_uv];
    let slices = make_slices(
        &ctx,
        &assumptions,
        &[],
        &verified_invariants,
        &verified_assert_by,
        &scoped_assumptions,
    );

    let plan = build_per_assertion_prune_plan(&slices, &assertion);
    let slice = plan
        .current_state_slice()
        .expect("per-assertion plan should carry a current-state slice");

    for name in ["x", "y", "z", "u", "v"] {
        assert!(
            slice.reachable_variables.contains(name),
            "{name} should be reachable through the fixed-point slice"
        );
    }
    assert!(
        !slice.reachable_variables.contains("w"),
        "unrelated variable should stay pruned"
    );
    assert_eq!(slice.selected_regular_assumptions, vec![0, 1]);
    assert_eq!(slice.selected_verified_invariants, vec![0]);
    assert_eq!(slice.selected_verified_assert_by, vec![0]);
    assert_eq!(slice.selected_scoped_assumptions, vec![0]);
}

#[test]
fn test_per_assertion_current_state_slice_replays_facts_in_source_order() {
    let assertion = make_obligation("assert_a", ge(var("a"), int_lit(0)));
    let prerequisite = make_obligation("assume_b", ge(var("b"), int_lit(0)));
    let discovered_first = make_obligation("assume_ab", eq(var("a"), var("b")));

    let ctx = make_ctx();
    let assumptions: Vec<&PreparedObligation> = vec![&prerequisite, &discovered_first];
    let slices = make_slices(&ctx, &assumptions, &[], &[], &[], &[]);

    let plan = build_per_assertion_prune_plan(&slices, &assertion);
    let slice = plan
        .current_state_slice()
        .expect("per-assertion plan should carry a current-state slice");

    assert_eq!(
        slice.selected_regular_assumptions,
        vec![0, 1],
        "facts discovered by a later fixed-point pass must still replay in source order"
    );
}

/// A PROVEN QUANTIFIED `assert_by` whose only free root is its bound var (the
/// quantifier wrapper is reattached only at encode time, and the receiver
/// collection is an inlined pure-constructor term with no free `Var` root) must
/// still be selected for a later bare re-assert that shares its collection
/// function footprint — the free-root key alone would drop it (#2778). A
/// quantified fact over a DISJOINT footprint, and a SCALAR fact with disjoint
/// roots, must stay pruned, proving the widening is gated to related quantified
/// facts only.
#[test]
fn test_per_assertion_keeps_quantified_assert_by_via_function_footprint() {
    use crate::ir::QuantifierKind;
    use crate::vc::VariableDecl;

    // Inlined pure-constructor collection term (no free Var root), e.g. the
    // memoized `Set::new(..)` backing `pos2`.
    let collection = || fn_call("set_ctor", vec![]);
    let contains = |elem: TrustVcExpr| fn_call("contains", vec![collection(), elem]);

    // Bare re-assert obligation: `forall|i| contains(set_ctor(), i) == (i >= 0)`.
    // Free roots are EMPTY (i is bound, set_ctor takes no args), so the
    // free-root key has nothing to latch onto.
    let assertion = make_obligation(
        "reassert",
        TrustVcExpr::Quantifier {
            kind: QuantifierKind::Forall,
            bound_vars: vec![("i".to_string(), TrustVcType::Int { width: 32 })],
            body: Box::new(eq(contains(var("i")), ge(var("i"), int_lit(0)))),
            triggers: None,
            trigger_inference_mode: None,
        },
    );

    // Proven quantified fact: stored as its BARE body (i free), sharing the
    // `contains`/`set_ctor` footprint with the re-assert.
    let qfact = make_obligation("qfact", eq(contains(var("i")), ge(var("i"), int_lit(0))));
    // Proven quantified fact over a DISJOINT footprint (`len`) with a disjoint
    // free root `z` (a non-empty root, so `select_lane`'s empty-root keep does
    // not apply — isolating the footprint key).
    let qother = make_obligation("qother", ge(fn_call("len", vec![var("z")]), int_lit(0)));
    // Proven SCALAR fact (no forall_bound_vars entry) sharing `contains` but
    // with a disjoint free root `q`: the wider key must NOT pick it up.
    let sfact = make_obligation("sfact", eq(contains(var("q")), ge(var("q"), int_lit(0))));

    let mut ctx = make_ctx();
    ctx.forall_bound_vars.insert(
        "qfact".to_string(),
        vec![VariableDecl {
            bounded_len: false,
            name: "i".to_string(),
            ty: TrustVcType::Int { width: 32 },
        }],
    );
    ctx.forall_bound_vars.insert(
        "qother".to_string(),
        vec![VariableDecl {
            bounded_len: false,
            name: "i".to_string(),
            ty: TrustVcType::Int { width: 32 },
        }],
    );

    let verified_assert_by: Vec<&PreparedObligation> = vec![&qfact, &qother, &sfact];
    let slices = make_slices(&ctx, &[], &[], &[], &verified_assert_by, &[]);

    let plan = build_per_assertion_prune_plan(&slices, &assertion);
    let slice = plan
        .current_state_slice()
        .expect("per-assertion plan should carry a current-state slice");

    assert_eq!(
        slice.selected_verified_assert_by,
        vec![0],
        "only the footprint-related quantified fact (qfact) may be selected; the \
         disjoint-footprint quantified fact (qother) and the scalar fact (sfact) \
         must stay pruned"
    );
}

#[test]
fn test_setup_from_prepared_assertion_slice_skips_unreachable_variables_and_fact_lanes() {
    use crate::encoder::AYEncoder;
    use crate::vc::VariableDecl;

    let assertion = make_obligation("assert_x", ge(var("x"), int_lit(0)));
    let assume_x = make_obligation("assume_x", ge(var("x"), int_lit(0)));
    let assume_y = make_obligation("assume_y", ge(var("y"), int_lit(0)));
    let inv_z = make_obligation("inv_z", ge(var("z"), int_lit(0)));
    let assert_by_w = make_obligation("assert_by_w", ge(var("w"), int_lit(0)));
    let scoped_v = make_obligation("scoped_v", ge(var("v"), int_lit(0)));

    let mut ctx = make_ctx();
    ctx.variables = vec![
        VariableDecl {
            bounded_len: false,
            name: "x".to_string(),
            ty: TrustVcType::Int { width: 32 },
        },
        VariableDecl {
            bounded_len: false,
            name: "y".to_string(),
            ty: TrustVcType::Int { width: 32 },
        },
        VariableDecl {
            bounded_len: false,
            name: "z".to_string(),
            ty: TrustVcType::Int { width: 32 },
        },
        VariableDecl {
            bounded_len: false,
            name: "w".to_string(),
            ty: TrustVcType::Int { width: 32 },
        },
        VariableDecl {
            bounded_len: false,
            name: "v".to_string(),
            ty: TrustVcType::Int { width: 32 },
        },
        VariableDecl {
            bounded_len: false,
            name: "s".to_string(),
            ty: TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })),
        },
    ];

    let assumptions: Vec<&PreparedObligation> = vec![&assume_x, &assume_y];
    let verified_invariants: Vec<&PreparedObligation> = vec![&inv_z];
    let verified_assert_by: Vec<&PreparedObligation> = vec![&assert_by_w];
    let scoped_assumptions: Vec<&PreparedObligation> = vec![&scoped_v];
    let slices = make_slices(
        &ctx,
        &assumptions,
        &[],
        &verified_invariants,
        &verified_assert_by,
        &scoped_assumptions,
    );

    let encoder = AYEncoder::setup_from_prepared_with_extra_variables(
        &slices,
        false,
        None,
        &[],
        Some(&assertion),
    )
    .expect("setup should succeed after pruning unrelated fact lanes");

    assert!(
        encoder.variables.contains_key("x"),
        "assertion variable must stay declared"
    );
    for name in ["y", "z", "w", "v", "s"] {
        assert!(
            !encoder.variables.contains_key(name),
            "{name} should be pruned from the current-state encoder"
        );
    }
}

#[test]
fn test_per_assertion_current_state_slice_expands_reachable_broadcast_bound_vars() {
    use crate::vc::{FunctionContext, VariableDecl};

    let assertion = make_obligation("assert_foo", fn_call("foo", vec![var("x")]));
    let broadcast = make_broadcast_with_bound_vars(
        "broadcast_foo",
        eq(var("x"), var("y")),
        Some(vec![vec!["foo(x)".to_string()]]),
        vec!["y"],
    );

    let mut ctx = make_ctx();
    ctx.variables = vec![
        VariableDecl {
            bounded_len: false,
            name: "x".to_string(),
            ty: TrustVcType::Int { width: 32 },
        },
        VariableDecl {
            bounded_len: false,
            name: "y".to_string(),
            ty: TrustVcType::Int { width: 32 },
        },
    ];
    ctx.helper_function_contexts = vec![FunctionContext {
        name: "foo".to_string(),
        params: vec![("x".to_string(), TrustVcType::Int { width: 32 })],
        return_type: TrustVcType::Int { width: 32 },
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    }];

    let broadcasts: Vec<&PreparedObligation> = vec![&broadcast];
    let slices = make_slices(&ctx, &[], &broadcasts, &[], &[], &[]);
    let plan = build_per_assertion_prune_plan(&slices, &assertion);
    let slice = plan
        .current_state_slice()
        .expect("per-assertion plan should carry a current-state slice");

    assert!(
        slice.reachable_variables.contains("x"),
        "assertion root should seed the current-state slice"
    );
    assert!(
        slice.reachable_variables.contains("y"),
        "reachable broadcast bound_vars must stay declared for setup"
    );
}

#[test]
fn test_setup_from_prepared_post_loop_keeps_all_variables_and_fact_lanes() {
    use crate::encoder::AYEncoder;
    use crate::vc::VariableDecl;

    let assertion = make_obligation("assert_x", ge(var("x"), int_lit(0)));
    let assume_y = make_obligation("assume_y", eq(var("y"), int_lit(1)));
    let inv_z = make_obligation("inv_z", eq(var("z"), int_lit(2)));
    let assert_by_w = make_obligation("assert_by_w", eq(var("w"), int_lit(3)));
    let scoped_v = make_obligation("scoped_v", eq(var("v"), int_lit(4)));

    let mut ctx = make_ctx();
    ctx.variables = vec![
        VariableDecl {
            bounded_len: false,
            name: "x".to_string(),
            ty: TrustVcType::Int { width: 32 },
        },
        VariableDecl {
            bounded_len: false,
            name: "y".to_string(),
            ty: TrustVcType::Int { width: 32 },
        },
        VariableDecl {
            bounded_len: false,
            name: "z".to_string(),
            ty: TrustVcType::Int { width: 32 },
        },
        VariableDecl {
            bounded_len: false,
            name: "w".to_string(),
            ty: TrustVcType::Int { width: 32 },
        },
        VariableDecl {
            bounded_len: false,
            name: "v".to_string(),
            ty: TrustVcType::Int { width: 32 },
        },
    ];

    let assumptions: Vec<&PreparedObligation> = vec![&assume_y];
    let verified_invariants: Vec<&PreparedObligation> = vec![&inv_z];
    let verified_assert_by: Vec<&PreparedObligation> = vec![&assert_by_w];
    let scoped_assumptions: Vec<&PreparedObligation> = vec![&scoped_v];
    let slices = make_slices(
        &ctx,
        &assumptions,
        &[],
        &verified_invariants,
        &verified_assert_by,
        &scoped_assumptions,
    );
    let modified_vars = HashSet::from(["x".to_string()]);

    let encoder = AYEncoder::setup_from_prepared_with_extra_variables(
        &slices,
        false,
        Some(&modified_vars),
        &[],
        Some(&assertion),
    )
    .expect("post-loop setup should bypass current-state variable/fact slicing");

    for name in ["x", "y", "z", "w", "v"] {
        assert!(
            encoder.variables.contains_key(name),
            "{name} should stay declared in post-loop mode"
        );
        assert!(
            encoder
                .variables
                .contains_key(&format!("{}{}", name, super::super::PRE_STATE_SUFFIX)),
            "{name} should also have a declared pre-state shadow in post-loop mode"
        );
    }

    for name in [
        format!("y{}", super::super::PRE_STATE_SUFFIX),
        "z".to_string(),
        "w".to_string(),
        "v".to_string(),
    ] {
        assert!(
            encoder.state.equality_assumptions.contains_key(&name),
            "{name} equality should still be encoded when post-loop mode disables the current-state slice"
        );
    }
}
