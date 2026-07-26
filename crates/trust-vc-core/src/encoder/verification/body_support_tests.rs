// Tests for shared verification body-support helpers.
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::ir::TrustVcExpr;
use crate::prepared_context::PreparedObligation;
use crate::vc::{ConditionOrigin, ObligationKind};

fn stub_obligation(name: &str) -> PreparedObligation {
    PreparedObligation {
        name: name.to_string(),
        kind: ObligationKind::BroadcastAssume,
        location: None,
        condition_origin: ConditionOrigin::LoweredFromCondition,
        bound_vars: None,
        trigger_patterns: None,
        prepared_triggers: None,
        solver_mode: None,
        is_opaque: false,
        is_inline: false,
        broadcast_group: None,
        condition: "true".to_string(),
        expr: TrustVcExpr::BoolLit(true),
        invariant_namespace: None,
        trigger_inference_mode: None,
        broadcast_guard: None,
        raw_broadcast_guard_count: 0,
        step_meta: None,
    }
}

fn inline_body_axiom_obligation(name: &str, condition: &str) -> PreparedObligation {
    let function_name = name
        .strip_prefix(BODY_AXIOM_PREFIX)
        .expect("test helper expects a body axiom name")
        .split('_')
        .next()
        .expect("body axiom name should contain a function name");
    let mut env = crate::ir_lowering::TypeEnv::new();
    env.insert("x".to_string(), crate::ir::TrustVcType::Int { width: 32 });
    env.insert_fn(
        function_name.to_string(),
        crate::ir::TrustVcType::Int { width: 32 },
    );
    env.insert_fn_params(
        function_name.to_string(),
        vec![crate::ir::TrustVcType::Int { width: 32 }],
    );
    let parsed = crate::chained_comparisons::parse_expr_str_with_chains(condition)
        .expect("test body axiom should parse");
    let lowered =
        crate::ir_lowering::lower_syn_expr(&parsed, &env).expect("test body axiom should lower");

    PreparedObligation {
        name: name.to_string(),
        kind: ObligationKind::BroadcastAssume,
        location: None,
        condition_origin: ConditionOrigin::LoweredFromCondition,
        bound_vars: Some(vec!["x".to_string()]),
        trigger_patterns: Some(vec![vec!["foo(x)".to_string()]]),
        prepared_triggers: None,
        solver_mode: None,
        is_opaque: false,
        is_inline: true,
        broadcast_group: None,
        condition: condition.to_string(),
        expr: lowered,
        invariant_namespace: None,
        trigger_inference_mode: None,
        broadcast_guard: None,
        raw_broadcast_guard_count: 0,
        step_meta: None,
    }
}

#[test]
fn test_body_axiom_exact_match() {
    let ob = stub_obligation("__body_axiom_foo");
    assert!(is_body_axiom_for_function(&ob, "foo"));
}

#[test]
fn test_body_axiom_disambiguation_suffix() {
    let ob = stub_obligation("__body_axiom_foo_0");
    assert!(is_body_axiom_for_function(&ob, "foo"));

    let ob = stub_obligation("__body_axiom_foo_42");
    assert!(is_body_axiom_for_function(&ob, "foo"));
}

#[test]
fn test_body_axiom_module_suffix_matches_via_trigger_head() {
    let mut ob = stub_obligation("__body_axiom_foo_test_inline_spec");
    ob.trigger_patterns = Some(vec![vec!["foo(x)".to_string()]]);

    assert!(
        is_body_axiom_for_function(&ob, "foo"),
        "module-suffixed body axioms should match through trigger heads"
    );
}

/// Regression: prefix collision must NOT match (#2532).
#[test]
fn test_body_axiom_prefix_collision_rejected() {
    let ob = stub_obligation("__body_axiom_foo_bar");
    assert!(
        !is_body_axiom_for_function(&ob, "foo"),
        "foo_bar must NOT match foo — prefix collision (#2532)"
    );
}

#[test]
fn test_body_axiom_non_body_axiom_rejected() {
    let ob = stub_obligation("some_other_obligation");
    assert!(!is_body_axiom_for_function(&ob, "foo"));
}

#[test]
fn test_body_axiom_mixed_suffix_rejected() {
    let ob = stub_obligation("__body_axiom_foo_3x");
    assert!(
        !is_body_axiom_for_function(&ob, "foo"),
        "_3x is not a valid numeric disambiguation suffix"
    );
}

#[test]
fn test_extracted_inline_body_axiom_returns_function_metadata() {
    let ob = inline_body_axiom_obligation("__body_axiom_foo", "foo(x) == x + x");
    let extracted = extracted_inline_body_axiom(&ob).expect("body axiom should extract");

    assert_eq!(extracted.function_name, "foo");
    assert_eq!(extracted.param_names, vec!["x".to_string()]);
    match extracted.body {
        TrustVcExpr::Arith {
            op: crate::ir::ArithOp::Add,
            left,
            right,
            ..
        } => {
            assert!(
                matches!(*left, TrustVcExpr::Var { ref name, .. } if name == "x"),
                "left side should remain the formal parameter"
            );
            assert!(
                matches!(*right, TrustVcExpr::Var { ref name, .. } if name == "x"),
                "right side should remain the formal parameter"
            );
        }
        other => panic!("expected extracted body to be x + x, got {other:?}"),
    }
}

#[test]
fn test_extracted_inline_body_axiom_rejects_malformed_shape() {
    let ob = inline_body_axiom_obligation("__body_axiom_magic", "x + x == magic(x)");
    assert!(
        extracted_inline_body_axiom(&ob).is_none(),
        "reversed equalities must not be treated as inline-substitutable body axioms"
    );
}

// -- Demand-inline tests (Part of #2655) ----------------------------------------

/// Creates a non-inline body axiom obligation for demand-inline testing.
fn non_inline_body_axiom(name: &str, fn_names: &[&str], condition: &str) -> PreparedObligation {
    let mut env = crate::ir_lowering::TypeEnv::new();
    env.insert("x".to_string(), crate::ir::TrustVcType::Int { width: 32 });
    for fn_name in fn_names {
        env.insert_fn(
            fn_name.to_string(),
            crate::ir::TrustVcType::Int { width: 32 },
        );
        env.insert_fn_params(
            fn_name.to_string(),
            vec![crate::ir::TrustVcType::Int { width: 32 }],
        );
    }
    let parsed = crate::chained_comparisons::parse_expr_str_with_chains(condition)
        .expect("test body axiom should parse");
    let lowered =
        crate::ir_lowering::lower_syn_expr(&parsed, &env).expect("test body axiom should lower");
    PreparedObligation {
        name: name.to_string(),
        kind: ObligationKind::BroadcastAssume,
        location: None,
        condition_origin: ConditionOrigin::LoweredFromCondition,
        bound_vars: Some(vec!["x".to_string()]),
        trigger_patterns: None,
        prepared_triggers: None,
        solver_mode: None,
        is_opaque: false,
        is_inline: false, // NOT inline — eligible for demand promotion
        broadcast_group: None,
        condition: condition.to_string(),
        expr: lowered,
        invariant_namespace: None,
        trigger_inference_mode: None,
        broadcast_guard: None,
        raw_broadcast_guard_count: 0,
        step_meta: None,
    }
}

#[test]
fn test_referenced_function_names_collects_fncall_names() {
    let mut env = crate::ir_lowering::TypeEnv::new();
    env.insert("x".to_string(), crate::ir::TrustVcType::Int { width: 32 });
    env.insert_fn("foo".to_string(), crate::ir::TrustVcType::Int { width: 32 });
    env.insert_fn_params(
        "foo".to_string(),
        vec![crate::ir::TrustVcType::Int { width: 32 }],
    );
    env.insert_fn("bar".to_string(), crate::ir::TrustVcType::Int { width: 32 });
    env.insert_fn_params(
        "bar".to_string(),
        vec![crate::ir::TrustVcType::Int { width: 32 }],
    );
    let parsed = crate::chained_comparisons::parse_expr_str_with_chains("foo(x) + bar(x)")
        .expect("should parse");
    let lowered = crate::ir_lowering::lower_syn_expr(&parsed, &env).expect("should lower");

    let names = referenced_function_names(&lowered);
    assert!(names.contains("foo"), "should find foo");
    assert!(names.contains("bar"), "should find bar");
    assert_eq!(names.len(), 2);
}

#[test]
fn test_build_body_catalog_skips_opaque_and_inline() {
    let normal = non_inline_body_axiom("__body_axiom_helper", &["helper"], "helper(x) == x + x");
    let mut opaque =
        non_inline_body_axiom("__body_axiom_secret", &["secret"], "secret(x) == x + x");
    opaque.is_opaque = true;
    let mut already_inline =
        non_inline_body_axiom("__body_axiom_fast", &["fast"], "fast(x) == x + x");
    already_inline.is_inline = true;

    let broadcasts: Vec<&PreparedObligation> = vec![&normal, &opaque, &already_inline];
    let catalog = build_body_catalog(&broadcasts, None, &HashSet::new(), &HashSet::new());

    assert!(
        catalog.contains_key("helper"),
        "non-opaque, non-inline should be cataloged"
    );
    assert!(!catalog.contains_key("secret"), "opaque should be skipped");
    assert!(
        !catalog.contains_key("fast"),
        "already-inline should be skipped"
    );
}

#[test]
fn test_build_body_catalog_skips_primary_function() {
    let ob = non_inline_body_axiom("__body_axiom_myself", &["myself"], "myself(x) == x + x");
    let broadcasts: Vec<&PreparedObligation> = vec![&ob];

    let catalog = build_body_catalog(
        &broadcasts,
        Some("myself"),
        &HashSet::new(),
        &HashSet::new(),
    );
    assert!(
        catalog.is_empty(),
        "primary function should be excluded (recursion guard)"
    );
}

#[test]
fn test_select_candidates_depth_1_direct_callees() {
    let helper_ob = non_inline_body_axiom("__body_axiom_helper", &["helper"], "helper(x) == x + x");
    let broadcasts: Vec<&PreparedObligation> = vec![&helper_ob];
    let catalog = build_body_catalog(&broadcasts, None, &HashSet::new(), &HashSet::new());

    // Build an assertion that calls helper(x)
    let mut env = crate::ir_lowering::TypeEnv::new();
    env.insert("x".to_string(), crate::ir::TrustVcType::Int { width: 32 });
    env.insert_fn(
        "helper".to_string(),
        crate::ir::TrustVcType::Int { width: 32 },
    );
    env.insert_fn_params(
        "helper".to_string(),
        vec![crate::ir::TrustVcType::Int { width: 32 }],
    );
    let parsed = crate::chained_comparisons::parse_expr_str_with_chains("helper(x) > 0")
        .expect("should parse");
    let assertion_expr = crate::ir_lowering::lower_syn_expr(&parsed, &env).expect("should lower");

    let selection = select_demand_inline_candidates(&assertion_expr, &[], &catalog, 1, 4);
    assert_eq!(selection.functions, vec!["helper".to_string()]);
    assert_eq!(selection.depth_used, 1);
}

#[test]
fn test_select_candidates_respects_max_callees() {
    let a = non_inline_body_axiom("__body_axiom_a", &["a"], "a(x) == x + x");
    let b = non_inline_body_axiom("__body_axiom_b", &["b"], "b(x) == x + x");
    let c = non_inline_body_axiom("__body_axiom_c", &["c"], "c(x) == x + x");
    let broadcasts: Vec<&PreparedObligation> = vec![&a, &b, &c];
    let catalog = build_body_catalog(&broadcasts, None, &HashSet::new(), &HashSet::new());

    let mut env = crate::ir_lowering::TypeEnv::new();
    env.insert("x".to_string(), crate::ir::TrustVcType::Int { width: 32 });
    for name in ["a", "b", "c"] {
        env.insert_fn(name.to_string(), crate::ir::TrustVcType::Int { width: 32 });
        env.insert_fn_params(
            name.to_string(),
            vec![crate::ir::TrustVcType::Int { width: 32 }],
        );
    }
    let parsed = crate::chained_comparisons::parse_expr_str_with_chains("a(x) + b(x) + c(x)")
        .expect("should parse");
    let assertion_expr = crate::ir_lowering::lower_syn_expr(&parsed, &env).expect("should lower");

    let selection = select_demand_inline_candidates(&assertion_expr, &[], &catalog, 1, 2);
    assert_eq!(
        selection.functions.len(),
        2,
        "max_callees=2 should cap at 2"
    );
    assert_eq!(selection.depth_used, 1);
}

#[test]
fn test_select_candidates_depth_2_chained() {
    // g(x) == x * x (depth 1 callee)
    let g = non_inline_body_axiom("__body_axiom_g", &["g"], "g(x) == x + x");
    // f(x) calls g(x) in its body → eligible at depth 2
    let f = non_inline_body_axiom("__body_axiom_f", &["f", "g"], "f(x) == g(x) + x");
    let broadcasts: Vec<&PreparedObligation> = vec![&f, &g];
    let catalog = build_body_catalog(&broadcasts, None, &HashSet::new(), &HashSet::new());

    let mut env = crate::ir_lowering::TypeEnv::new();
    env.insert("x".to_string(), crate::ir::TrustVcType::Int { width: 32 });
    env.insert_fn("f".to_string(), crate::ir::TrustVcType::Int { width: 32 });
    env.insert_fn_params(
        "f".to_string(),
        vec![crate::ir::TrustVcType::Int { width: 32 }],
    );

    let parsed =
        crate::chained_comparisons::parse_expr_str_with_chains("f(x) > 0").expect("should parse");
    let assertion_expr = crate::ir_lowering::lower_syn_expr(&parsed, &env).expect("should lower");

    // depth=1: only f
    let d1 = select_demand_inline_candidates(&assertion_expr, &[], &catalog, 1, 4);
    assert_eq!(
        d1.functions,
        vec!["f".to_string()],
        "depth=1 should only find direct callee f"
    );
    assert_eq!(d1.depth_used, 1);

    // depth=2: f then g (found via f's body)
    let d2 = select_demand_inline_candidates(&assertion_expr, &[], &catalog, 2, 4);
    assert_eq!(d2.functions.len(), 2, "depth=2 should find f and g");
    assert!(d2.functions.contains(&"f".to_string()));
    assert!(d2.functions.contains(&"g".to_string()));
    assert_eq!(d2.depth_used, 2);
}

#[test]
fn test_select_candidates_include_supporting_query_roots_after_goal() {
    let goal_fn =
        non_inline_body_axiom("__body_axiom_goal_fn", &["goal_fn"], "goal_fn(x) == x + x");
    let assumed_fn = non_inline_body_axiom(
        "__body_axiom_assumed_fn",
        &["assumed_fn"],
        "assumed_fn(x) == x + x",
    );
    let broadcasts: Vec<&PreparedObligation> = vec![&goal_fn, &assumed_fn];
    let catalog = build_body_catalog(&broadcasts, None, &HashSet::new(), &HashSet::new());

    let mut env = crate::ir_lowering::TypeEnv::new();
    env.insert("x".to_string(), crate::ir::TrustVcType::Int { width: 32 });
    for name in ["goal_fn", "assumed_fn"] {
        env.insert_fn(name.to_string(), crate::ir::TrustVcType::Int { width: 32 });
        env.insert_fn_params(
            name.to_string(),
            vec![crate::ir::TrustVcType::Int { width: 32 }],
        );
    }
    let lower = |condition: &str| {
        let parsed = crate::chained_comparisons::parse_expr_str_with_chains(condition)
            .expect("query expression should parse");
        crate::ir_lowering::lower_syn_expr(&parsed, &env).expect("query expression should lower")
    };
    let assertion_expr = lower("goal_fn(x) > 0");
    let supporting_expr = lower("assumed_fn(x) == 2");

    let selection =
        select_demand_inline_candidates(&assertion_expr, &[&supporting_expr], &catalog, 1, 2);
    assert_eq!(
        selection.functions,
        vec!["goal_fn".to_string(), "assumed_fn".to_string()],
        "the assertion remains first, and an assumption callee is also a depth-one root"
    );
    assert_eq!(selection.depth_used, 1);

    let capped =
        select_demand_inline_candidates(&assertion_expr, &[&supporting_expr], &catalog, 1, 1);
    assert_eq!(
        capped.functions,
        vec!["goal_fn".to_string()],
        "the bounded retry must prioritize the failing assertion"
    );
}

#[test]
fn test_select_candidates_skips_opaque_and_recursive() {
    // opaque_fn body available but is_opaque prevents catalog entry
    let mut opaque = non_inline_body_axiom(
        "__body_axiom_opaque_fn",
        &["opaque_fn"],
        "opaque_fn(x) == x + x",
    );
    opaque.is_opaque = true;

    let broadcasts: Vec<&PreparedObligation> = vec![&opaque];
    let catalog = build_body_catalog(&broadcasts, None, &HashSet::new(), &HashSet::new());

    let mut env = crate::ir_lowering::TypeEnv::new();
    env.insert("x".to_string(), crate::ir::TrustVcType::Int { width: 32 });
    env.insert_fn(
        "opaque_fn".to_string(),
        crate::ir::TrustVcType::Int { width: 32 },
    );
    env.insert_fn_params(
        "opaque_fn".to_string(),
        vec![crate::ir::TrustVcType::Int { width: 32 }],
    );
    let parsed = crate::chained_comparisons::parse_expr_str_with_chains("opaque_fn(x) > 0")
        .expect("should parse");
    let assertion_expr = crate::ir_lowering::lower_syn_expr(&parsed, &env).expect("should lower");

    let candidates = select_demand_inline_candidates(&assertion_expr, &[], &catalog, 1, 4);
    assert!(
        candidates.functions.is_empty(),
        "opaque callee must not be auto-inlined"
    );
    assert_eq!(candidates.depth_used, 0);
}

#[test]
fn test_build_body_catalog_revealed_opaque_is_inlinable() {
    // Proc-macro-path shape: a revealed opaque axiom still carries
    // `is_opaque == true` (the reveal is query-level). The catalog must
    // consult the reveal set so the demand-inline retry can unfold the
    // revealed definition in BOTH directions (Verified and Counterexample).
    let mut opaque =
        non_inline_body_axiom("__body_axiom_secret", &["secret"], "secret(x) == x + x");
    opaque.is_opaque = true;
    let broadcasts: Vec<&PreparedObligation> = vec![&opaque];

    let revealed: HashSet<String> = ["secret".to_string()].into_iter().collect();
    let catalog = build_body_catalog(&broadcasts, None, &revealed, &HashSet::new());
    assert!(
        catalog.contains_key("secret"),
        "a revealed opaque body must be inlinable"
    );

    // Soundness pin: WITHOUT the reveal the same axiom must stay out — the
    // retry inlining an unrevealed opaque body would prove more than Verus.
    let catalog = build_body_catalog(&broadcasts, None, &HashSet::new(), &HashSet::new());
    assert!(
        catalog.is_empty(),
        "an unrevealed opaque body must never be inlinable"
    );
}

#[test]
fn test_build_body_catalog_hidden_fn_excluded_unless_revealed() {
    // `hide!(f)` re-opaques a non-opaque fn for the query: its body must not
    // be inlinable (the demand-inline retry would otherwise leak the hidden
    // body). Reveal wins over hide.
    let visible = non_inline_body_axiom("__body_axiom_helper", &["helper"], "helper(x) == x + x");
    let broadcasts: Vec<&PreparedObligation> = vec![&visible];

    let hidden: HashSet<String> = ["helper".to_string()].into_iter().collect();
    let catalog = build_body_catalog(&broadcasts, None, &HashSet::new(), &hidden);
    assert!(
        catalog.is_empty(),
        "a hidden (unrevealed) body must not be inlinable"
    );

    let revealed: HashSet<String> = ["helper".to_string()].into_iter().collect();
    let catalog = build_body_catalog(&broadcasts, None, &revealed, &hidden);
    assert!(
        catalog.contains_key("helper"),
        "reveal wins over hide (upstream hide(f)+reveal(f) nets to revealed)"
    );
}

#[test]
fn test_fn_name_named_in_matches_bare_and_qualified_leaf() {
    let set: HashSet<String> = ["mul".to_string()].into_iter().collect();
    assert!(fn_name_named_in("mul", &set));
    assert!(fn_name_named_in("dep::module::mul", &set));
    assert!(!fn_name_named_in("mulx", &set));
    assert!(!fn_name_named_in("dep::module::mulx", &set));
}
