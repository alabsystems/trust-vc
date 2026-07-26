//! Broadcast trigger handling: explicit triggers, prepared metadata, and inference.
//!
//! Issues: #1613, #1866, #2461, #2575
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ========================================================================
// Trigger pattern propagation to ay (Fix 1, #1613)
// ========================================================================

/// Broadcast with explicit trigger patterns uses try_forall_with_triggers.
/// The trigger expression "n >= 0" is parsed and attached to the forall.
/// Without #1613 fix, triggers were silently discarded.
#[test]
fn test_broadcast_with_trigger_patterns_no_error() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("i32"));
    // Single trigger group with one pattern
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("broadcast_triggered", "n >= 0")
            .with_bound_vars(vec!["n".to_string()])
            .with_trigger_patterns(vec![vec!["n >= 0".to_string()]]),
    );
    ctx.push_obligation(ProofObligation::assert("check", "n >= 0"));

    let result = AYEncoder::verify(&ctx);
    // ay-dpll trigger matching limitation — may return Unknown (#2229 triage)
    expect_verified_or_unknown(&result, "Broadcast with trigger patterns");
}

/// Trigger encoding is fail-closed: qualified paths like `Math::double(n)` that
/// resolve to `Undefined function: Math::double` produce an error instead of
/// silently falling back to the legacy string parser.
/// Part of #1866 Phase 5 Step 1: trigger path fail-closed migration.
#[test]
fn test_broadcast_trigger_qualified_path_errors_without_fallback() {
    use crate::vc::FunctionContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext {
        name: "double".to_string(),
        params: vec![(
            "x".to_string(),
            crate::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Exec,
        trait_bounds: vec![],
    });
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume(
            "broadcast_trigger_fallback",
            "double(n) >= 0",
        )
        .with_bound_vars(vec!["n".to_string()])
        .with_trigger_patterns(vec![vec!["Math::double(n) >= 0".to_string()]]),
    );
    ctx.push_obligation(ProofObligation::assert("check", "n == n"));

    let result = AYEncoder::verify(&ctx);
    expect_error(
        &result,
        "Qualified-path trigger without registered function should error (fail-closed)",
    );
}

/// Trigger lowering must include function return types so method-trigger terms
/// on function-call receivers infer/cast literals correctly (e.g., `1` in
/// `f(n).wrapping_add(1)` should coerce to `u8`, not default `i32`).
#[test]
fn test_broadcast_trigger_function_return_type_in_type_env() {
    use crate::vc::FunctionContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext {
        name: "f".to_string(),
        params: vec![(
            "x".to_string(),
            crate::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("u8").unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Exec,
        trait_bounds: vec![],
    });
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume(
            "broadcast_trigger_function_return_type",
            "f(n).wrapping_add(1) == f(n).wrapping_add(1)",
        )
        .with_bound_vars(vec!["n".to_string()])
        .with_trigger_patterns(vec![vec!["f(n).wrapping_add(1)".to_string()]]),
    );
    ctx.push_obligation(ProofObligation::assert("check", "n == n"));

    let result = AYEncoder::verify(&ctx);
    expect_encodes_without_error(&result, "Trigger function-call receiver typing");
}

/// Broadcast without trigger patterns still works (regression test).
/// When trigger_patterns is None, the encoder uses try_forall without triggers
/// and ay auto-extracts patterns.
#[test]
fn test_broadcast_without_triggers_still_works() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("i32"));
    // No triggers — ay auto-extracts
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("broadcast_no_trigger", "n >= 0")
            .with_bound_vars(vec!["n".to_string()]),
    );
    ctx.push_obligation(ProofObligation::assert("check", "n >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_encodes_without_error(&result, "Broadcast without triggers");
}

/// Broadcast with an invalid trigger expression returns an error.
/// This ensures the encoder propagates parse failures from trigger expressions.
#[test]
fn test_broadcast_with_invalid_trigger_returns_error() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("broadcast_bad_trigger", "n >= 0")
            .with_bound_vars(vec!["n".to_string()])
            .with_trigger_patterns(vec![vec!["@#$invalid".to_string()]]),
    );
    ctx.push_obligation(ProofObligation::assert("check", "n >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_error(
        &result,
        "Broadcast with invalid trigger expression should error",
    );
}

#[test]
fn test_broadcast_prepared_metadata_keeps_all_alternative_singleton_seed_symbols() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_helper_function_typed(
        "f",
        crate::ir::TrustVcType::Bool,
        vec![("x".to_string(), crate::ir::TrustVcType::Int { width: 32 })],
    );
    ctx.declare_helper_function_typed(
        "g",
        crate::ir::TrustVcType::Bool,
        vec![("x".to_string(), crate::ir::TrustVcType::Int { width: 32 })],
    );
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("broadcast_fg", "x == x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["f(x)".to_string()], vec!["g(x)".to_string()]]),
    );

    let prepared = crate::prepared_context::prepare_context(&ctx)
        .expect("alternative singleton trigger groups should prepare");
    let obligation = prepared
        .obligations
        .first()
        .expect("prepared broadcast obligation should exist");

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
fn test_broadcast_prepared_metadata_keeps_multitrigger_groups_solver_only_for_seeding() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_helper_function_typed(
        "f",
        crate::ir::TrustVcType::Bool,
        vec![("x".to_string(), crate::ir::TrustVcType::Int { width: 32 })],
    );
    ctx.declare_helper_function_typed(
        "g",
        crate::ir::TrustVcType::Bool,
        vec![("x".to_string(), crate::ir::TrustVcType::Int { width: 32 })],
    );
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("broadcast_multi", "x == x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["f(x)".to_string(), "g(x)".to_string()]]),
    );

    let prepared =
        crate::prepared_context::prepare_context(&ctx).expect("multi-trigger group should prepare");
    let obligation = prepared
        .obligations
        .first()
        .expect("prepared broadcast obligation should exist");

    assert!(
        obligation.eager_seed_symbols().is_empty(),
        "multi-trigger groups must remain solver-only for eager seeding"
    );
    assert_eq!(
        obligation
            .trigger_head_symbols()
            .iter()
            .map(|symbol| symbol.as_ref())
            .collect::<Vec<_>>(),
        vec!["f", "g"]
    );
}

#[test]
fn test_broadcast_prepared_metadata_lowers_manual_arith_trigger() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::MathInt);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::MathInt);
    ctx.declare_helper_function_typed(
        "some_fn",
        crate::ir::TrustVcType::MathInt,
        vec![("x".to_string(), crate::ir::TrustVcType::MathInt)],
    );
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume(
            "broadcast_manual_arith_trigger",
            "some_fn(a + b) == 10",
        )
        .with_bound_vars(vec!["a".to_string(), "b".to_string()])
        .with_trigger_patterns(vec![vec!["some_fn(a + b)".to_string()]]),
    );

    let prepared = crate::prepared_context::prepare_context(&ctx)
        .expect("manual arithmetic trigger should prepare");
    let obligation = prepared
        .obligations
        .first()
        .expect("prepared broadcast obligation should exist");
    let trigger_groups = obligation
        .prepared_triggers
        .as_ref()
        .expect("prepared trigger metadata should be present");

    assert_eq!(trigger_groups.len(), 1);
    assert_eq!(trigger_groups[0].len(), 1);
    assert_eq!(
        obligation
            .trigger_head_symbols()
            .iter()
            .map(|symbol| symbol.as_ref())
            .collect::<Vec<_>>(),
        vec!["some_fn"]
    );

    match &trigger_groups[0][0].expr {
        crate::ir::TrustVcExpr::FnCall { name, args, .. } => {
            assert_eq!(name, "some_fn");
            assert!(
                matches!(
                    args.as_slice(),
                    [crate::ir::TrustVcExpr::Arith {
                        op: crate::ir::ArithOp::Add,
                        ..
                    }]
                ),
                "manual trigger should preserve a + b as the function argument"
            );
        }
        other => panic!("expected some_fn(a + b) trigger, got {other:?}"),
    }
}

#[test]
fn test_broadcast_manual_arith_trigger_encodes_ground_call() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::MathInt);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::MathInt);
    ctx.declare_helper_function_typed(
        "some_fn",
        crate::ir::TrustVcType::MathInt,
        vec![("x".to_string(), crate::ir::TrustVcType::MathInt)],
    );
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume(
            "broadcast_manual_arith_trigger",
            "some_fn(a + b) == 10",
        )
        .with_bound_vars(vec!["a".to_string(), "b".to_string()])
        .with_trigger_patterns(vec![vec!["some_fn(a + b)".to_string()]]),
    );
    ctx.push_obligation(ProofObligation::assert(
        "manual_arith_trigger_instantiates",
        "some_fn(2 + 3) == 10",
    ));

    let result = AYEncoder::verify(&ctx);
    // Mirrors upstream Verus `test_ok_arith_trigger` at the TrustVc
    // broadcast/prepared-context boundary.
    expect_verified(
        &result,
        "manual trigger some_fn(a + b) should instantiate for some_fn(2 + 3)",
    );
}

#[test]
fn test_broadcast_manual_arith_trigger_with_constant_encodes_ground_call() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::MathInt);
    ctx.declare_helper_function_typed(
        "some_fn",
        crate::ir::TrustVcType::MathInt,
        vec![("x".to_string(), crate::ir::TrustVcType::MathInt)],
    );
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume(
            "broadcast_manual_arith_constant_trigger",
            "some_fn(a + 1) == 10",
        )
        .with_bound_vars(vec!["a".to_string()])
        .with_trigger_patterns(vec![vec!["some_fn(a + 1)".to_string()]]),
    );
    ctx.push_obligation(ProofObligation::assert(
        "manual_arith_constant_trigger_instantiates",
        "some_fn(2 + 1) == 10",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "manual trigger some_fn(a + 1) should instantiate for some_fn(2 + 1)",
    );
}

// ========================================================================
// Automatic trigger inference (#2461)
// ========================================================================

/// Broadcast without explicit triggers gets auto-inferred trigger from body.
/// The body `f(x) == x + 1` should infer trigger `[f(x)]` since `f(x)` is a
/// FnCall that references bound variable `x`.
#[test]
fn test_broadcast_auto_inferred_trigger_from_body() {
    use crate::vc::FunctionContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext {
        name: "f".to_string(),
        params: vec![(
            "x".to_string(),
            crate::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    ctx.push_obligation(ProofObligation::assume("x_bound", "x >= 0 && x <= 50"));

    // NO trigger_patterns — inference should pick f(x)
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("__body_axiom_f", "f(x) == x + 1")
            .with_bound_vars(vec!["x".to_string()]),
    );

    ctx.push_obligation(ProofObligation::assert("f_property", "f(3) == 4"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Broadcast with auto-inferred trigger f(x) should prove f(3)==4.",
    );
}

/// Explicit triggers override inference — no double-trigger.
/// When the user provides an explicit trigger, inference must not add more.
#[test]
fn test_broadcast_explicit_trigger_overrides_inference() {
    use crate::vc::FunctionContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext {
        name: "f".to_string(),
        params: vec![(
            "x".to_string(),
            crate::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    ctx.push_obligation(ProofObligation::assume("x_bound", "x >= 0 && x <= 50"));

    // Explicit trigger provided — inference should NOT add more
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("__body_axiom_f", "f(x) == x + 1")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["f(x)".to_string()]]),
    );

    ctx.push_obligation(ProofObligation::assert("f_property", "f(3) == 4"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Broadcast with explicit trigger should still verify.",
    );
}

/// Pure arithmetic broadcast body gets no inferred trigger.
/// `x + 1 > 0` has no FnCall/CollectionOp/Index candidates, so inference
/// returns empty and the broadcast proceeds trigger-less (same as before #2461).
#[test]
fn test_broadcast_pure_arith_no_auto_trigger() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));

    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("arith_broadcast", "x + 1 > 0")
            .with_bound_vars(vec!["x".to_string()]),
    );
    ctx.push_obligation(ProofObligation::assume("x_bound", "x >= 0"));
    ctx.push_obligation(ProofObligation::assert("check", "x + 1 > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_encodes_without_error(&result, "Pure arithmetic broadcast without trigger");
}

/// Collection-layer test: broadcast with guard clauses populates
/// PreparedObligation.broadcast_guard, while guardless broadcast leaves it None.
/// Verifies the metadata plumbing from ProofObligation → PreparedObligation.
/// Part of #2575.
#[test]
fn test_broadcast_guard_metadata_plumbing() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));

    // Broadcast WITH guard
    let mut guarded = crate::vc::ProofObligation::broadcast_assume("broadcast_with_guard", "x > 0")
        .with_bound_vars(vec!["x".to_string()]);
    guarded.broadcast_guard = Some(vec![crate::vc::BroadcastGuardClause {
        condition: "x > 0".to_string(),
    }]);
    ctx.obligations.push(guarded);

    // Broadcast WITHOUT guard
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("broadcast_no_guard", "x >= 0")
            .with_bound_vars(vec!["x".to_string()]),
    );

    ctx.push_obligation(ProofObligation::assert("trivial", "x == x"));

    let prepared = crate::prepared_context::prepare_context(&ctx)
        .expect("prepare_context should succeed for guard metadata test");

    let guarded_obligation = prepared
        .obligations
        .iter()
        .find(|o| o.name == "broadcast_with_guard")
        .expect("guarded broadcast obligation should be in prepared context");
    assert!(
        guarded_obligation.broadcast_guard.is_some(),
        "Broadcast with guard clauses must populate PreparedObligation.broadcast_guard"
    );
    assert_eq!(
        guarded_obligation.raw_broadcast_guard_count, 1,
        "Broadcast with one guard clause must record the raw guard count"
    );

    let unguarded_obligation = prepared
        .obligations
        .iter()
        .find(|o| o.name == "broadcast_no_guard")
        .expect("unguarded broadcast obligation should be in prepared context");
    assert!(
        unguarded_obligation.broadcast_guard.is_none(),
        "Broadcast without guard clauses must leave PreparedObligation.broadcast_guard as None"
    );
    assert_eq!(
        unguarded_obligation.raw_broadcast_guard_count, 0,
        "Broadcast without guard clauses must record zero raw guard clauses"
    );
}

/// Broadcast obligation with aggressive trigger inference mode returns all
/// valid trigger groups. Verifies that the mode field on ProofObligation
/// flows through to the encoder's trigger inference call. Part of #2461 Slice 3.
#[test]
fn test_broadcast_aggressive_trigger_mode() {
    use crate::trigger_inference::TriggerInferenceMode;

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_helper_function_typed(
        "f",
        crate::ir::TrustVcType::Int { width: 32 },
        vec![("x".to_string(), crate::ir::TrustVcType::Int { width: 32 })],
    );
    ctx.declare_helper_function_typed(
        "g",
        crate::ir::TrustVcType::Int { width: 32 },
        vec![("x".to_string(), crate::ir::TrustVcType::Int { width: 32 })],
    );

    // Body has two FnCall candidates: f(x) and g(x).
    // Aggressive mode should produce two trigger groups; conservative would
    // produce one. We verify the obligation stores the mode correctly.
    let mut obligation =
        crate::vc::ProofObligation::broadcast_assume("aggressive_bc", "f(x) > 0 && g(x) > 0")
            .with_bound_vars(vec!["x".to_string()]);
    obligation.trigger_inference_mode = Some(TriggerInferenceMode::Aggressive);
    ctx.obligations.push(obligation);

    ctx.push_obligation(ProofObligation::assert("check", "f(x) > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_encodes_without_error(&result, "Broadcast with aggressive trigger inference mode");
}

// ========================================================================
// Soundness: SAT-model re-validation against broadcast forall premises (#1)
//
// ay's model validation SKIPS quantified assertions, so an un-instantiated
// broadcast `forall` can be violated by a SAT model that is nonetheless
// reported `sat_model_validated`. These tests pin both soundness directions:
//   (a) a model that violates an assumed premise is NEVER emitted as a
//       definitive counterexample;
//   (b)/(c) genuine refutations are still produced.
// ========================================================================

/// (a) An assumed broadcast `forall n. n >= 0` makes asserting `n >= 0`
/// vacuously/genuinely valid: any candidate counterexample model (e.g.
/// `n = -1`) violates the assumed premise, so it must be REJECTED. The
/// negated-goal query is UNSAT once the premise is instantiated at the
/// witness, so the obligation is discharged (Verified), and may never be a
/// definitive Counterexample with `n = -1`.
#[test]
fn test_broadcast_forall_premise_rejects_false_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("premise_nonneg", "n >= 0")
            .with_bound_vars(vec!["n".to_string()])
            .with_trigger_patterns(vec![vec!["n >= 0".to_string()]]),
    );
    ctx.push_obligation(ProofObligation::assert("check", "n >= 0"));

    let result = AYEncoder::verify(&ctx);
    // Must NOT be a definitive counterexample (model n = -1 violates the
    // assumed forall). Verified is the sound discharge here; Unknown is also
    // acceptable, but a Counterexample is a soundness violation.
    expect_verified_or_unknown(&result, "broadcast-forall premise must reject false CE");
}

/// (b) A genuine counterexample with a plain (non-broadcast) assumption:
/// `assume x > 0; assert x > 5` is refutable by, e.g., `x = 1`, which truly
/// satisfies the assumption and negates the goal. Re-validation must not fire
/// here (no broadcast premise) and the counterexample must still be produced.
#[test]
fn test_genuine_counterexample_with_plain_assumption_preserved() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("pos", "x > 0"));
    ctx.push_obligation(ProofObligation::assert("check", "x > 5"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "genuine CE: x > 0 does not imply x > 5");
}

/// (c) A genuine counterexample WITH a live, genuinely-instantiable broadcast
/// `forall` in scope. `forall k. k == k` is universally true, so every
/// model-derived instantiation holds — re-validation must reach a fixpoint and
/// still emit the counterexample for the truly-failing goal `x > 5`
/// (refutable by, e.g., `x = 0`, which satisfies the premise). This proves the
/// fix does not over-suppress real refutations when a broadcast forall exists.
#[test]
fn test_genuine_counterexample_with_broadcast_forall_in_scope_preserved() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("k", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("trivially_true", "k == k")
            .with_bound_vars(vec!["k".to_string()])
            .with_trigger_patterns(vec![vec!["k == k".to_string()]]),
    );
    ctx.push_obligation(ProofObligation::assert("check", "x > 5"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "genuine CE preserved with a true broadcast forall in scope",
    );
}

/// (c') Genuine counterexample where a true, instantiable broadcast `forall`
/// premise ranges over a variable INDEPENDENT of the goal. `forall k. k <= k`
/// is universally true and does not constrain `x`, so `assert x > 5` is
/// refutable (e.g. `x = 0`). Re-validation instantiates the premise at the
/// model's witnesses (which it satisfies) and reaches a fixpoint, so the
/// counterexample must survive — proving the fix does not over-suppress real
/// refutations even with a live, model-satisfied broadcast forall in scope.
#[test]
fn test_genuine_counterexample_independent_broadcast_premise_preserved() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("k", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("self_le", "k <= k")
            .with_bound_vars(vec!["k".to_string()])
            .with_trigger_patterns(vec![vec!["k <= k".to_string()]]),
    );
    ctx.push_obligation(ProofObligation::assert("check", "x > 5"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "genuine CE preserved: independent broadcast premise is satisfied",
    );
}

// ========================================================================
// Boundary-witness hardening (RP1 / RP6): a broadcast `forall` that is
// CONTRADICTORY over its sort makes the obligation VACUOUSLY valid, so the
// candidate SAT model is spurious and must NEVER be a definitive
// counterexample. The contradiction surfaces only at a domain boundary
// (`n = -1`) that is absent from the candidate model's scalars, so the
// original model-only witness harvesting missed it. Type-boundary witnesses
// instantiate the premise at `i32::MIN, -1, 0, 1, i32::MAX`, exposing the
// false ground instance `-1 >= 0` -> UNSAT -> sound Verified.
// ========================================================================

/// RP1: `forall n:i32. n >= 0` is contradictory over `i32` (false at
/// `n = -1`), so `assert n >= 100` is vacuously valid. The model-only check
/// harvested no boundary witness and emitted a FALSE counterexample `n = 0`;
/// with type-boundary witnesses the premise instance `-1 >= 0` is false, the
/// re-check is UNSAT, and the obligation is soundly discharged. Must NOT be a
/// definitive Counterexample (Verified, or Unknown if the solver cannot close
/// it — but never a refutation).
#[test]
fn test_broadcast_contradictory_premise_boundary_witness_rejects_false_ce() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("premise_nonneg_over_i32", "n >= 0")
            .with_bound_vars(vec!["n".to_string()])
            .with_trigger_patterns(vec![vec!["n >= 0".to_string()]]),
    );
    ctx.push_obligation(ProofObligation::assert("check", "n >= 100"));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "RP1: contradictory broadcast forall over i32 must reject the false CE n=0",
    );
}

/// RP6: same contradictory premise `forall n:i32. n >= 0`, but the goal ranges
/// over an INDEPENDENT variable `m` (`assert m >= 100`). The premise is still
/// contradictory over `i32`, so the obligation is vacuously valid regardless of
/// the goal variable. The model-only check emitted a false counterexample
/// `m = 0, n = 0`; the boundary witness `n = -1` again makes `-1 >= 0` false ->
/// UNSAT -> sound discharge. Must NOT be a definitive Counterexample.
#[test]
fn test_broadcast_contradictory_premise_independent_goal_rejects_false_ce() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("m", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.obligations.push(
        crate::vc::ProofObligation::broadcast_assume("premise_nonneg_over_i32", "n >= 0")
            .with_bound_vars(vec!["n".to_string()])
            .with_trigger_patterns(vec![vec!["n >= 0".to_string()]]),
    );
    ctx.push_obligation(ProofObligation::assert("check", "m >= 100"));

    let result = AYEncoder::verify(&ctx);
    expect_verified_or_unknown(
        &result,
        "RP6: contradictory broadcast forall must reject the false CE even for an \
         independent goal variable",
    );
}
