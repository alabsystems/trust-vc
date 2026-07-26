//! Inductive step broadcast assumption tests (#2244).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Verifies that the inductive step (both havoc-all and frame-condition modes)
//! includes broadcast assumptions (spec function body axioms, broadcast lemmas).
//! Without these, invariants depending on spec axioms get spurious
//! counterexamples.
//!
//! Split from inductive_step_coverage.rs due to 500-line file limit.
//! Fixes #2244.

use super::*;
use crate::vc::{FunctionContext, ProofObligation};

/// Invariant that depends on a spec function body axiom.
///
/// The invariant `double(n) == n + n` requires the body axiom
/// `double(x) == x + x` to verify in the inductive step (havoc-all mode).
/// Without broadcast assumptions in the inductive step, the solver treats
/// `double` as uninterpreted and cannot prove the equality.
///
/// Regression test for #2244: inductive step excluded broadcast assumptions.
#[test]
fn test_inductive_havoc_all_with_broadcast_assumption() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32")); // bound variable for body axiom

    ctx.set_function_context(FunctionContext {
        name: "double".to_string(),
        params: vec![(
            "x".to_string(),
            crate::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    // Body axiom: double(x) == x + x
    ctx.obligations.push(
        ProofObligation::broadcast_assume("__body_axiom_double", "double(x) == x + x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["double(x)".to_string()]]),
    );

    ctx.push_obligation(ProofObligation::assume("init", "n == 0"));
    // Invariant uses spec function — needs body axiom in inductive step
    ctx.obligations.push(ProofObligation::loop_invariant(
        "double_def",
        "double(n) == n + n",
    ));
    ctx.push_obligation(ProofObligation::assert("post", "double(n) == n + n"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Invariant depending on body axiom should pass inductive step (#2244)",
    );
}

/// Frame-condition inductive step with broadcast assumption.
///
/// Same as above but uses frame-condition mode (modified_vars set).
/// The invariant `double(limit) == limit + limit` should pass because:
/// - limit is unmodified (frame condition: limit == limit__pre)
/// - body axiom available: double(x) == x + x
///
/// Regression test for #2244.
#[test]
fn test_inductive_frame_condition_with_broadcast_assumption() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("i", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("limit", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32")); // bound variable for body axiom

    ctx.set_function_context(FunctionContext {
        name: "double".to_string(),
        params: vec![(
            "x".to_string(),
            crate::ir::TrustVcType::from_str("i32").unwrap(),
        )],
        return_type: crate::ir::TrustVcType::from_str("i32").unwrap(),
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    ctx.obligations.push(
        ProofObligation::broadcast_assume("__body_axiom_double", "double(x) == x + x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["double(x)".to_string()]]),
    );

    ctx.push_obligation(ProofObligation::assume("init_i", "i == 0"));
    ctx.push_obligation(ProofObligation::assume("init_limit", "limit == 5"));
    ctx.obligations.push(ProofObligation::loop_invariant(
        "double_limit",
        "double(limit) == limit + limit",
    ));
    // Only i is modified — limit preserved by frame condition
    ctx.set_loop_modified_vars("double_limit", vec!["i".to_string()]);
    ctx.push_obligation(ProofObligation::assert(
        "post",
        "double(limit) == limit + limit",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Frame-condition invariant with body axiom should verify (#2244)",
    );
}

/// Negative test: without body axiom, invariant on uninterpreted function fails.
///
/// Paired with test_inductive_havoc_all_with_broadcast_assumption to confirm
/// that the broadcast assumption is actually needed (discriminating test).
#[test]
fn test_inductive_step_without_broadcast_fails() {
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
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });

    // NO body axiom — double is uninterpreted
    ctx.push_obligation(ProofObligation::assume("init", "n == 0"));
    ctx.obligations.push(ProofObligation::loop_invariant(
        "double_def",
        "double(n) == n + n",
    ));
    ctx.push_obligation(ProofObligation::assert("post", "double(n) == n + n"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "Without body axiom, double(n) == n + n");
}

// ============================================================
// Collection frame condition negative tests
// (Companion tests for positive tests in inductive_step_coverage.rs)
// ============================================================

/// Negative: modified Map domain is NOT preserved by frame condition.
///
/// Companion to `test_map_domain_frame_condition` in inductive_step_coverage.rs.
/// When `m` IS in modified_vars, neither array content nor domain gets a frame
/// condition. The solver can set post-state dom to any value, so
/// `m.contains_key(1)` in the invariant should fail.
///
/// Part of #2243.
#[test]
fn test_modified_map_domain_not_preserved() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, i32>"),
    );
    ctx.declare_var_typed("i", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("inserted", "m.contains_key(1)"));
    ctx.push_obligation(ProofObligation::assume("init_i", "i == 0"));

    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "key_present",
            "m.contains_key(1)",
        ));
    // m IS modified — no frame condition on domain or content
    ctx.set_loop_modified_vars("key_present", vec!["m".to_string(), "i".to_string()]);
    ctx.push_obligation(ProofObligation::assert("post", "m.contains_key(1)"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "Modified Map should NOT have frame condition on domain",
    );
}

// ============================================================
// Inductive step overflow checking (#2246)
// ============================================================

/// Invariant with overflow-prone arithmetic: havoc-all mode.
///
/// The invariant `a + b <= 100` contains `a + b` which can overflow in BV64
/// arithmetic when a, b are near u64::MAX. In havoc-all mode all variables
/// are unconstrained, so the overflow check should fire.
///
/// Before #2246: inductive step skipped overflow checks entirely.
#[test]
fn test_inductive_step_havoc_all_overflow_detected() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("u64"));

    ctx.push_obligation(ProofObligation::assume("init", "a == 0"));
    ctx.obligations
        .push(ProofObligation::loop_invariant("sum_bound", "a + b <= 100"));
    ctx.push_obligation(ProofObligation::assert("post", "a + b <= 100"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(&result, "Inductive step overflow in `a + b`");
}

/// Invariant with no overflow: frame-condition mode with unmodified variable.
///
/// The invariant `b <= 100` has no arithmetic that can overflow.
/// In frame-condition mode with only `a` modified, `b == b__pre` and
/// the pre-state invariant `b__pre <= 100` prove `b <= 100`. Overflow
/// checks are enabled but should not interfere.
#[test]
fn test_inductive_step_frame_no_overflow_safe_expr() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("u64"));

    ctx.push_obligation(ProofObligation::assume("init", "b <= 100"));
    ctx.obligations
        .push(ProofObligation::loop_invariant("b_bound", "b <= 100"));
    ctx.set_loop_modified_vars("b_bound", vec!["a".to_string()]);
    ctx.push_obligation(ProofObligation::assert("post", "b <= 100"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Safe invariant should still verify with overflow checks (#2246)",
    );
}

/// Invariant with overflow-prone arithmetic: frame-condition mode.
///
/// Same as havoc-all overflow test but with modified_vars set to trigger
/// frame-condition mode. The overflow in `a + b` should still be detected.
#[test]
fn test_inductive_step_frame_condition_overflow_detected() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("u64"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("u64"));

    ctx.push_obligation(ProofObligation::assume("init", "a == 0"));
    ctx.obligations
        .push(ProofObligation::loop_invariant("sum_bound", "a + b <= 100"));
    ctx.set_loop_modified_vars("sum_bound", vec!["a".to_string()]);
    ctx.push_obligation(ProofObligation::assert("post", "a + b <= 100"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Frame-condition inductive step overflow in `a + b`",
    );
}

// ============================================================
// Collection-typed broadcast axioms in inductive step
// ============================================================

/// Inductive step with a broadcast assumption that references Seq operations.
///
/// The invariant `s.len() >= 1` depends on a broadcast axiom that reasons
/// about Seq. This exercises the collection-typed broadcast path in the
/// inductive step encoder, which involves array theory sort matching,
/// Seq length axiom injection, and ground pool interaction.
///
/// All prior broadcast tests used pure integer axioms (double(x) == x + x).
/// This test closes the collection-typed broadcast gap in inductive step
/// coverage.
#[test]
fn test_inductive_havoc_all_with_collection_broadcast() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext {
        name: "seq_head".to_string(),
        params: vec![(
            "s".to_string(),
            crate::ir::TrustVcType::Seq(Box::new(crate::ir::TrustVcType::Int { width: 32 })),
        )],
        return_type: crate::ir::TrustVcType::Int { width: 32 },
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });
    // Broadcast axiom referencing Seq: seq_head(s) == s.index(0)
    // This exercises collection encoding in the broadcast path.
    ctx.obligations.push(
        ProofObligation::broadcast_assume("__body_axiom_seq_head", "seq_head(s) == s.index(0)")
            .with_bound_vars(vec!["s".to_string()])
            .with_trigger_patterns(vec![vec!["seq_head(s)".to_string()]]),
    );

    ctx.push_obligation(ProofObligation::assume("s_has_elem", "s.len() >= 1"));
    ctx.obligations.push(ProofObligation::loop_invariant(
        "s_nonempty",
        "s.len() >= 1",
    ));
    ctx.set_loop_modified_vars("s_nonempty", vec![]);
    ctx.push_obligation(ProofObligation::assert("post", "s.len() >= 1"));

    let result = AYEncoder::verify(&ctx);
    // The empty modified-vars frame step should preserve `s` while still
    // exercising collection-typed broadcast setup in the inductive encoder.
    expect_verified_or_unknown(
        &result,
        "Collection broadcast in empty-frame inductive step",
    );
}

/// Frame-condition inductive step with collection broadcast where the
/// collection itself is in the modified set.
///
/// When `s` is modified, no frame condition applies. The broadcast axiom
/// referencing Seq operations must still encode correctly (no sort mismatch
/// between pre-state and post-state array terms).
#[test]
fn test_inductive_frame_condition_with_collection_broadcast_modified_seq() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("i", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext {
        name: "seq_head".to_string(),
        params: vec![(
            "s".to_string(),
            crate::ir::TrustVcType::Seq(Box::new(crate::ir::TrustVcType::Int { width: 32 })),
        )],
        return_type: crate::ir::TrustVcType::Int { width: 32 },
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![],
    });
    ctx.obligations.push(
        ProofObligation::broadcast_assume("__body_axiom_seq_head", "seq_head(s) == s.index(0)")
            .with_bound_vars(vec!["s".to_string()])
            .with_trigger_patterns(vec![vec!["seq_head(s)".to_string()]]),
    );

    ctx.push_obligation(ProofObligation::assume("init_len", "s.len() >= 1"));
    ctx.push_obligation(ProofObligation::assume("init_i", "i == 0"));
    ctx.obligations.push(ProofObligation::loop_invariant(
        "s_nonempty",
        "s.len() >= 1",
    ));
    // s IS modified — no frame condition for collection length
    ctx.set_loop_modified_vars("s_nonempty", vec!["s".to_string(), "i".to_string()]);
    ctx.push_obligation(ProofObligation::assert("post", "s.len() >= 1"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Collection broadcast with modified Seq in frame-condition",
    );
}
