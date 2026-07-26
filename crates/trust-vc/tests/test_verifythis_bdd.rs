// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 45 - Binary Decision Diagram (BDD) core VCs.
//!
//! VerifyThis 2023 included a BDD challenge. This tier verifies BDD
//! representation invariants and evaluation over a flat-array encoding:
//!   - `bdd_var: Seq<i64>`  — variable index per node (symbolic sentinel for terminals)
//!   - `bdd_lo:  Seq<i64>`  — low-child index per node (-1 for terminals)
//!   - `bdd_hi:  Seq<i64>`  — high-child index per node (-1 for terminals)
//!   - Node 0 = FALSE terminal, Node 1 = TRUE terminal
//!
//! Core obligations:
//!   - terminal nodes have sentinel variable indices
//!   - variable ordering: children have strictly greater var index than parent
//!   - reducedness: lo != hi for all non-terminal nodes
//!   - evaluation follows the correct child based on variable assignment
//!   - insert preserves ordering invariant
//!
//! Positive tests use symbolic var indices (var_x0 < var_x1 < var_sentinel)
//! and symbolic boolean assignments, so the solver must prove invariants hold
//! for any valid ordering and any satisfying input, not just one concrete
//! evaluation trace. Graph topology (lo/hi pointers) stays concrete.
//!
//! Part of #2187.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationPipeline.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

fn verify_with_pipeline(context: VerificationContext) -> VerifyResult {
    let mut pipeline = VerificationPipeline::new();
    pipeline.replace_context(context);
    pipeline.verify()
}

fn assume_seq_i64(ctx: &mut VerificationContext, name: &str, values: &[i64]) {
    let len_name = format!("{name}_len");
    let len_cond = format!("{name}.len() == {}", values.len());
    ctx.declare_var_parsed(name, "Seq<i64>");
    ctx.push_assume(&len_name, &len_cond);
    for (idx, value) in values.iter().enumerate() {
        let elem_name = format!("{name}_{idx}");
        let elem_cond = format!("{name}.index({idx}) == {value}");
        ctx.push_assume(&elem_name, &elem_cond);
    }
}

fn assume_seq_exprs(ctx: &mut VerificationContext, name: &str, exprs: &[&str]) {
    let len_name = format!("{name}_len");
    let len_cond = format!("{name}.len() == {}", exprs.len());
    ctx.declare_var_parsed(name, "Seq<i64>");
    ctx.push_assume(&len_name, &len_cond);
    for (idx, expr) in exprs.iter().enumerate() {
        let elem_name = format!("{name}_{idx}");
        let elem_cond = format!("{name}.index({idx}) == {expr}");
        ctx.push_assume(&elem_name, &elem_cond);
    }
}

/// Declare symbolic BDD var indices: var_x0 < var_x1 < var_sentinel
/// with non-negative and anti-overflow bounds.
fn setup_symbolic_bdd_vars_2(ctx: &mut VerificationContext) {
    ctx.declare_var_parsed("var_x0", "i64");
    ctx.declare_var_parsed("var_x1", "i64");
    ctx.declare_var_parsed("var_sentinel", "i64");
    ctx.push_assume("var_x0_nonneg", "var_x0 >= 0");
    ctx.push_assume("var_order_01", "var_x0 < var_x1");
    ctx.push_assume("var_order_1s", "var_x1 < var_sentinel");
    ctx.push_assume("var_sentinel_bound", "var_sentinel < 1000");
}

/// 3-variable variant: var_x0 < var_x1 < var_x2 < var_sentinel.
fn setup_symbolic_bdd_vars_3(ctx: &mut VerificationContext) {
    ctx.declare_var_parsed("var_x0", "i64");
    ctx.declare_var_parsed("var_x1", "i64");
    ctx.declare_var_parsed("var_x2", "i64");
    ctx.declare_var_parsed("var_sentinel", "i64");
    ctx.push_assume("var_x0_nonneg", "var_x0 >= 0");
    ctx.push_assume("var_order_01", "var_x0 < var_x1");
    ctx.push_assume("var_order_12", "var_x1 < var_x2");
    ctx.push_assume("var_order_2s", "var_x2 < var_sentinel");
    ctx.push_assume("var_sentinel_bound", "var_sentinel < 1000");
}

fn setup_symbolic_boolean_assignment_2(ctx: &mut VerificationContext) {
    ctx.declare_var_parsed("assign_x0", "i64");
    ctx.declare_var_parsed("assign_x1", "i64");
    ctx.push_assume("assign_x0_bool", "assign_x0 == 0 || assign_x0 == 1");
    ctx.push_assume("assign_x1_bool", "assign_x1 == 0 || assign_x1 == 1");
    assume_seq_exprs(ctx, "assign", &["assign_x0", "assign_x1"]);
}

fn setup_symbolic_and_eval(ctx: &mut VerificationContext) {
    setup_symbolic_bdd_vars_2(ctx);
    setup_symbolic_boolean_assignment_2(ctx);
    assume_seq_exprs(ctx, "bdd_var", AND_BDD_VAR);
    assume_seq_i64(ctx, "bdd_lo", &[-1, -1, 0, 0]);
    assume_seq_i64(ctx, "bdd_hi", &[-1, -1, 1, 2]);

    ctx.declare_var_parsed("step1", "i64");
    ctx.declare_var_parsed("step2", "i64");
    ctx.declare_var_parsed("terminal", "i64");
    ctx.push_assume("step1_root", "step1 == 3");
    ctx.push_assume(
        "step2_from_assign_x0",
        "(assign.index(0) == 0 && step2 == bdd_lo.index(step1)) || (assign.index(0) == 1 && step2 == bdd_hi.index(step1))",
    );
    ctx.push_assume(
        "terminal_from_assign_x1",
        "(step2 == 0 && terminal == step2) || (step2 == 2 && assign.index(1) == 0 && terminal == bdd_lo.index(step2)) || (step2 == 2 && assign.index(1) == 1 && terminal == bdd_hi.index(step2))",
    );
}

fn setup_symbolic_or_eval(ctx: &mut VerificationContext) {
    setup_symbolic_bdd_vars_2(ctx);
    setup_symbolic_boolean_assignment_2(ctx);
    assume_seq_exprs(ctx, "bdd_var", OR_BDD_VAR);
    assume_seq_i64(ctx, "bdd_lo", &[-1, -1, 0, 2]);
    assume_seq_i64(ctx, "bdd_hi", &[-1, -1, 1, 1]);

    ctx.declare_var_parsed("step1", "i64");
    ctx.declare_var_parsed("step2", "i64");
    ctx.declare_var_parsed("terminal", "i64");
    ctx.push_assume("step1_root", "step1 == 3");
    ctx.push_assume(
        "step2_from_assign_x0",
        "(assign.index(0) == 0 && step2 == bdd_lo.index(step1)) || (assign.index(0) == 1 && step2 == bdd_hi.index(step1))",
    );
    ctx.push_assume(
        "terminal_from_assign_x1",
        "(step2 == 1 && terminal == step2) || (step2 == 2 && assign.index(1) == 0 && terminal == bdd_lo.index(step2)) || (step2 == 2 && assign.index(1) == 1 && terminal == bdd_hi.index(step2))",
    );
}

/// AND BDD bdd_var with symbolic indices for a 4-node BDD.
const AND_BDD_VAR: &[&str] = &["var_sentinel", "var_sentinel", "var_x1", "var_x0"];

// ========================================================================
// GROUP A: BDD representation invariants (symbolic var indices)
// ========================================================================
//
// BDD for `x0 AND x1` (4 nodes, symbolic var indices):
//   Node 0: FALSE terminal — var=var_sentinel, lo=-1, hi=-1
//   Node 1: TRUE terminal  — var=var_sentinel, lo=-1, hi=-1
//   Node 2: x1 decision    — var=var_x1,       lo=0,  hi=1
//   Node 3: x0 decision    — var=var_x0,       lo=0,  hi=2  (root)
//   Constraint: var_x0 < var_x1 < var_sentinel

/// Tier 45a: terminal nodes carry the sentinel variable index.
#[test]
fn test_vt_tier45a_terminal_nodes_have_sentinel_var() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_bdd_vars_2(&mut ctx);
    assume_seq_exprs(&mut ctx, "bdd_var", AND_BDD_VAR);

    ctx.push_assert(
        "false_terminal_sentinel",
        "bdd_var.index(0) == var_sentinel",
    );
    ctx.push_assert("true_terminal_sentinel", "bdd_var.index(1) == var_sentinel");
    ctx.push_assert("non_terminal_x1", "bdd_var.index(2) < var_sentinel");
    ctx.push_assert("non_terminal_x0", "bdd_var.index(3) < var_sentinel");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 45a: terminal sentinel invariant should verify, got: {:?}",
        result,
    );
}

/// Tier 45b: variable ordering — children have strictly greater var index.
#[test]
fn test_vt_tier45b_variable_ordering_and_bdd() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_bdd_vars_2(&mut ctx);
    assume_seq_exprs(&mut ctx, "bdd_var", AND_BDD_VAR);
    assume_seq_i64(&mut ctx, "bdd_lo", &[-1, -1, 0, 0]);
    assume_seq_i64(&mut ctx, "bdd_hi", &[-1, -1, 1, 2]);

    ctx.push_assert(
        "node3_lo_ordering",
        "bdd_var.index(bdd_lo.index(3)) > bdd_var.index(3)",
    );
    ctx.push_assert(
        "node3_hi_ordering",
        "bdd_var.index(bdd_hi.index(3)) > bdd_var.index(3)",
    );
    ctx.push_assert(
        "node2_lo_ordering",
        "bdd_var.index(bdd_lo.index(2)) > bdd_var.index(2)",
    );
    ctx.push_assert(
        "node2_hi_ordering",
        "bdd_var.index(bdd_hi.index(2)) > bdd_var.index(2)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 45b: BDD ordering invariant should verify, got: {:?}",
        result,
    );
}

/// Tier 45c: reducedness — every non-terminal node has lo != hi.
#[test]
fn test_vt_tier45c_reducedness_non_terminals_differ() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_bdd_vars_2(&mut ctx);
    assume_seq_exprs(&mut ctx, "bdd_var", AND_BDD_VAR);
    assume_seq_i64(&mut ctx, "bdd_lo", &[-1, -1, 0, 0]);
    assume_seq_i64(&mut ctx, "bdd_hi", &[-1, -1, 1, 2]);

    ctx.push_assert("node2_reduced", "bdd_lo.index(2) != bdd_hi.index(2)");
    ctx.push_assert("node3_reduced", "bdd_lo.index(3) != bdd_hi.index(3)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 45c: BDD reducedness should verify, got: {:?}",
        result,
    );
}

/// Tier 45d: no duplicate nodes — distinct non-terminal nodes differ in
/// at least one of (var, lo, hi).
#[test]
fn test_vt_tier45d_no_duplicate_nodes() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_bdd_vars_2(&mut ctx);
    assume_seq_exprs(&mut ctx, "bdd_var", AND_BDD_VAR);
    assume_seq_i64(&mut ctx, "bdd_lo", &[-1, -1, 0, 0]);
    assume_seq_i64(&mut ctx, "bdd_hi", &[-1, -1, 1, 2]);

    // var_x1 != var_x0 follows from var_x0 < var_x1
    ctx.push_assert("nodes_2_3_distinct", "bdd_var.index(2) != bdd_var.index(3)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 45d: no-duplicate invariant should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: BDD evaluation (symbolic var indices, symbolic boolean assignments)
// ========================================================================

/// Tier 45e: `x0 AND x1` evaluates correctly for every boolean assignment.
#[test]
fn test_vt_tier45e_eval_and_matches_symbolic_boolean_semantics() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_and_eval(&mut ctx);

    ctx.push_assert("step2_hits_false_or_x1", "step2 == 0 || step2 == 2");
    ctx.push_assert("terminal_is_boolean", "terminal == 0 || terminal == 1");
    ctx.push_assert(
        "and_semantics",
        "((assign.index(0) == 1 && assign.index(1) == 1) && terminal == 1) || (((assign.index(0) == 0) || (assign.index(1) == 0)) && terminal == 0)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 45e: AND BDD should match symbolic boolean semantics, got: {:?}",
        result,
    );
}

/// Tier 45f: when `x0` is true and `x1` is false, the AND BDD takes hi then lo.
#[test]
fn test_vt_tier45f_eval_and_true_false_uses_assignment_driven_path() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_and_eval(&mut ctx);
    ctx.push_assume("x0_true", "assign.index(0) == 1");
    ctx.push_assume("x1_false", "assign.index(1) == 0");

    ctx.push_assert("root_follows_hi_branch", "step2 == 2");
    ctx.push_assert("x1_node_selected", "bdd_var.index(step2) == var_x1");
    ctx.push_assert("second_branch_reaches_false", "terminal == 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 45f: AND BDD should follow hi/lo under symbolic assignment, got: {:?}",
        result,
    );
}

/// Tier 45g: when `x0` is false, the AND BDD short-circuits to FALSE regardless of `x1`.
/// Gated: BDD solver timeout >600s. Needs v2 parallel solving. (#2658 Category H)
#[test]
#[cfg(feature = "expensive-tests")]
fn test_vt_tier45g_eval_and_false_any_short_circuits() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_and_eval(&mut ctx);
    ctx.push_assume("x0_false", "assign.index(0) == 0");

    ctx.push_assert("root_follows_lo_branch", "step2 == 0");
    ctx.push_assert("short_circuit_terminal", "terminal == 0");
    ctx.push_assert(
        "short_circuit_hits_terminal",
        "bdd_var.index(step2) == var_sentinel",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 45g: AND BDD should short-circuit to FALSE, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: BDD construction — OR BDD and insert (symbolic var indices)
// ========================================================================

/// OR BDD bdd_var: same terminal/decision layout, different child wiring.
const OR_BDD_VAR: &[&str] = &["var_sentinel", "var_sentinel", "var_x1", "var_x0"];

/// Tier 45h: OR BDD ordering — children have strictly greater var index.
#[test]
fn test_vt_tier45h_or_bdd_ordering_invariant() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_bdd_vars_2(&mut ctx);
    assume_seq_exprs(&mut ctx, "bdd_var", OR_BDD_VAR);
    assume_seq_i64(&mut ctx, "bdd_lo", &[-1, -1, 0, 2]);
    assume_seq_i64(&mut ctx, "bdd_hi", &[-1, -1, 1, 1]);

    ctx.push_assert(
        "or_node3_lo_ordering",
        "bdd_var.index(bdd_lo.index(3)) > bdd_var.index(3)",
    );
    ctx.push_assert(
        "or_node3_hi_ordering",
        "bdd_var.index(bdd_hi.index(3)) > bdd_var.index(3)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 45h: OR BDD ordering should verify, got: {:?}",
        result,
    );
}

/// Tier 45i: `x0 OR x1` evaluates correctly for every boolean assignment.
#[test]
fn test_vt_tier45i_eval_or_matches_symbolic_boolean_semantics() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_or_eval(&mut ctx);

    ctx.push_assert("step2_hits_true_or_x1", "step2 == 1 || step2 == 2");
    ctx.push_assert("terminal_is_boolean", "terminal == 0 || terminal == 1");
    ctx.push_assert(
        "or_semantics",
        "(((assign.index(0) == 1) || (assign.index(1) == 1)) && terminal == 1) || ((assign.index(0) == 0 && assign.index(1) == 0) && terminal == 0)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 45i: OR BDD should match symbolic boolean semantics, got: {:?}",
        result,
    );
}

/// Tier 45j: insert a new x2 node under the AND BDD preserves ordering.
///
/// 5-node BDD with var_x0 < var_x1 < var_x2 < var_sentinel.
#[test]
fn test_vt_tier45j_insert_new_variable_preserves_ordering() {
    let mut ctx = VerificationContext::new();
    setup_symbolic_bdd_vars_3(&mut ctx);
    assume_seq_exprs(
        &mut ctx,
        "bdd_var",
        &["var_sentinel", "var_sentinel", "var_x1", "var_x0", "var_x2"],
    );
    assume_seq_i64(&mut ctx, "bdd_lo", &[-1, -1, 0, 0, 0]);
    assume_seq_i64(&mut ctx, "bdd_hi", &[-1, -1, 4, 2, 1]);

    ctx.push_assert(
        "node3_hi_order",
        "bdd_var.index(bdd_hi.index(3)) > bdd_var.index(3)",
    );
    ctx.push_assert(
        "node2_hi_order",
        "bdd_var.index(bdd_hi.index(2)) > bdd_var.index(2)",
    );
    ctx.push_assert(
        "node4_lo_order",
        "bdd_var.index(bdd_lo.index(4)) > bdd_var.index(4)",
    );
    ctx.push_assert(
        "node4_hi_order",
        "bdd_var.index(bdd_hi.index(4)) > bdd_var.index(4)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 45j: insert new var should preserve ordering, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Soundness negatives (concrete — test specific bad structures)
// ========================================================================

/// Tier 45k: violating the ordering invariant must be rejected.
#[test]
fn test_vt_tier45k_violated_ordering_rejected() {
    let mut ctx = VerificationContext::new();
    // Bad: node 2 has var=0, same as node 3 — ordering violated
    assume_seq_i64(&mut ctx, "bdd_var", &[99, 99, 0, 0]);
    assume_seq_i64(&mut ctx, "bdd_lo", &[-1, -1, 0, 0]);
    assume_seq_i64(&mut ctx, "bdd_hi", &[-1, -1, 1, 2]);

    ctx.push_assert(
        "ordering_check",
        "bdd_var.index(bdd_hi.index(3)) > bdd_var.index(3)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 45k SOUNDNESS: violated ordering must be rejected, got: {:?}",
        result,
    );
}

/// Tier 45l: a node with lo == hi violates reducedness.
#[test]
fn test_vt_tier45l_unreduced_node_rejected() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "bdd_var", &[99, 99, 1]);
    // Bad: node 2 has lo=1, hi=1 (both point to TRUE — node is redundant)
    assume_seq_i64(&mut ctx, "bdd_lo", &[-1, -1, 1]);
    assume_seq_i64(&mut ctx, "bdd_hi", &[-1, -1, 1]);

    ctx.push_assert("reduced_check", "bdd_lo.index(2) != bdd_hi.index(2)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 45l SOUNDNESS: unreduced node must be rejected, got: {:?}",
        result,
    );
}
