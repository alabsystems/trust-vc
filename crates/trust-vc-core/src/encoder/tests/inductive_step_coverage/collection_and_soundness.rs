//! Collection length frame conditions, ay array equality, soundness gaps,
//! and multi-invariant plumbing tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from inductive_step_coverage/mod.rs (#2145).

use super::*;

// ============================================================
// Correctness gap: collection length frame conditions
// ============================================================

/// Collection length frame condition: unmodified Seq preserves .len().
///
/// When Seq variable `s` is unmodified, the frame condition must constrain
/// both the array content (`s == s__pre`) AND the length term
/// (`__trust_vc_len_s == __trust_vc_len_s__pre`). Without the length frame
/// condition, the solver treats post-state len as unconstrained.
///
/// Fixes #2243.
#[test]
fn test_collection_length_frame_condition_gap() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("i", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("init_len", "s.len() >= 1"));
    ctx.push_obligation(ProofObligation::assume("init_i", "i == 0"));

    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "s_nonempty",
            "s.len() >= 1",
        ));
    ctx.set_loop_modified_vars("s_nonempty", vec!["i".to_string()]);
    ctx.push_obligation(ProofObligation::assert("post", "s.len() >= 1"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Unmodified Seq length should be preserved by frame condition",
    );
}

/// Negative: modified collection length is NOT preserved by frame condition.
///
/// When `s` IS in modified_vars, the frame condition does not apply.
/// The solver can choose any post-state length, so `s.len() >= 1` fails.
///
/// Fixes #2243.
#[test]
fn test_modified_collection_length_not_preserved() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Seq<i32>"));
    ctx.declare_var_typed("i", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("init_len", "s.len() >= 1"));
    ctx.push_obligation(ProofObligation::assume("init_i", "i == 0"));

    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "s_nonempty",
            "s.len() >= 1",
        ));
    // s IS modified — no frame condition
    ctx.set_loop_modified_vars("s_nonempty", vec!["s".to_string(), "i".to_string()]);
    ctx.push_obligation(ProofObligation::assert("post", "s.len() >= 1"));

    let result = AYEncoder::verify(&ctx);
    // Under native-seq, ay-dpll's Seq theory disables model validation,
    // so the correct SAT result is demoted to Unknown. Part of #2680.
    #[cfg(feature = "native-seq")]
    expect_fail_closed(
        &result,
        "Modified Seq should NOT have frame condition on length (model validation disabled)",
    );
    #[cfg(not(feature = "native-seq"))]
    expect_counterexample(
        &result,
        "Modified Seq should NOT have frame condition on length",
    );
}

/// Set length frame condition: unmodified Set preserves .len().
///
/// Same pattern as Seq — Set types also have separate `__trust_vc_len_*`
/// terms that need frame conditions. Fixes #2243.
#[test]
fn test_set_length_frame_condition() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.declare_var_typed("i", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("init_len", "s.len() >= 1"));
    ctx.push_obligation(ProofObligation::assume("init_i", "i == 0"));

    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "set_nonempty",
            "s.len() >= 1",
        ));
    ctx.set_loop_modified_vars("set_nonempty", vec!["i".to_string()]);
    ctx.push_obligation(ProofObligation::assert("post", "s.len() >= 1"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Unmodified Set length should be preserved by frame condition",
    );
}

/// Map domain frame condition: unmodified Map preserves dom().
///
/// When Map variable `m` is unmodified, the frame condition must constrain
/// both the array content (`m == m__pre`) AND the domain term
/// (`m_dom == m__pre_dom`). Without the domain frame condition, the solver
/// treats post-state dom() as unconstrained, so `m.dom().contains(k)` could
/// spuriously fail after a verified insert.
///
/// Fixes #2243.
#[test]
fn test_map_domain_frame_condition() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed(
        "m",
        crate::ir::TrustVcType::parse_or_opaque("Map<i32, i32>"),
    );
    ctx.declare_var_typed("i", crate::ir::TrustVcType::parse_or_opaque("u32"));
    // Insert key 1, then enter loop where m is unmodified
    ctx.push_obligation(ProofObligation::assume("inserted", "m.contains_key(1)"));
    ctx.push_obligation(ProofObligation::assume("init_i", "i == 0"));

    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "key_present",
            "m.contains_key(1)",
        ));
    ctx.set_loop_modified_vars("key_present", vec!["i".to_string()]);
    ctx.push_obligation(ProofObligation::assert("post", "m.contains_key(1)"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Unmodified Map domain should be preserved by frame condition",
    );
}

/// Diagnostic: verify that declare_variable registers Map domain variables
/// in encoder.variables for both current and pre-state Maps.
///
/// If this test passes but test_map_domain_frame_condition fails, the
/// frame condition lookup in invariants.rs is the culprit.
#[test]
fn test_map_domain_variables_registered_in_encoder() {
    let mut encoder = AYEncoder::new();
    let m_var = crate::vc::VariableDecl {
        bounded_len: false,
        name: "m".to_string(),
        ty: crate::ir::TrustVcType::Map(
            Box::new(crate::ir::TrustVcType::Int { width: 32 }),
            Box::new(crate::ir::TrustVcType::Int { width: 32 }),
        ),
    };
    let m_pre_var = crate::vc::VariableDecl {
        bounded_len: false,
        name: "m__trust_vc_pre".to_string(),
        ty: crate::ir::TrustVcType::Map(
            Box::new(crate::ir::TrustVcType::Int { width: 32 }),
            Box::new(crate::ir::TrustVcType::Int { width: 32 }),
        ),
    };
    encoder.declare_variable(&m_var).expect("declare m");
    encoder
        .declare_variable(&m_pre_var)
        .expect("declare m__trust_vc_pre");

    let has_m_dom = encoder.variables.contains_key("m_dom");
    let has_pre_dom = encoder.variables.contains_key("m__trust_vc_pre_dom");

    assert!(
        has_m_dom,
        "m_dom not found in encoder.variables; keys: {:?}",
        encoder.variables.keys().collect::<Vec<_>>()
    );
    assert!(
        has_pre_dom,
        "m__trust_vc_pre_dom not found in encoder.variables; keys: {:?}",
        encoder.variables.keys().collect::<Vec<_>>()
    );
}

/// ay-dpll Array equality propagation to reads: FIXED.
///
/// Previously (pre-aae15b56), `eq(a, b)` for Array-sorted variables did
/// not ensure `select(a, k) == select(b, k)`. This was ay-dpll bug #2383.
/// ay-dpll now correctly returns Unsat for this query, meaning the
/// aliasing workaround in invariants.rs is no longer strictly necessary.
/// We keep it as defense-in-depth since it is semantically correct and
/// costs nothing. If ay-dpll regresses, the workaround prevents silent
/// unsoundness.
#[test]
fn test_ay_array_equality_propagates_to_reads() {
    use ay_core::Sort;

    let mut encoder = AYEncoder::new();
    let dom_sort = Sort::Array(Box::new(ay_core::ArraySort {
        index_sort: Sort::bitvec(32),
        element_sort: Sort::Bool,
    }));
    let a = encoder.solver.declare_const("a_dom", dom_sort.clone());
    let b = encoder.solver.declare_const("b_dom", dom_sort);

    // Assert a_dom == b_dom
    let eq = encoder.solver.try_eq(a, b).expect("try_eq");
    encoder.solver.try_assert_term(eq).expect("try_assert");

    // Assert select(a_dom, 1) == true
    let key = encoder.solver.try_bv_const(1, 32).expect("bv_const");
    let sel_a = encoder.solver.try_select(a, key).expect("select a");
    encoder.solver.try_assert_term(sel_a).expect("assert sel_a");

    // Check: does ay-dpll propagate equality to select(b_dom, 1)?
    let sel_b = encoder.solver.try_select(b, key).expect("select b");
    let not_sel_b = encoder.solver.try_not(sel_b).expect("not sel_b");
    encoder.solver.try_push().expect("push");
    encoder
        .solver
        .try_assert_term(not_sel_b)
        .expect("assert not");
    let result = encoder.solver.check_sat();
    encoder.solver.try_pop().expect("pop");

    // ay-dpll now correctly propagates Array equality to reads (Unsat).
    // The aliasing workaround in invariants.rs is kept as defense-in-depth.
    // If this regresses to Sat, ay-dpll has a soundness regression.
    assert!(
        result.is_unsat(),
        "ay-dpll array equality propagation regressed? \
         eq(a, b) must imply select(a, k) == select(b, k). See #2383.",
    );
}

// ============================================================
// Soundness gap: loop_modified_vars validation
// ============================================================

/// SOUNDNESS: Typo in loop_modified_vars causes false verification.
///
/// If `loop_modified_vars` contains "typo_x" instead of "x", then x is
/// NOT havoced (it gets a frame condition x == x__pre). This makes the
/// inductive step trivially true: the invariant x > 0 passes because
/// x is constrained to equal x__pre, and x__pre > 0 is assumed.
///
/// This is a known validation gap: variable names in loop_modified_vars
/// are not checked against ctx.variables. A misspelled variable causes
/// a false positive (the invariant appears to hold when it shouldn't).
///
/// The correct behavior: x is modified by the loop, so with the correct
/// modified_vars ["x"], the inductive step should FAIL (x is havoced,
/// can be <= 0). With the typo ["typo_x"], x gets a frame condition
/// and the invariant falsely passes.
#[test]
fn test_modified_vars_typo_causes_false_verification() {
    // First: verify the invariant correctly FAILS with proper modified_vars
    let mut ctx_correct = VerificationContext::new();
    ctx_correct.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx_correct.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx_correct.push_obligation(ProofObligation::assume("init_x", "x == 5"));
    ctx_correct.push_obligation(ProofObligation::assume("init_y", "y == 1"));
    ctx_correct
        .obligations
        .push(crate::vc::ProofObligation::loop_invariant("x_pos", "x > 0"));
    ctx_correct.set_loop_modified_vars("x_pos", vec!["x".to_string()]);
    ctx_correct.push_obligation(ProofObligation::assert("post", "x >= 0"));

    let result_correct = AYEncoder::verify(&ctx_correct);
    expect_counterexample(
        &result_correct,
        "With correct modified_vars [x], x>0 should fail inductive step",
    );

    // Second: the SAME invariant with typo in modified_vars
    let mut ctx_typo = VerificationContext::new();
    ctx_typo.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx_typo.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx_typo.push_obligation(ProofObligation::assume("init_x", "x == 5"));
    ctx_typo.push_obligation(ProofObligation::assume("init_y", "y == 1"));
    ctx_typo
        .obligations
        .push(crate::vc::ProofObligation::loop_invariant("x_pos", "x > 0"));
    // TYPO: "typo_x" instead of "x" — x won't be havoced
    ctx_typo.set_loop_modified_vars("x_pos", vec!["typo_x".to_string()]);
    ctx_typo.push_obligation(ProofObligation::assert("post", "x >= 0"));

    let result_typo = AYEncoder::verify(&ctx_typo);
    // BUG: This SHOULD fail (same invariant, same logic) but PASSES
    // because x gets a frame condition (x == x__pre) instead of being havoced.
    // When this test starts failing (i.e., the typo case also returns
    // Counterexample), the validation gap has been fixed.
    expect_verified(
        &result_typo,
        "BUG DEMONSTRATION: typo in modified_vars causes false verification. \
         If this assertion fails, the validation gap has been fixed!",
    );
}

// ============================================================
// Inter-dependent invariants: prior verified invariants as assumptions
// ============================================================

/// Multiple loop invariants: second invariant's inductive step receives
/// the first invariant as a pre-state assumption.
///
/// Scenario: `a` is unmodified, `i` is modified. Two invariants:
///   inv1: `a >= 0` (frame condition preserves this for u32)
///   inv2: `a <= 100` (frame condition preserves this independently)
///
/// Both are individually self-sustaining via their own pre-state + frame,
/// but this test validates the plumbing: `verify_invariant_inductive_step_typed`
/// receives `verified_invariants` and adds them as pre-state assumptions.
/// If the pre-state assumption encoding fails (e.g., sort mismatch,
/// variable not found), this test would catch the regression.
#[test]
fn test_multi_invariant_inductive_step_plumbing() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("i", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("init_a", "a >= 0"));
    ctx.push_obligation(ProofObligation::assume("init_a_bound", "a <= 100"));
    ctx.push_obligation(ProofObligation::assume("init_i", "i == 0"));
    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "a_nonneg", "a >= 0",
        ));
    ctx.set_loop_modified_vars("a_nonneg", vec!["i".to_string()]);
    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "a_bounded",
            "a <= 100",
        ));
    ctx.set_loop_modified_vars("a_bounded", vec!["i".to_string()]);
    ctx.push_obligation(ProofObligation::assert("post", "a >= 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Both invariants should verify with inter-dependent assumption plumbing",
    );
}

// ADVERSARIAL SOUNDNESS GUARDS for the post-loop
// alias_framed_collection_variables frame fix. These confirm the fix does not
// "stop the stack overflow by returning a wrong/trivial Set length": a modified
// Set's length must stay unconstrained, and an unmodified Set's preserved
// length must be the real value, not a trivially-true placeholder.

/// Probe A: a MODIFIED Set must NOT have its length preserved.
/// s is in modified_vars, so alias_framed_collection_variables must skip it,
/// leaving the post-state length unconstrained. `s.len() >= 1` must fail-closed.
#[test]
fn probe_modified_set_length_not_preserved() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.declare_var_typed("i", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("init_len", "s.len() >= 1"));
    ctx.push_obligation(ProofObligation::assume("init_i", "i == 0"));
    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "set_nonempty",
            "s.len() >= 1",
        ));
    // s IS modified — no frame condition, length havoced.
    ctx.set_loop_modified_vars("set_nonempty", vec!["s".to_string(), "i".to_string()]);
    ctx.push_obligation(ProofObligation::assert("post", "s.len() >= 1"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Modified Set length must NOT be preserved (must not spuriously Verify)",
    );
}

/// Probe B: an UNMODIFIED Set's preserved length is the real value, not a
/// trivially-true placeholder. Only `s.len() >= 1` is known; the stronger
/// `s.len() >= 2` must fail-closed. If aliasing made the length trivial, this
/// would spuriously Verify.
#[test]
fn probe_unmodified_set_length_not_trivial() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::parse_or_opaque("Set<i32>"));
    ctx.declare_var_typed("i", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("init_len", "s.len() >= 1"));
    ctx.push_obligation(ProofObligation::assume("init_i", "i == 0"));
    ctx.obligations
        .push(crate::vc::ProofObligation::loop_invariant(
            "set_nonempty",
            "s.len() >= 1",
        ));
    ctx.set_loop_modified_vars("set_nonempty", vec!["i".to_string()]);
    // Stronger than what is known — must NOT verify.
    ctx.push_obligation(ProofObligation::assert("post", "s.len() >= 2"));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Unmodified Set: stronger claim len>=2 must fail-closed (length not trivial)",
    );
}

// Broadcast assumption tests for inductive step moved to
// inductive_step_broadcasts.rs (#2244) due to 500-line file limit.
