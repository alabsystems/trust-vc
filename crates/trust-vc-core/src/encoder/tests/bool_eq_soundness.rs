//! Bool-sorted try_eq soundness tests (mk_eq finding audit).
//!
//! An audit raised whether ay-dpll's mk_eq may not properly constrain
//! Bool-sorted terms. Investigation shows ay's Tseitin encoder generates
//! proper biconditional clauses for Bool equality, and ay has 7 regression
//! tests in test_bool_eq.rs. These trust-vc-level tests verify the constraint
//! holds through our encoder's solver interface.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

/// #2660 AC1: try_eq(bool_a, bool_b) + assert(bool_a) must force bool_b=true.
/// If eq(Bool, Bool) acted as an uninterpreted function (the suspected bug),
/// this would be SAT with bool_b=false.
#[test]
fn test_bool_try_eq_forces_implication() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let a = solver.declare_const("a", Sort::Bool);
    let b = solver.declare_const("b", Sort::Bool);

    // Assert eq(a, b) — should behave as biconditional
    let eq_ab = solver.try_eq(a, b).unwrap();
    solver.try_assert_term(eq_ab).unwrap();

    // Assert a = true
    solver.try_assert_term(a).unwrap();

    // Assert b = false — should be UNSAT if eq is biconditional
    let not_b = solver.try_not(b).unwrap();
    solver.try_assert_term(not_b).unwrap();

    assert!(
        solver.try_check_sat().unwrap().is_unsat(),
        "#2660: try_eq(bool_a, bool_b) + a + !b must be UNSAT — \
         Bool equality must enforce biconditional semantics"
    );
}

/// #2660 reverse direction: try_eq(a, b) + !a must force b=false.
#[test]
fn test_bool_try_eq_forces_reverse_implication() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let a = solver.declare_const("a", Sort::Bool);
    let b = solver.declare_const("b", Sort::Bool);

    let eq_ab = solver.try_eq(a, b).unwrap();
    solver.try_assert_term(eq_ab).unwrap();

    let not_a = solver.try_not(a).unwrap();
    solver.try_assert_term(not_a).unwrap();

    // b must also be false; b=true should be UNSAT
    solver.try_assert_term(b).unwrap();

    assert!(
        solver.try_check_sat().unwrap().is_unsat(),
        "#2660: try_eq(a, b) + !a + b must be UNSAT"
    );
}

/// #2660 SAT positive control: eq(a, b) allows both-true.
/// Combined with `test_bool_try_eq_allows_both_false`, these two SAT
/// tests distinguish biconditional from NOR (!a ∧ !b), which also
/// makes (T,F) and (F,T) UNSAT but makes (T,T) UNSAT too.
#[test]
fn test_bool_try_eq_allows_both_true() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let a = solver.declare_const("a", Sort::Bool);
    let b = solver.declare_const("b", Sort::Bool);

    let eq_ab = solver.try_eq(a, b).unwrap();
    solver.try_assert_term(eq_ab).unwrap();

    // Assert both true — biconditional allows this, NOR does not
    solver.try_assert_term(a).unwrap();
    solver.try_assert_term(b).unwrap();

    assert!(
        solver.try_check_sat().unwrap().is_sat(),
        "#2660: try_eq(a, b) + a + b must be SAT — \
         biconditional allows both-true (NOR would not)"
    );
}

/// #2660 SAT positive control: eq(a, b) allows both-false.
/// Distinguishes biconditional (a ↔ b) from conjunction (a ∧ b):
///   - Biconditional: a=false, b=false satisfies a ↔ b → SAT
///   - Conjunction:    a=false, b=false violates a ∧ b → UNSAT
///
/// Without this test, the UNSAT-only tests above cannot detect an
/// over-constraining bug where try_eq returns conjunction.
#[test]
fn test_bool_try_eq_allows_both_false() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let a = solver.declare_const("a", Sort::Bool);
    let b = solver.declare_const("b", Sort::Bool);

    let eq_ab = solver.try_eq(a, b).unwrap();
    solver.try_assert_term(eq_ab).unwrap();

    // Assert both false — biconditional allows this, conjunction does not
    let not_a = solver.try_not(a).unwrap();
    let not_b = solver.try_not(b).unwrap();
    solver.try_assert_term(not_a).unwrap();
    solver.try_assert_term(not_b).unwrap();

    assert!(
        solver.try_check_sat().unwrap().is_sat(),
        "#2660: try_eq(a, b) + !a + !b must be SAT — \
         biconditional allows both-false (a ∧ b would not)"
    );
}

/// #2660 datatype-invariant pattern: try_eq(inv_T(v), body) used in
/// datatype_invariants.rs:307. Both operands are Bool-sorted UF applications.
/// Verifies the biconditional holds for UF-produced Bool terms (not just
/// declared constants).
#[test]
fn test_bool_try_eq_uf_biconditional() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let poly = Sort::Uninterpreted("T".to_string());
    let v = solver.declare_const("v", poly.clone());

    // Model: inv_T(v) and body(v) are Bool-sorted UFs
    let inv_fn = solver
        .try_declare_fun("inv_T", std::slice::from_ref(&poly), Sort::Bool)
        .unwrap();
    let body_fn = solver
        .try_declare_fun("body_T", &[poly], Sort::Bool)
        .unwrap();

    let inv_v = solver.try_apply(&inv_fn, &[v]).unwrap();
    let body_v = solver.try_apply(&body_fn, &[v]).unwrap();

    // Assert inv_T(v) <==> body_T(v) via try_eq
    let iff = solver.try_eq(inv_v, body_v).unwrap();
    solver.try_assert_term(iff).unwrap();

    // Assert inv_T(v) = true
    solver.try_assert_term(inv_v).unwrap();

    // Assert body_T(v) = false — UNSAT if biconditional works
    let not_body = solver.try_not(body_v).unwrap();
    solver.try_assert_term(not_body).unwrap();

    assert!(
        solver.try_check_sat().unwrap().is_unsat(),
        "#2660: try_eq(inv_T(v), body_T(v)) with inv=true must force body=true — \
         validates datatype_invariants.rs:307 pattern"
    );
}
