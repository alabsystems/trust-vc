// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Verification integration tests: Nat guards, declare_const, assert_forall_by.

use super::*;

#[test]
fn test_float_variable_declaration_uses_native_fp_sort() {
    use crate::encoder::AYEncoder;
    use crate::vc::VariableDecl;

    let mut encoder = AYEncoder::new();
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "f32_val".to_string(),
            ty: TrustVcType::Float { width: 32 },
        })
        .expect("f32 variable should declare");
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "f64_val".to_string(),
            ty: TrustVcType::Float { width: 64 },
        })
        .expect("f64 variable should declare");

    assert_eq!(
        encoder
            .solver
            .term_sort(*encoder.variables.get("f32_val").unwrap()),
        Sort::FloatingPoint(8, 24)
    );
    assert_eq!(
        encoder
            .solver
            .term_sort(*encoder.variables.get("f64_val").unwrap()),
        Sort::FloatingPoint(11, 53)
    );
}

#[cfg(feature = "native-seq")]
#[test]
fn test_native_seq_variable_declaration_registers_shadow_term() {
    use crate::encoder::parser_state::native_seq_shadow_var_name;
    use crate::encoder::AYEncoder;
    use crate::vc::VariableDecl;

    let mut encoder = AYEncoder::new();
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "s".to_string(),
            ty: TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })),
        })
        .expect("Seq variable should declare under native-seq");

    let seq_term = *encoder
        .variables
        .get("s")
        .expect("source Seq term should exist");
    let shadow_name = native_seq_shadow_var_name("s");
    let shadow_term = *encoder
        .variables
        .get(&shadow_name)
        .expect("declaration should register a native shadow term");
    assert_eq!(
        encoder.solver.term_sort(seq_term),
        encoder.solver.term_sort(shadow_term),
        "shadow term should use the same backend sort as the source Seq term"
    );

    let seq_eq_shadow = encoder.solver.try_eq(seq_term, shadow_term).unwrap();
    let not_seq_eq_shadow = encoder.solver.try_not(seq_eq_shadow).unwrap();
    encoder.solver.try_push().unwrap();
    encoder.solver.try_assert_term(not_seq_eq_shadow).unwrap();
    assert!(
        encoder.solver.check_sat().is_unsat(),
        "native shadow term should be bridged to the source declaration"
    );
    encoder.solver.try_pop().unwrap();

    let shadow_len = encoder.solver.try_seq_len(shadow_term).unwrap();
    let len_term = *encoder
        .collection_lengths
        .get("s")
        .expect("Seq declaration should still register the public length term");
    let shadow_len_eq = encoder.solver.try_eq(shadow_len, len_term).unwrap();
    let not_shadow_len_eq = encoder.solver.try_not(shadow_len_eq).unwrap();
    encoder.solver.try_push().unwrap();
    encoder.solver.try_assert_term(not_shadow_len_eq).unwrap();
    assert!(
        encoder.solver.check_sat().is_unsat(),
        "native shadow length should stay bridged to the public Seq length term"
    );
    encoder.solver.try_pop().unwrap();
}

#[cfg(feature = "native-strings")]
#[test]
fn test_native_string_variable_declaration_registers_int_length_alias() {
    use crate::encoder::AYEncoder;
    use crate::vc::VariableDecl;

    let mut encoder = AYEncoder::new();
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "s".to_string(),
            ty: TrustVcType::String,
        })
        .expect("String variable should declare under native-strings");

    let string_term = *encoder
        .variables
        .get("s")
        .expect("source String term should exist");
    let len_term = *encoder
        .collection_lengths
        .get("s")
        .expect("String declaration should register a public length alias");

    assert_eq!(encoder.solver.term_sort(string_term), Sort::String);
    assert_eq!(encoder.solver.term_sort(len_term), Sort::Int);

    let raw_len = encoder
        .solver
        .try_str_len(string_term)
        .expect("String term should support native str.len");
    assert_eq!(encoder.solver.term_sort(raw_len), Sort::Int);
}

#[test]
fn test_float_ieee_nan_is_not_equal_to_itself() {
    use crate::encoder::AYEncoder;

    let mut encoder = AYEncoder::new();
    let nan = encoder.solver.fp_nan(8, 24);
    let eq = encoder.solver.try_fp_eq(nan, nan).unwrap();
    let not_eq = encoder.solver.try_not(eq).unwrap();
    encoder.solver.try_assert_term(not_eq).unwrap();

    assert!(
        encoder.solver.check_sat().is_sat(),
        "IEEE NaN should remain unequal to itself"
    );
}

#[test]
fn test_float_ieee_signed_zeros_compare_equal() {
    use crate::encoder::AYEncoder;

    let mut encoder = AYEncoder::new();
    let pos_zero = encoder.solver.fp_plus_zero(8, 24);
    let neg_zero = encoder.solver.fp_minus_zero(8, 24);
    let eq = encoder.solver.try_fp_eq(pos_zero, neg_zero).unwrap();
    let not_eq = encoder.solver.try_not(eq).unwrap();
    encoder.solver.try_assert_term(not_eq).unwrap();

    assert!(
        encoder.solver.check_sat().is_unsat(),
        "IEEE +0 and -0 should compare equal via fp.eq"
    );
}

#[test]
fn test_float_ieee_overflow_adds_to_infinity() {
    use crate::encoder::AYEncoder;

    let mut encoder = AYEncoder::new();
    let rm = encoder.solver.try_fp_rounding_mode("RNE").unwrap();
    let sign = encoder.solver.try_bv_const(0, 1).unwrap();
    let exponent = encoder.solver.try_bv_const(254, 8).unwrap();
    let significand = encoder.solver.try_bv_const((1 << 23) - 1, 23).unwrap();
    let max_f32 = encoder
        .solver
        .try_fp_from_bvs(sign, exponent, significand, 8, 24)
        .unwrap();
    let overflowed = encoder.solver.try_fp_add(rm, max_f32, max_f32).unwrap();
    let pos_infinity = encoder.solver.fp_plus_infinity(8, 24);
    let eq = encoder.solver.try_fp_eq(overflowed, pos_infinity).unwrap();
    let not_eq = encoder.solver.try_not(eq).unwrap();
    encoder.solver.try_assert_term(not_eq).unwrap();

    assert!(
        encoder.solver.check_sat().is_unsat(),
        "max_f32 + max_f32 should overflow to +infinity"
    );
}

// === Nat non-negativity guard (#2418) ===

/// Nat-typed variable gets automatic non-negativity guard.
/// Asserting x < 0 for a Nat should be UNSAT.
#[test]
fn test_nat_variable_nonneg_guard_rejects_negative() {
    use crate::encoder::AYEncoder;
    use crate::vc::VariableDecl;

    let mut encoder = AYEncoder::new();
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "n".to_string(),
            ty: TrustVcType::Nat,
        })
        .expect("nat variable should declare");

    let n = *encoder.variables.get("n").unwrap();
    let zero = encoder.solver.int_const(0);
    // Assert n < 0 — should be UNSAT because Nat has n >= 0 guard.
    let neg = encoder.solver.try_lt(n, zero).unwrap();
    encoder.solver.try_assert_term(neg).unwrap();
    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "Nat variable with n < 0 should be UNSAT, got: {:?}",
        result
    );
}

/// MathInt-typed variable does NOT get non-negativity guard.
/// Asserting x < 0 for a MathInt should be SAT.
#[test]
fn test_math_int_variable_allows_negative() {
    use crate::encoder::AYEncoder;
    use crate::vc::VariableDecl;

    let mut encoder = AYEncoder::new();
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "n".to_string(),
            ty: TrustVcType::MathInt,
        })
        .expect("MathInt variable should declare");

    let n = *encoder.variables.get("n").unwrap();
    let zero = encoder.solver.int_const(0);
    // Assert n < 0 — should be SAT because MathInt has no guard.
    let neg = encoder.solver.try_lt(n, zero).unwrap();
    encoder.solver.try_assert_term(neg).unwrap();
    let result = encoder.solver.check_sat();
    assert!(
        !result.is_unsat(),
        "MathInt variable with n < 0 should be SAT, got: {:?}",
        result
    );
}

/// Nat-typed variable allows zero (boundary).
#[test]
fn test_nat_variable_allows_zero() {
    use crate::encoder::AYEncoder;
    use crate::vc::VariableDecl;

    let mut encoder = AYEncoder::new();
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "n".to_string(),
            ty: TrustVcType::Nat,
        })
        .expect("nat variable should declare");

    let n = *encoder.variables.get("n").unwrap();
    let zero = encoder.solver.int_const(0);
    // Assert n == 0 — should be SAT (zero is non-negative).
    let eq_zero = encoder.solver.try_eq(n, zero).unwrap();
    encoder.solver.try_assert_term(eq_zero).unwrap();
    let result = encoder.solver.check_sat();
    assert!(
        !result.is_unsat(),
        "Nat variable with n == 0 should be SAT, got: {:?}",
        result
    );
}

/// Multiset-typed variable declaration avoids global count quantifiers; count
/// Nat guards are emitted at operation sites.
#[test]
fn test_multiset_variable_declaration_avoids_global_count_quantifier() {
    use crate::encoder::AYEncoder;
    use crate::vc::VariableDecl;
    use ay_dpll::api::TermKind;

    let mut encoder = AYEncoder::new();
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "ms".to_string(),
            ty: TrustVcType::Multiset(Box::new(TrustVcType::Int { width: 32 })),
        })
        .expect("Multiset variable should declare");

    let assertions = encoder.solver.assertions();
    let has_forall = assertions
        .into_iter()
        .any(|term| matches!(encoder.solver.term_kind(term), TermKind::Forall));
    assert!(
        !has_forall,
        "Multiset declaration should not emit a global quantified count guard"
    );
}

// === declare_const end-to-end (#2423) ===

/// A constant declared via declare_const has its value available as an axiom.
#[test]
fn test_declare_const_verifies_value_equality() {
    use crate::encoder::AYEncoder;
    use crate::vc::VerificationContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_const_typed("MAX", crate::ir::TrustVcType::parse_or_opaque("u32"), "100");
    ctx.push_obligation(ProofObligation::assert("max_is_100", "MAX == 100"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "declare_const(MAX, u32, 100) should make MAX == 100 verifiable",
    );
}

/// A constant's value can be used in arithmetic assertions.
#[test]
fn test_declare_const_usable_in_arithmetic() {
    use crate::encoder::AYEncoder;
    use crate::vc::VerificationContext;

    let mut ctx = VerificationContext::new();
    ctx.declare_const_typed(
        "LIMIT",
        crate::ir::TrustVcType::parse_or_opaque("i32"),
        "50",
    );
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_bounded", "x >= 0 && x < LIMIT"));
    ctx.push_obligation(ProofObligation::assert("check_upper", "x < 50"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "x < LIMIT with LIMIT == 50 should imply x < 50");
}

// === assert_forall_by end-to-end (#2416) ===

/// assert_forall_by: bound variable receives scoped proof, proven condition
/// becomes available as an assumption for subsequent assertions.
///
/// We prove `k + 1 > k` (trivially true for all u32) via a scoped hint,
/// then use the proven conclusion as an assumption.
#[test]
fn test_assert_forall_by_verifies_with_scoped_proof() {
    use crate::encoder::AYEncoder;
    use crate::vc::{ProofObligation, VerificationContext};

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));

    // Prove "x + 1 > x" using a scoped hint that's trivially redundant
    // but exercises the assert_forall_by machinery.
    ctx.add_assert_forall_by_typed(
        "inc_positive",
        "x + 1 > x",
        vec![],
        vec![ProofObligation::assume("trivial", "true")],
    );

    // The proven conclusion should be available as an assumption.
    ctx.push_obligation(ProofObligation::assert("check_inc", "x + 1 > x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "assert_forall_by proven conclusion should cascade");
}

/// assert_forall_by with bound variable: the bound var is declared in context
/// and the proof block can reference it.
#[test]
fn test_assert_forall_by_bound_var_in_proof_block() {
    use crate::encoder::AYEncoder;
    use crate::vc::{ProofObligation, VerificationContext};

    let mut ctx = VerificationContext::new();

    // Prove: for all k: u32, k + 0 == k
    // Scoped proof block provides a hint (trivially true).
    ctx.add_assert_forall_by_typed(
        "add_zero_identity",
        "k + 0 == k",
        vec![("k", crate::ir::TrustVcType::parse_or_opaque("u32"))],
        vec![ProofObligation::assume("hint", "true")],
    );

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "forall k: u32, k + 0 == k should verify");
}

#[test]
fn test_assert_forall_by_scoped_assertion_can_use_bound_var() {
    use crate::encoder::AYEncoder;
    use crate::ir::TrustVcType;
    use crate::vc::{ProofObligation, VerificationContext};

    let mut ctx = VerificationContext::new();
    ctx.add_assert_forall_by_typed(
        "bound_var_assertion_scope",
        "k == k",
        vec![("k", TrustVcType::MathInt)],
        vec![ProofObligation::assert("proof_uses_k", "k == k")],
    );

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "assert_forall_by proof-block assertions should see the forall binder",
    );
}

#[test]
fn test_assert_forall_by_scoped_assertion_using_bound_var_must_prove() {
    use crate::encoder::AYEncoder;
    use crate::ir::TrustVcType;
    use crate::vc::{ProofObligation, VerificationContext};

    let mut ctx = VerificationContext::new();
    ctx.declare_helper_function_typed(
        "mystery",
        TrustVcType::MathInt,
        vec![("v".to_string(), TrustVcType::MathInt)],
    );
    ctx.add_assert_forall_by_typed(
        "bound_var_assertion_scope_rejected",
        "k == k",
        vec![("k", TrustVcType::MathInt)],
        vec![ProofObligation::assert(
            "proof_uses_k_unproved",
            "mystery(k) == k",
        )],
    );

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "assert_forall_by proof-block assertions over the forall binder must be checked",
    );
}

/// assert_forall_by with MathInt bound variables must feed back a quantified
/// fact, not a leaked Skolem constant. Part of #2551.
#[test]
fn test_assert_forall_by_bound_var_reuses_quantified_fact_math_int() {
    use crate::encoder::AYEncoder;
    use crate::ir::TrustVcType;
    use crate::vc::{ProofObligation, VerificationContext};

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::MathInt);
    ctx.declare_helper_function_typed(
        "id",
        TrustVcType::MathInt,
        vec![("v".to_string(), TrustVcType::MathInt)],
    );
    ctx.add_assert_forall_by_typed(
        "id_identity",
        "id(k) == k",
        vec![("k", TrustVcType::MathInt)],
        vec![ProofObligation::assume("id_axiom", "id(k) == k")],
    );
    ctx.push_obligation(ProofObligation::assert("use_forall_fact", "id(x) == x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall-by proof should reuse its conclusion as a quantified fact",
    );
}

/// assert_forall_by must also preserve concrete BV sorts when the proven fact
/// is replayed as a quantified assumption. Part of #2551.
#[test]
fn test_assert_forall_by_bound_var_reuses_quantified_fact_bitvector_helper() {
    use crate::encoder::AYEncoder;
    use crate::ir::TrustVcType;
    use crate::vc::{ProofObligation, VerificationContext};

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_helper_function_typed(
        "id",
        TrustVcType::Uint { width: 32 },
        vec![("v".to_string(), TrustVcType::Uint { width: 32 })],
    );
    ctx.add_assert_forall_by_typed(
        "id_identity",
        "id(k) == k",
        vec![("k", crate::ir::TrustVcType::parse_or_opaque("u32"))],
        vec![ProofObligation::assume("id_axiom", "id(k) == k")],
    );
    ctx.push_obligation(ProofObligation::assert("use_forall_fact", "id(x) == x"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall-by proof should reuse its conclusion with BV helper sorts intact",
    );
}

/// assert_forall_by_typed with Nat bound variable gets non-negativity guard.
#[test]
fn test_assert_forall_by_typed_nat_bound_var() {
    use crate::encoder::AYEncoder;
    use crate::vc::{ProofObligation, VerificationContext};

    let mut ctx = VerificationContext::new();

    // Prove: for all n: nat, n >= 0 (tautological with Nat guard)
    ctx.add_assert_forall_by_typed(
        "nat_nonneg",
        "n >= 0",
        vec![("n", crate::ir::TrustVcType::Nat)],
        vec![ProofObligation::assume("hint", "true")],
    );

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "forall n: nat, n >= 0 should verify with Nat guard",
    );
}

/// Negative test: forall-by with an insufficient proof block should NOT
/// promote its conclusion. If the system blindly accepts conclusions
/// without verifying the proof block, this test catches it. Part of #949.
#[test]
fn test_assert_forall_by_unproven_conclusion_not_available() {
    use crate::encoder::AYEncoder;
    use crate::ir::TrustVcType;
    use crate::vc::{ProofObligation, VerificationContext};

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::MathInt);
    ctx.declare_helper_function_typed(
        "mystery",
        TrustVcType::MathInt,
        vec![("v".to_string(), TrustVcType::MathInt)],
    );

    // Attempt to prove "mystery(k) == k" with only "true" as a hint.
    // Since mystery is uninterpreted, the proof block cannot establish this.
    ctx.add_assert_forall_by_typed(
        "mystery_identity",
        "mystery(k) == k",
        vec![("k", TrustVcType::MathInt)],
        vec![ProofObligation::assume("insufficient_hint", "true")],
    );

    // If the unproven conclusion leaked as an assumption, this would verify.
    ctx.push_obligation(ProofObligation::assert(
        "use_unproven_fact",
        "mystery(x) == x",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_not_verified(
        &result,
        "unproven forall-by conclusion should not be available as assumption",
    );
}
