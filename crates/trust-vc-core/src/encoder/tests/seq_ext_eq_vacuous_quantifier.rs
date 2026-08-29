// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `encode_seq_extensional_eq` must never emit a DEGENERATE pointwise
//! quantifier — `(forall ((__trust_vc_seq_eq_idx_N (_ BitVec 64))) true)`.
//!
//! MECHANISM. The pointwise body is
//! `implies(in_bounds, eq(select(left_source, left_idx), select(right_source,
//! right_idx)))`. ay terms are HASH-CONSED and `mk_eq` folds `x = x` to `true`,
//! after which `mk_implies(_, true)` folds to `true`. So whenever the two sides
//! reduce to the SAME select term — same backing array AND same carrier offset —
//! the quantifier body is the constant `true` and the emitted `forall` says
//! nothing at all. The SYNTACTICALLY reflexive case (`left == right` as IR
//! expressions) short-circuits earlier in the function; this is the
//! STRUCTURALLY reflexive one, where two DISTINCT IR expressions lower to the
//! same backing term at the same offset.
//!
//! MEASURED at the defective HEAD (`412f3f5d`), by rendering the encoded term:
//!
//! ```text
//!   a == b (aliased)          BEFORE  (forall ((__trust_vc_seq_eq_idx_2_2_3 (_ BitVec 64))) true)
//!                             AFTER   true
//!   a == a.subrange(0, k)     BEFORE  (and (= seq_a_len (bv2nat ((_ int2bv 64) k)))
//!                                          (forall ((__trust_vc_seq_eq_idx_2_2_3 (_ BitVec 64))) true))
//!                             AFTER   (= seq_a_len (bv2nat ((_ int2bv 64) k)))
//!   a == b (distinct)         BEFORE == AFTER, byte-identical:
//!                                     (and (= seq_a_len seq_b_len)
//!                                          (forall ((__trust_vc_seq_eq_idx_2_3_4 (_ BitVec 64)))
//!                                            (or (= (select seq_a __trust_vc_seq_eq_idx_2_3_4)
//!                                                   (select seq_b __trust_vc_seq_eq_idx_2_3_4))
//!                                                (not (< (bv2nat __trust_vc_seq_eq_idx_2_3_4) seq_a_len)))))
//! ```
//!
//! WHY IT MATTERS. The vacuous collapse is certified, but it is also pure waste
//! and a live landmine for downstream quantifier bookkeeping: ay's conservative
//! `quantified_proof_translation_incomplete` marker fired on this exact shape,
//! and its read site demanded a strictly checkable proof and downgraded a
//! computed UNSAT to `Unknown(UnhandledQuantifier)` — rotating four trust-vc
//! soundness tests pass/fail (fixed ay-side at `35a1ee861`). This is the other
//! half: stop emitting the useless shape at all.
//!
//! SOUNDNESS. Dropping a `true` conjunct removes no constraint. The guard is
//! EXACT equality with `bool_const(true)` — never a structural "looks trivial"
//! test — so a body that is not literally the folded constant still gets its
//! quantifier. Two pins hold the guard in place from the other side:
//!
//!   * `structurally_reflexive_seq_eq_keeps_its_length_equality` — the
//!     LOAD-BEARING `len(a) == k` conjunct must SURVIVE; only the quantifier
//!     may go.
//!   * `must_still_emit_pointwise_forall_for_distinct_sources` — a genuine
//!     `Seq == Seq` over two different backing arrays MUST still carry its
//!     pointwise congruence, or the guard would have degenerated into dropping
//!     real element constraints.

use super::*;
use crate::ir::{CollectionOp, CompareOp, TrustVcExpr, TrustVcType};
use ay_dpll::api::{ArraySort, Logic, Solver, Sort, Term};

/// Which `Seq == Seq` shape to encode.
#[derive(Clone, Copy)]
enum Shape {
    /// `a == b` where `a` and `b` are distinct IR variables bound to the SAME
    /// backing array term (the loop-invariant inductive step's
    /// `s == s__trust_vc_pre` framing). Both selects collapse to one term.
    AliasedSources,
    /// `a == a.subrange(0, k)` — a distinct IR shape at the same zero offset
    /// over the same backing array, so the pointwise body still folds to
    /// `true`, but the LENGTH equality `len(a) == k` is genuine information.
    AliasedViaZeroOffsetSubrange,
    /// `a == b` over two genuinely DIFFERENT backing arrays. The pointwise body
    /// is non-trivial and its quantifier must be emitted.
    DistinctSources,
}

/// The array-backed `Seq<i32>` carrier sort (non-`native-seq` encoding).
fn seq_sort() -> Sort {
    Sort::Array(Box::new(ArraySort {
        index_sort: Sort::bitvec(crate::ir::pointer_width()),
        element_sort: Sort::bitvec(32),
    }))
}

fn seq_ty() -> TrustVcType {
    TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }))
}

fn seq_var(name: &str) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty: seq_ty(),
    }
}

/// Encode the chosen `Seq == Seq` shape and return the rendered s-expression of
/// the resulting term.
///
/// Both operands are spec `Seq<i32>` with UNBOUNDED Int lengths, deliberately
/// not carrier-bounded, so the encoding takes the no-companion /
/// Int-domain-guard path that the cardinal-false-verify fix (`1280263f`)
/// installed — the same path that mints the deterministic binder.
fn encode_seq_eq_sexpr(shape: Shape) -> String {
    let mut solver = Solver::try_new(Logic::All).expect("solver");

    let a_term = solver
        .try_declare_const("seq_a", seq_sort())
        .expect("declare seq_a");
    let b_term = match shape {
        Shape::DistinctSources => solver
            .try_declare_const("seq_b", seq_sort())
            .expect("declare seq_b"),
        _ => a_term,
    };
    let a_len = solver
        .try_declare_const("seq_a_len", Sort::Int)
        .expect("declare seq_a_len");
    let b_len = solver
        .try_declare_const("seq_b_len", Sort::Int)
        .expect("declare seq_b_len");
    let k = solver.try_declare_const("k", Sort::Int).expect("declare k");

    let mut variables: std::collections::HashMap<String, Term> = std::collections::HashMap::new();
    let mut var_types: std::collections::HashMap<String, TrustVcType> =
        std::collections::HashMap::new();
    let mut collection_lengths: std::collections::HashMap<String, Term> =
        std::collections::HashMap::new();
    variables.insert("a".to_string(), a_term);
    var_types.insert("a".to_string(), seq_ty());
    collection_lengths.insert("a".to_string(), a_len);
    variables.insert("k".to_string(), k);
    var_types.insert("k".to_string(), TrustVcType::MathInt);
    // `b` is registered ONLY for the two-operand shapes. The parser keys
    // collection metadata by TERM as well as by name, so registering a second
    // name over the SAME backing term would make which of the two length
    // symbols wins depend on HashMap iteration order — a genuinely flaky
    // assertion. The subrange shape needs exactly one registered length.
    if !matches!(shape, Shape::AliasedViaZeroOffsetSubrange) {
        variables.insert("b".to_string(), b_term);
        var_types.insert("b".to_string(), seq_ty());
        collection_lengths.insert("b".to_string(), b_len);
    }

    let functions = std::collections::HashMap::new();

    let right = match shape {
        Shape::AliasedSources | Shape::DistinctSources => seq_var("b"),
        Shape::AliasedViaZeroOffsetSubrange => TrustVcExpr::CollectionOp {
            op: CollectionOp::Subrange,
            receiver: Box::new(seq_var("a")),
            receiver_name: Some("a".to_string()),
            args: vec![
                TrustVcExpr::IntLit {
                    value: 0,
                    ty: TrustVcType::MathInt,
                },
                TrustVcExpr::Var {
                    name: "k".to_string(),
                    ty: TrustVcType::MathInt,
                },
            ],
            ty: seq_ty(),
        },
    };
    let eq = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(seq_var("a")),
        right: Box::new(right),
    };

    let encoded = {
        let mut parser = AstExpressionParser::new(
            &mut solver,
            &variables,
            &mut collection_lengths,
            &var_types,
            &functions,
        );
        parser
            .encode_subexpr(&eq)
            .expect("Seq == Seq should encode")
    };
    solver.format_term(encoded)
}

/// THE REGRESSION PIN. Structurally-reflexive `Seq == Seq` (two distinct IR
/// variables bound to one backing array) must emit NO quantifier at all: the
/// pointwise body folds to the constant `true`, and a `forall` over a `true`
/// body is pure waste.
#[test]
fn structurally_reflexive_seq_eq_emits_no_vacuous_quantifier() {
    let sexpr = encode_seq_eq_sexpr(Shape::AliasedSources);
    assert!(
        !sexpr.contains("forall"),
        "structurally-reflexive Seq == Seq must not emit a pointwise quantifier: \
         its body folds to the constant `true` (same backing array, same carrier \
         offset => both selects are the SAME hash-consed term), so the forall \
         says nothing. Got: {sexpr}"
    );
}

/// THE LOAD-BEARING-CONJUNCT PIN. Same aliased backing array, but reached
/// through a zero-offset `subrange(0, k)` so the LENGTH equality is genuine
/// information. Only the vacuous quantifier may be dropped — the length
/// equality must come through untouched.
#[test]
fn structurally_reflexive_seq_eq_keeps_its_length_equality() {
    let sexpr = encode_seq_eq_sexpr(Shape::AliasedViaZeroOffsetSubrange);
    assert!(
        !sexpr.contains("forall"),
        "a zero-offset subrange of the same backing array still folds its \
         pointwise body to `true` and must emit no quantifier. Got: {sexpr}"
    );
    assert!(
        sexpr.contains("seq_a_len") && sexpr.contains('k'),
        "the length equality `len(a) == k` is the load-bearing conjunct and must \
         survive the vacuous-quantifier guard — dropping it would weaken the \
         equality to nothing at all. Got: {sexpr}"
    );
    assert!(
        sexpr.starts_with("(="),
        "with the vacuous quantifier gone, the whole encoding IS the length \
         equality — no surviving `and` wrapper around a dropped conjunct. \
         Got: {sexpr}"
    );
}

/// THE NARROWNESS PIN. A genuine `Seq == Seq` over two DIFFERENT backing arrays
/// has a non-trivial pointwise body and MUST still emit its congruence
/// quantifier. Without this, the guard could degenerate into dropping real
/// element constraints and every collection-equality proof would silently
/// weaken to a bare length equality.
#[test]
fn must_still_emit_pointwise_forall_for_distinct_sources() {
    let sexpr = encode_seq_eq_sexpr(Shape::DistinctSources);
    assert!(
        sexpr.contains("forall"),
        "a genuine Seq == Seq over distinct backing arrays must keep its \
         pointwise element congruence — dropping it would weaken the equality \
         to a bare length equality. Got: {sexpr}"
    );
    assert!(
        sexpr.contains("select"),
        "the pointwise body must still read both operands. Got: {sexpr}"
    );
}
