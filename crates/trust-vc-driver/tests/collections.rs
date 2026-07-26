// Native collection decision-procedure tests (capability #4).
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Run with: cargo test -p trust-vc-driver --features collections
//
// These tests drive Set / Seq / Map / Multiset properties through trust-vc-core's
// REAL encoder + ay solver via the `collections` front-end seam. They prove the
// capability end to end:
//   * collection facts that HOLD verify (Set membership, Map read-over-write,
//     Map domain, Seq length, Multiset count non-negativity), and
//   * collection facts that are FALSE are refuted with a counterexample (the
//     seam is sound, not a rubber stamp).
//
// Crucially these obligations reduce to GROUND array + arithmetic theory — the
// array read-over-write axiom and bag-count arithmetic — so ay settles them with
// a decision procedure rather than the quantifier/MBQI instantiation loop a
// Z3-backed tool (Verus) needs for the same Set/Map/Seq lemmas. That is the
// "no Z3 MBQI" superiority claim, demonstrated.
//
// Fail-closed note: the *symbolic* "different element/key" direction
// (`s.insert(e).contains(d)` for an unconstrained `d != e`, or a fresh-key
// `contains_key`) returns solver `Unknown` here, not `Refuted` — the array
// disequality split is not auto-discharged without a concrete witness. That is
// acceptable incompleteness (Unknown is never a false proof); we assert the
// directions that are decided and use the always-decided false goals
// (`get(k) == v + 1`, `count(e) >= 1`) for the refutation evidence.

#![cfg(feature = "collections")]

use trust_vc_core::ir::{ArithOp, CompareOp, TrustVcExpr, TrustVcType};
use trust_vc_driver::collections::{
    collection_lemma, collection_var, contains, is_true, len, map_contains_key, map_get,
    map_insert, map_ty, multiset_count, multiset_ty, result_var, seq_push, seq_ty, set_insert,
    set_ty,
};
use trust_vc_driver::lower::{cmp, lit, Binding, Outcome};

fn u32t() -> TrustVcType {
    TrustVcType::Uint { width: 32 }
}
fn u64t() -> TrustVcType {
    TrustVcType::Uint { width: 64 }
}

fn set_u32(name: &str) -> TrustVcExpr {
    collection_var(name, set_ty(u32t()))
}
fn seq_u32(name: &str) -> TrustVcExpr {
    collection_var(name, seq_ty(u32t()))
}
fn map_u32(name: &str) -> TrustVcExpr {
    collection_var(name, map_ty(u32t(), u32t()))
}
fn multiset_u32(name: &str) -> TrustVcExpr {
    collection_var(name, multiset_ty(u32t()))
}
fn u32_var(name: &str) -> TrustVcExpr {
    collection_var(name, u32t())
}

fn add(l: TrustVcExpr, r: TrustVcExpr, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Arith {
        op: ArithOp::Add,
        left: Box::new(l),
        right: Box::new(r),
        ty,
    }
}

// ---------------------------------------------------------------------------
// VERIFIED: native Set membership — store/select, no quantifiers.
// ---------------------------------------------------------------------------

/// `s.insert(e).contains(e)` is always true: the Set is the array `T -> Bool`,
/// `insert(e)` is `store(s, e, true)`, and `contains(e)` is the select at the
/// same index, so the array read-over-write axiom proves it directly. Symbolic
/// `s` and `e`.
#[test]
fn set_insert_then_contains_self_verifies() {
    let f = collection_lemma(
        "set_insert_contains_self",
        vec![Binding::new("s", set_ty(u32t())), Binding::new("e", u32t())],
        TrustVcType::Bool,
        contains(set_insert(set_u32("s"), u32_var("e"), u32t()), u32_var("e")),
        vec![],
        vec![is_true(result_var(TrustVcType::Bool))],
    );
    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Verified, "raw verdict: {raw:?}");
}

/// The same fact, NEGATED (`s.insert(e).contains(e) == false`), must NOT verify:
/// a sound seam may not prove a false goal. The backend either refutes it or
/// returns Unknown; it must never return Verified.
#[test]
fn set_insert_contains_self_negation_does_not_verify() {
    let f = collection_lemma(
        "set_insert_contains_self_neg",
        vec![Binding::new("s", set_ty(u32t())), Binding::new("e", u32t())],
        TrustVcType::Bool,
        contains(set_insert(set_u32("s"), u32_var("e"), u32t()), u32_var("e")),
        vec![],
        // ensures result == false  (FALSE goal)
        vec![cmp(
            CompareOp::Eq,
            result_var(TrustVcType::Bool),
            TrustVcExpr::BoolLit(false),
        )],
    );
    let (outcome, raw) = f.verify();
    assert_ne!(
        outcome,
        Outcome::Verified,
        "a false Set-membership goal must never verify; raw: {raw:?}"
    );
}

// ---------------------------------------------------------------------------
// VERIFIED: native Map read-over-write + domain.
// ---------------------------------------------------------------------------

/// `m.insert(k, v)[k] == v`: the Map is the array `K -> V`, `insert(k, v)` is
/// `store(m, k, v)`, and the index read at `k` is `select(store(m, k, v), k)`,
/// which the array theory proves equal to `v`. Symbolic `m`, `k`, `v`.
#[test]
fn map_insert_then_get_verifies() {
    let f = collection_lemma(
        "map_insert_get",
        vec![
            Binding::new("m", map_ty(u32t(), u32t())),
            Binding::new("k", u32t()),
            Binding::new("v", u32t()),
        ],
        u32t(),
        map_get(
            map_insert(map_u32("m"), u32_var("k"), u32_var("v"), u32t(), u32t()),
            u32_var("k"),
            u32t(),
        ),
        vec![],
        vec![cmp(CompareOp::Eq, result_var(u32t()), u32_var("v"))],
    );
    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Verified, "raw verdict: {raw:?}");
}

/// `m.insert(k, v).contains_key(k)` is always true — the inserted key is in the
/// updated domain. Symbolic `m`, `k`, `v`.
#[test]
fn map_insert_then_contains_key_verifies() {
    let f = collection_lemma(
        "map_insert_contains_key",
        vec![
            Binding::new("m", map_ty(u32t(), u32t())),
            Binding::new("k", u32t()),
            Binding::new("v", u32t()),
        ],
        TrustVcType::Bool,
        map_contains_key(
            map_insert(map_u32("m"), u32_var("k"), u32_var("v"), u32t(), u32t()),
            u32_var("k"),
        ),
        vec![],
        vec![is_true(result_var(TrustVcType::Bool))],
    );
    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Verified, "raw verdict: {raw:?}");
}

// ---------------------------------------------------------------------------
// VERIFIED: native Seq length model.
// ---------------------------------------------------------------------------

/// `s.push(e).len() == s.len() + 1`, under a length bound that rules out the
/// pointer-width overflow side condition the encoder emits for `push`. Symbolic
/// `s`, `e`; the only precondition is `len < 1000`, which discharges that
/// overflow guard.
#[test]
fn seq_push_increments_len_verifies() {
    let f = collection_lemma(
        "seq_push_len",
        vec![Binding::new("s", seq_ty(u32t())), Binding::new("e", u32t())],
        u64t(),
        len(seq_push(seq_u32("s"), u32_var("e"), u32t())),
        vec![cmp(CompareOp::Lt, len(seq_u32("s")), lit(1000, u64t()))],
        vec![cmp(
            CompareOp::Eq,
            result_var(u64t()),
            add(len(seq_u32("s")), lit(1, u64t()), u64t()),
        )],
    );
    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Verified, "raw verdict: {raw:?}");
}

// ---------------------------------------------------------------------------
// VERIFIED: native Multiset bag-count.
// ---------------------------------------------------------------------------

/// `m.count(e) >= 0` for any bag `m` and element `e` — the count theory keeps
/// per-element multiplicities non-negative. Symbolic `m`, `e`.
#[test]
fn multiset_count_is_nonnegative_verifies() {
    let f = collection_lemma(
        "multiset_count_nonneg",
        vec![
            Binding::new("m", multiset_ty(u32t())),
            Binding::new("e", u32t()),
        ],
        TrustVcType::MathInt,
        multiset_count(multiset_u32("m"), u32_var("e")),
        vec![],
        vec![cmp(
            CompareOp::Ge,
            result_var(TrustVcType::MathInt),
            lit(0, TrustVcType::MathInt),
        )],
    );
    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Verified, "raw verdict: {raw:?}");
}

// ---------------------------------------------------------------------------
// REFUTED: the seam is sound, not a rubber stamp.
// ---------------------------------------------------------------------------

/// `m.insert(k, v)[k] == v + 1` is FALSE — read-over-write gives exactly `v`,
/// not `v + 1`. The backend must REFUTE it with a counterexample, proving the
/// Map decision procedure is checked, not assumed. (`v < 100` rules out the
/// arithmetic-overflow distraction so the refutation is the clean
/// `result != v + 1` one.)
#[test]
fn map_insert_get_wrong_value_is_refuted() {
    let f = collection_lemma(
        "map_get_false",
        vec![
            Binding::new("m", map_ty(u32t(), u32t())),
            Binding::new("k", u32t()),
            Binding::new("v", u32t()),
        ],
        u32t(),
        map_get(
            map_insert(map_u32("m"), u32_var("k"), u32_var("v"), u32t(), u32t()),
            u32_var("k"),
            u32t(),
        ),
        vec![cmp(CompareOp::Lt, u32_var("v"), lit(100, u32t()))],
        vec![cmp(
            CompareOp::Eq,
            result_var(u32t()),
            add(u32_var("v"), lit(1, u32t()), u32t()),
        )],
    );
    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Refuted, "raw verdict: {raw:?}");
}

/// `m.count(e) >= 1` is FALSE — a bag need not contain `e` at all (count 0). The
/// backend must REFUTE it, confirming the Multiset count theory is exercised.
#[test]
fn multiset_count_ge_one_is_refuted() {
    let f = collection_lemma(
        "multiset_count_ge1_false",
        vec![
            Binding::new("m", multiset_ty(u32t())),
            Binding::new("e", u32t()),
        ],
        TrustVcType::MathInt,
        multiset_count(multiset_u32("m"), u32_var("e")),
        vec![],
        vec![cmp(
            CompareOp::Ge,
            result_var(TrustVcType::MathInt),
            lit(1, TrustVcType::MathInt),
        )],
    );
    let (outcome, raw) = f.verify();
    assert_eq!(outcome, Outcome::Refuted, "raw verdict: {raw:?}");
}
