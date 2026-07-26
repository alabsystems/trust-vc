//! #4 Native collection decision procedures (Seq / Set / Map / Multiset).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! # What this capability is
//!
//! Verus delegates collection reasoning (`Set`/`Seq`/`Map`/`Multiset`
//! membership, length, permutation, bag-count) to Z3, where it is encoded with
//! universally-quantified axioms and discharged by MBQI — a heuristic,
//! trigger-fragile, *incomplete* instantiation loop with no checkable artifact.
//! trust-vc instead lowers the same operations onto ay's native theory encoding
//! (Set/Map as extensional arrays `index -> {Bool, value}`, Seq as a length +
//! select model), so the verdict comes from a *decision procedure* on the array
//! and arithmetic theories rather than from quantifier guessing.
//!
//! This module is the front-end seam for that capability: small, total builders
//! that assemble collection-typed [`DriverFn`]s out of the stable
//! [`crate::lower`] vocabulary, plus the [`TrustVcExpr`] constructors for the
//! [`CollectionOp`] forms that the encoder discharges natively. Each builder is
//! a *shape*, not a proof: a false postcondition built with these helpers is
//! still refuted by the real backend (see `tests/collections.rs`), which is what
//! keeps the seam sound rather than a rubber stamp.
//!
//! # Encoding notes (why these shapes verify)
//!
//! * A `Set<T>` is the array `T -> Bool`; `insert(e)` is `store(set, e, true)`
//!   and `contains(e)` is `select(set, e)`. Hence `s.insert(e).contains(e)` is
//!   `select(store(s, e, true), e)`, which the array theory proves equal to
//!   `true` with **no quantifier instantiation**. For a *different*, symbolic
//!   element `d`, `select(store(s, e, true), d)` is `ite(d == e, true,
//!   select(s, d))` — not valid, so the backend *refutes* it with a witness
//!   (`d != e`, `d` originally absent).
//! * A `Map<K, V>` is the array `K -> V`; `insert(k, v).get(k)` reduces to
//!   `select(store(m, k, v), k) == v` by the array read-over-write axiom.
//! * `Seq<T>` carries a length model; `push(e)` increments it, so
//!   `s.push(e).len() == s.len() + 1`.
//!
//! These are exactly the facts a Z3-backed tool needs MBQI for; here they are
//! ground array/arithmetic obligations.

use trust_vc_core::ir::{CollectionOp, CompareOp, TrustVcExpr, TrustVcType};

use crate::lower::{Binding, DriverFn};

// ---------------------------------------------------------------------------
// Type builders.
// ---------------------------------------------------------------------------

/// `Seq<elem>` — an ordered, length-carrying sequence.
#[must_use]
pub fn seq_ty(elem: TrustVcType) -> TrustVcType {
    TrustVcType::Seq(Box::new(elem))
}

/// `Set<elem>` — an extensional set, encoded as `elem -> Bool`.
#[must_use]
pub fn set_ty(elem: TrustVcType) -> TrustVcType {
    TrustVcType::Set(Box::new(elem))
}

/// `Map<key, value>` — a total map, encoded as `key -> value` with a tracked
/// domain.
#[must_use]
pub fn map_ty(key: TrustVcType, value: TrustVcType) -> TrustVcType {
    TrustVcType::Map(Box::new(key), Box::new(value))
}

/// `Multiset<elem>` — a bag, encoded with per-element counts.
#[must_use]
pub fn multiset_ty(elem: TrustVcType) -> TrustVcType {
    TrustVcType::Multiset(Box::new(elem))
}

// ---------------------------------------------------------------------------
// Collection-op expression constructors.
//
// Every constructor carries the *result* type in `ty`, which is what the
// encoder dispatch and downstream width-coercion rely on. The `receiver_name`
// is threaded through whenever the receiver is a named variable, because the
// encoder keys length / domain metadata by that name for chained operations.
// ---------------------------------------------------------------------------

/// Pull the variable name out of a `Var` receiver, so the encoder can key its
/// collection metadata (length, domain) by name. `None` for anonymous
/// receivers (e.g. the result of a prior collection op).
fn receiver_name_of(expr: &TrustVcExpr) -> Option<String> {
    match expr {
        TrustVcExpr::Var { name, .. } => Some(name.clone()),
        _ => None,
    }
}

/// `receiver.len()` — the length of a `Seq`/`Set`/`Map`/`Multiset`, as a
/// `usize`-width unsigned integer (the pointer-width the encoder uses for
/// cardinalities).
#[must_use]
pub fn len(receiver: TrustVcExpr) -> TrustVcExpr {
    let receiver_name = receiver_name_of(&receiver);
    TrustVcExpr::CollectionOp {
        op: CollectionOp::Len,
        receiver: Box::new(receiver),
        receiver_name,
        args: vec![],
        ty: TrustVcType::Uint { width: 64 },
    }
}

/// `set.contains(elem)` / `seq.contains(elem)` — a `bool` membership test.
#[must_use]
pub fn contains(receiver: TrustVcExpr, elem: TrustVcExpr) -> TrustVcExpr {
    let receiver_name = receiver_name_of(&receiver);
    TrustVcExpr::CollectionOp {
        op: CollectionOp::Contains,
        receiver: Box::new(receiver),
        receiver_name,
        args: vec![elem],
        ty: TrustVcType::Bool,
    }
}

/// `set.insert(elem)` — the set with `elem` added. Result type mirrors the
/// receiver set type so chained ops resolve the element type.
#[must_use]
pub fn set_insert(receiver: TrustVcExpr, elem: TrustVcExpr, elem_ty: TrustVcType) -> TrustVcExpr {
    let receiver_name = receiver_name_of(&receiver);
    TrustVcExpr::CollectionOp {
        op: CollectionOp::Insert,
        receiver: Box::new(receiver),
        receiver_name,
        args: vec![elem],
        ty: set_ty(elem_ty),
    }
}

/// `seq.push(elem)` — the sequence with `elem` appended. Result type mirrors
/// the receiver seq type.
#[must_use]
pub fn seq_push(receiver: TrustVcExpr, elem: TrustVcExpr, elem_ty: TrustVcType) -> TrustVcExpr {
    let receiver_name = receiver_name_of(&receiver);
    TrustVcExpr::CollectionOp {
        op: CollectionOp::Push,
        receiver: Box::new(receiver),
        receiver_name,
        args: vec![elem],
        ty: seq_ty(elem_ty),
    }
}

/// `map.insert(key, value)` — the map with `key` bound to `value`. Result type
/// mirrors the receiver map type.
#[must_use]
pub fn map_insert(
    receiver: TrustVcExpr,
    key: TrustVcExpr,
    value: TrustVcExpr,
    key_ty: TrustVcType,
    value_ty: TrustVcType,
) -> TrustVcExpr {
    let receiver_name = receiver_name_of(&receiver);
    TrustVcExpr::CollectionOp {
        op: CollectionOp::Insert,
        receiver: Box::new(receiver),
        receiver_name,
        args: vec![key, value],
        ty: map_ty(key_ty, value_ty),
    }
}

/// `map.contains_key(key)` — a `bool` domain-membership test.
#[must_use]
pub fn map_contains_key(receiver: TrustVcExpr, key: TrustVcExpr) -> TrustVcExpr {
    let receiver_name = receiver_name_of(&receiver);
    TrustVcExpr::CollectionOp {
        op: CollectionOp::ContainsKey,
        receiver: Box::new(receiver),
        receiver_name,
        args: vec![key],
        ty: TrustVcType::Bool,
    }
}

/// `map.index(key)` / `map[key]` — the value bound to `key`, at `value_ty`.
///
/// Map value lookup is encoded via the [`TrustVcExpr::Index`] read of the
/// underlying `key -> value` array (the encoder's read-over-write reduces
/// `insert(k, v)[k]` to `v`).
#[must_use]
pub fn map_get(receiver: TrustVcExpr, key: TrustVcExpr, value_ty: TrustVcType) -> TrustVcExpr {
    let receiver_name = receiver_name_of(&receiver);
    TrustVcExpr::Index {
        receiver: Box::new(receiver),
        index: Box::new(key),
        receiver_name,
        elem_ty: value_ty,
    }
}

/// `multiset.count(elem)` — how many copies of `elem` the bag holds, as a
/// mathematical integer (`nat` in the count theory).
#[must_use]
pub fn multiset_count(receiver: TrustVcExpr, elem: TrustVcExpr) -> TrustVcExpr {
    let receiver_name = receiver_name_of(&receiver);
    TrustVcExpr::CollectionOp {
        op: CollectionOp::Count,
        receiver: Box::new(receiver),
        receiver_name,
        args: vec![elem],
        ty: TrustVcType::MathInt,
    }
}

// ---------------------------------------------------------------------------
// Boolean / comparison glue used to phrase collection postconditions.
// ---------------------------------------------------------------------------

/// `expr == true` — asserts a boolean collection query (e.g. a `contains`) is
/// true. Phrasing membership as an equality keeps it a first-class checked
/// assertion rather than a bare boolean term.
#[must_use]
pub fn is_true(expr: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(expr),
        right: Box::new(TrustVcExpr::BoolLit(true)),
    }
}

/// `expr == false` — asserts a boolean collection query is false.
#[must_use]
pub fn is_false(expr: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(expr),
        right: Box::new(TrustVcExpr::BoolLit(false)),
    }
}

/// A `Var` of the given collection type, named so the encoder tracks its
/// length / domain metadata.
#[must_use]
pub fn collection_var(name: &str, ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: name.to_string(),
        ty,
    }
}

// ---------------------------------------------------------------------------
// DriverFn assembly.
//
// A collection lemma is just a `DriverFn` whose return binding is the
// collection query result and whose single postcondition is the property we
// want the native decision procedure to settle.
// ---------------------------------------------------------------------------

/// Assemble a collection lemma: a function over `params` whose body produces
/// `body` into a `result` binding of `result_ty`, asserted to satisfy each
/// `ensures` postcondition (under the optional `requires` preconditions).
///
/// This is the collection-flavoured front door onto [`DriverFn`]; it exists so
/// tests (and the THIR walker, eventually) can phrase a Set/Seq/Map property
/// without restating the Hoare-encoding boilerplate.
#[must_use]
pub fn collection_lemma(
    name: &str,
    params: Vec<Binding>,
    result_ty: TrustVcType,
    body: TrustVcExpr,
    requires: Vec<TrustVcExpr>,
    ensures: Vec<TrustVcExpr>,
) -> DriverFn {
    DriverFn {
        name: name.to_string(),
        params,
        result: Binding::new("result", result_ty),
        requires,
        body_value: Some(body),
        ensures,
    }
}

/// The `result` variable that [`collection_lemma`] binds the body to, at the
/// given type. Use this in `ensures` to refer to the computed collection /
/// query value.
#[must_use]
pub fn result_var(ty: TrustVcType) -> TrustVcExpr {
    TrustVcExpr::Var {
        name: "result".to_string(),
        ty,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn type_builders_nest() {
        assert_eq!(
            seq_ty(TrustVcType::Uint { width: 32 }),
            TrustVcType::Seq(Box::new(TrustVcType::Uint { width: 32 }))
        );
        assert_eq!(
            map_ty(TrustVcType::Uint { width: 32 }, TrustVcType::Bool),
            TrustVcType::Map(
                Box::new(TrustVcType::Uint { width: 32 }),
                Box::new(TrustVcType::Bool)
            )
        );
    }

    #[test]
    fn contains_threads_receiver_name() {
        let s = collection_var("s", set_ty(TrustVcType::Uint { width: 32 }));
        let c = contains(
            s,
            TrustVcExpr::IntLit {
                value: 1,
                ty: TrustVcType::Uint { width: 32 },
            },
        );
        match c {
            TrustVcExpr::CollectionOp {
                op,
                receiver_name,
                ty,
                ..
            } => {
                assert_eq!(op, CollectionOp::Contains);
                assert_eq!(receiver_name.as_deref(), Some("s"));
                assert_eq!(ty, TrustVcType::Bool);
            }
            other => panic!("expected CollectionOp, got {other:?}"),
        }
    }

    #[test]
    fn lemma_binds_result_and_body() {
        let lemma = collection_lemma(
            "noop",
            vec![],
            TrustVcType::Bool,
            TrustVcExpr::BoolLit(true),
            vec![],
            vec![is_true(result_var(TrustVcType::Bool))],
        );
        assert_eq!(lemma.result.name, "result");
        assert!(lemma.body_value.is_some());
        assert_eq!(lemma.ensures.len(), 1);
    }
}
