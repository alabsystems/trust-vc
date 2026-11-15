//! IR helpers for extensional equality / inequality macros.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Lowers `ext_eq!` / `ext_ne!` into ordinary `TrustVcExpr` formulas built from
//! existing collection operations. This keeps the encoder surface unchanged:
//! sequences compare length + indexed elements, sets compare membership for all
//! elements, and maps compare key membership plus values on present keys.

use std::collections::{HashMap, HashSet};

use crate::ir::{ArithOp, CollectionOp, TrustVcType};
use crate::ir_expr::{LogicOp, QuantifierKind, TrustVcExpr};
use crate::ir_expr_traversal::{
    fold_expr_children, fold_expr_scoped_children, free_root_names,
    free_root_names_with_initial_bound, ScopeAwareTrustVcExprFolder, TrustVcExprFolder,
};

pub(crate) const STRICT_EQ_FN: &str = "__trust_vc_strict_eq";

// Internal receiver marker: Map extensionality needs raw array select under an
// explicit domain guard, not user-facing Map::get side conditions. The `$`
// prefix keeps this impossible to collide with a Rust identifier.
pub(crate) const MAP_EXTENSIONAL_SELECT_RECEIVER: &str = "$trust_vc_map_extensional_select";

fn collection_receiver_name(expr: &TrustVcExpr) -> Option<String> {
    match expr {
        TrustVcExpr::Var { name, .. } => Some(name.clone()),
        TrustVcExpr::FnCall { name, args, .. } if args.is_empty() => Some(name.clone()),
        TrustVcExpr::CollectionOp {
            receiver_name,
            receiver,
            ..
        }
        | TrustVcExpr::Index {
            receiver_name,
            receiver,
            ..
        } => receiver_name
            .clone()
            .or_else(|| collection_receiver_name(receiver)),
        TrustVcExpr::Cast { expr, .. } => collection_receiver_name(expr),
        _ => None,
    }
}

fn collection_op_expr(
    op: CollectionOp,
    receiver: TrustVcExpr,
    args: Vec<TrustVcExpr>,
    ty: TrustVcType,
) -> TrustVcExpr {
    let receiver_name = collection_receiver_name(&receiver);
    crate::ir_builder::collection_op(op, receiver, receiver_name.as_deref(), args, ty)
}

fn map_extensional_select_expr(
    receiver: TrustVcExpr,
    key: TrustVcExpr,
    value_ty: TrustVcType,
) -> TrustVcExpr {
    crate::ir_builder::collection_op(
        CollectionOp::Get,
        receiver,
        Some(MAP_EXTENSIONAL_SELECT_RECEIVER),
        vec![key],
        value_ty,
    )
}

fn normalize_extensional_operand(expr: TrustVcExpr) -> (TrustVcExpr, TrustVcType) {
    let ty = crate::ir_lowering::infer_expr_type(&expr);
    match ty {
        TrustVcType::String | TrustVcType::StrSlice => {
            let Some(view_ty) = ty.view_collection_type() else {
                return (expr, ty);
            };
            (
                collection_op_expr(CollectionOp::View, expr, vec![], view_ty.clone()),
                view_ty,
            )
        }
        _ => (expr, ty),
    }
}

fn fresh_bound_name(base: &str, used_names: &mut HashSet<String>) -> String {
    if used_names.insert(base.to_string()) {
        return base.to_string();
    }

    for suffix in 1..=used_names.len().saturating_add(1) {
        let candidate = format!("{base}_{suffix}");
        if used_names.insert(candidate.clone()) {
            return candidate;
        }
    }

    let max_used_len = used_names
        .iter()
        .map(String::len)
        .max()
        .unwrap_or(base.len());
    let pad_len = max_used_len.saturating_sub(base.len()).saturating_add(1);
    let candidate = format!("{base}_{}", "_".repeat(pad_len));
    used_names.insert(candidate.clone());
    candidate
}

fn free_names_in_operands(lhs: &TrustVcExpr, rhs: &TrustVcExpr) -> HashSet<String> {
    let mut names = free_root_names(lhs);
    names.extend(free_root_names(rhs));
    names
}

/// Upper bound on the number of concrete element-equality conjuncts emitted by
/// the finite-length specialization below. Above this the symbolic FORALL form
/// is retained (its size is independent of the sequence length).
const SEQ_EXT_EQ_FINITE_UNROLL_CAP: usize = 64;

/// Extracts a non-negative integer literal value, seeing through a single
/// numeric `as` cast (e.g. `4usize`, `(3 as usize)`).
fn seq_static_int_literal(expr: &TrustVcExpr) -> Option<usize> {
    match expr {
        TrustVcExpr::IntLit { value, .. } => usize::try_from(*value).ok(),
        TrustVcExpr::Cast { expr, .. } => seq_static_int_literal(expr),
        _ => None,
    }
}

/// The statically-known length of a sequence-valued operand, when it can be
/// derived exactly from the operand's construction — `Seq::empty()`,
/// `push`/`add`/`concat` chains, `Seq::new(len, _)`, and concrete-bound
/// `subrange(a, b)` views over such sources. Returns `None` for symbolic
/// sequences (variables, unknown-length parameters), where the length cannot be
/// reduced to a constant.
///
/// This MUST agree exactly with the encoder's length semantics so the
/// finite-unrolled extensional equality below covers precisely the live index
/// range (`push` adds one, `subrange(a, b)` has length `b - a`, etc.).
pub(crate) fn seq_static_len(expr: &TrustVcExpr) -> Option<usize> {
    match expr {
        // `Seq::<T>::empty()` constructor.
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } if args.is_empty()
            && name.starts_with(crate::ir_lowering::COLLECTION_CONSTRUCTOR_PREFIX)
            && name.contains("Seq_")
            && name.ends_with("_empty")
            && matches!(return_ty, TrustVcType::Seq(_)) =>
        {
            Some(0)
        }
        // `Seq::new(len, gen)` / `Seq::from_fn(len, gen)` — length is the literal
        // first argument.
        TrustVcExpr::FnCall { name, args, .. }
            if name == crate::ir_lowering::SEQ_FROM_FN_BUILTIN && args.len() == 2 =>
        {
            seq_static_int_literal(&args[0])
        }
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Push,
            receiver,
            args,
            ty,
            ..
        } if args.len() == 1 && matches!(ty, TrustVcType::Seq(_)) => {
            seq_static_len(receiver)?.checked_add(1)
        }
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Add | CollectionOp::Concat,
            receiver,
            args,
            ty,
            ..
        } if args.len() == 1 && matches!(ty, TrustVcType::Seq(_)) => {
            seq_static_len(receiver)?.checked_add(seq_static_len(&args[0])?)
        }
        // `subrange(a, b)` over a known-length source has length `b - a`, valid
        // only when `a <= b <= len(source)` (otherwise the subrange bounds
        // obligation refutes; we fall back to the FORALL form there).
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Subrange,
            receiver,
            args,
            ty,
            ..
        } if args.len() == 2 && matches!(ty, TrustVcType::Seq(_)) => {
            let start = seq_static_int_literal(&args[0])?;
            let end = seq_static_int_literal(&args[1])?;
            let source_len = seq_static_len(receiver)?;
            (start <= end && end <= source_len).then(|| end - start)
        }
        TrustVcExpr::CollectionOp {
            op: CollectionOp::View,
            receiver,
            ..
        } => seq_static_len(receiver),
        TrustVcExpr::Cast {
            expr,
            to_ty: TrustVcType::Seq(_),
            ..
        } => seq_static_len(expr),
        _ => None,
    }
}

/// True when BOTH `lhs` and `rhs` are Seq expressions with a statically-known
/// length within the finite-unroll cap — i.e. [`build_seq_ext_eq`] would emit the
/// decided finite conjunction `lhs[0]==rhs[0] && … && lhs[n-1]==rhs[n-1]` (equal
/// lengths) or a concrete `len_eq` refutation (different lengths), NEVER a
/// symbolic pointwise quantifier.
///
/// The bare `Seq == Seq` compare path (`encode_seq_extensional_eq`) uses a
/// BV-companion quantifier form tuned for SYMBOLIC-length operands and
/// counterexample model validation; it does not unroll a concrete `Seq::new(n,·)`
/// / `push`-chain, so a provable equality between two structurally-distinct but
/// pointwise-equal concrete seqs (`Seq::new(5, |i| 10*i) == empty.push(0)…push(40)`)
/// stays `unknown`. When this returns `true`, the caller routes through
/// [`build_ext_eq_expr`] instead so the finite form decides it — matching the
/// `assert_seqs_equal!` (`ext_eq!`) path, which already unrolls and verifies.
/// Symbolic-length operands return `false` and keep the existing compare encoding
/// unchanged (no regression to the symbolic / counterexample paths).
pub(crate) fn seq_pair_is_finite_unrollable(lhs: &TrustVcExpr, rhs: &TrustVcExpr) -> bool {
    matches!(
        (seq_static_len(lhs), seq_static_len(rhs)),
        (Some(l), Some(r)) if l <= SEQ_EXT_EQ_FINITE_UNROLL_CAP && r <= SEQ_EXT_EQ_FINITE_UNROLL_CAP
    )
}

fn build_seq_ext_eq(lhs: TrustVcExpr, rhs: TrustVcExpr, elem_ty: TrustVcType) -> TrustVcExpr {
    let index_ty = TrustVcType::Uint {
        width: crate::ir::pointer_width(),
    };
    let len_ty = index_ty.clone();

    let lhs_len = collection_op_expr(CollectionOp::Len, lhs.clone(), vec![], len_ty.clone());
    let rhs_len = collection_op_expr(CollectionOp::Len, rhs.clone(), vec![], len_ty);
    let len_eq = crate::ir_builder::eq(lhs_len.clone(), rhs_len);

    // Finite-length specialization (offset-subrange / known-element source
    // soundness fix). When BOTH operands have the same statically-known concrete
    // length `n`, the universally-quantified body `forall i < n. lhs[i] == rhs[i]`
    // is logically equivalent to the finite conjunction `lhs[0] == rhs[0] && ...
    // && lhs[n-1] == rhs[n-1]`, since the index range is exactly `{0, .., n-1}`.
    //
    // We emit the finite form here because the SYMBOLIC quantifier is the source
    // of a soundness defect: `subrange(src, a, b).index(i)` for a SYMBOLIC `i` is
    // encoded through a fresh `__seq_shifted` array whose defining axiom
    // (`forall j. result[j] == src[j + a]`) the solver does not reliably
    // instantiate at the goal-quantifier's skolem index — leaving the body
    // under-constrained and letting the solver fabricate a model where a valid
    // equality is REFUTED (a false counterexample). At a CONCRETE index `k` the
    // same `.index(k)` read resolves directly (the subrange element law fires by
    // E-matching the axiom at the literal index), so the unrolled form is decided
    // soundly: a genuinely-different element (`subrange == [.., 99]`) still
    // refutes, and no false `Verified` is introduced because each conjunct is the
    // exact element equality the extensional definition requires.
    //
    // Scoped to equal concrete lengths only: a length mismatch falls through to
    // the FORALL form whose `len_eq` conjunct already refutes, and symbolic
    // lengths (e.g. `s[0..k] == t[0..k]`) keep the quantified form unchanged.
    if let (Some(lhs_n), Some(rhs_n)) = (seq_static_len(&lhs), seq_static_len(&rhs)) {
        if lhs_n == rhs_n && lhs_n <= SEQ_EXT_EQ_FINITE_UNROLL_CAP {
            let mut conjunction = len_eq;
            for k in 0..lhs_n {
                let idx = crate::ir_builder::int_lit(k as i128, index_ty.clone());
                let lhs_at = collection_op_expr(
                    CollectionOp::Get,
                    lhs.clone(),
                    vec![idx.clone()],
                    elem_ty.clone(),
                );
                let rhs_at =
                    collection_op_expr(CollectionOp::Get, rhs.clone(), vec![idx], elem_ty.clone());
                conjunction =
                    crate::ir_builder::and(conjunction, crate::ir_builder::eq(lhs_at, rhs_at));
            }
            return conjunction;
        }
    }

    let mut used_names = free_names_in_operands(&lhs, &rhs);
    let index_name = fresh_bound_name("__trust_vc_ext_seq_idx", &mut used_names);
    let index_var = crate::ir_builder::var(&index_name, index_ty.clone());

    let lhs_at = collection_op_expr(
        CollectionOp::Get,
        lhs,
        vec![index_var.clone()],
        elem_ty.clone(),
    );
    let rhs_at = collection_op_expr(CollectionOp::Get, rhs, vec![index_var.clone()], elem_ty);
    let in_bounds = crate::ir_builder::lt(index_var.clone(), lhs_len);
    let elem_eq = crate::ir_builder::eq(lhs_at, rhs_at);

    crate::ir_builder::and(
        len_eq,
        crate::ir_builder::forall(
            vec![(index_name, index_ty)],
            crate::ir_builder::implies(in_bounds, elem_eq),
            None,
        ),
    )
}

/// Peel `insert` / `remove` layers off a Set/Map operand and return the
/// innermost receiver (the base collection the modifications are applied to).
fn collection_chain_root(operand: &TrustVcExpr) -> &TrustVcExpr {
    match operand {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Insert | CollectionOp::Remove,
            receiver,
            ty: TrustVcType::Set(_) | TrustVcType::Map(_, _),
            ..
        } => collection_chain_root(receiver),
        _ => operand,
    }
}

/// True when the membership-law expansion (`set_membership_at` / `map_dom_at` /
/// `map_value_at`) should be applied to an `insert` / `remove` chain.
///
/// The expansion is the workaround for ay's symbolic-skolem read-over-write
/// incompleteness — ay can VALIDATE a model in which `select(store(a, x, _), e)`
/// and `select(a, e)` disagree when the read index `e` is the extensional FORALL
/// skolem and the store index `x` is symbolic. That only arises when the chain
/// is applied to a SYMBOLIC base array, i.e. a set/map VARIABLE. Restricting the
/// rewrite to variable-rooted chains targets exactly the defect while leaving
/// everything else on the EXACT, already-correct baseline path:
///
/// * CONCRETE constructor chains (`Set::empty().insert(1)…`) build a
///   fully-determined `store` chain the array theory decides directly; the
///   empty base's membership is NOT pinned to `false` by the structural rewrite
///   (a raw `contains(empty, e)` reads an unconstrained array), so expanding
///   them would risk a false `Verified`, and expanding a Map VALUE over an empty
///   base emits a `select` on the unconstrained empty data array that ay returns
///   Unknown on.
/// * Opaque op-results (`union` / `filter` / `map` / comprehension) carry their
///   own membership axioms over a fresh result array; leaving them raw preserves
///   their established behavior.
///
/// A bare variable operand (no `insert` / `remove`) expands to the raw
/// `contains` anyway, so this is behavior-preserving except where an
/// `insert` / `remove` chain sits on a symbolic base — the exact bug surface.
fn should_expand_membership(operand: &TrustVcExpr) -> bool {
    matches!(collection_chain_root(operand), TrustVcExpr::Var { .. })
}

/// Build the membership predicate `operand.contains(elem)` by structurally
/// expanding `insert` / `remove` layers into the EXACT set membership law:
///
/// * `contains(insert(base, x), e)  ==  (e == x) || contains(base, e)`
/// * `contains(remove(base, x), e)  ==  (e != x) && contains(base, e)`
///
/// and bottoming out at the raw `contains(base, elem)` once the variable base is
/// reached. Gated by `should_expand_membership`: only variable-rooted chains are
/// expanded; everything else (concrete constructors, opaque op-results) returns
/// the raw whole-operand `contains`, leaving the baseline encoding unchanged.
///
/// WHY this rewrite (soundness-preserving completeness fix): `insert` / `remove`
/// encode as array `store`, and `contains` as `select`. The extensional-equality
/// FORALL is discharged by SKOLEMIZING its element `e` to a fresh constant and
/// refuting the negated body. ay's array theory does not reliably apply the
/// read-over-write law to `select(store(base, x, _), e)` when the read index `e`
/// is that symbolic skolem and the store index `x` is symbolic — it can VALIDATE
/// a model that leaves the two reads independent, fabricating a counterexample
/// whose witness `e == x` contradicts a membership/value precondition that would
/// otherwise force equality (false counterexample). Expanding the store chain at
/// the IR level replaces `select(store_chain, e)` with `ite`/`||`/`&&` over the
/// concrete equality `e == x` and `select(base, e)`: the case split on `e == x`
/// is ordinary (decidable) integer-equality + EUF congruence reasoning — at
/// `e == x`, `select(base, e)` and `select(base, x)` are congruent, so the
/// ground precondition `select(base, x)` is consumed — and NO symbolic
/// read-over-write is required.
///
/// This is the TRUE membership law, never an assumed-equal shortcut: a
/// genuinely-different equality (no precondition forcing agreement, or a real
/// differing element) still refutes, because each side expands to its own honest
/// membership predicate.
fn set_membership_at(operand: &TrustVcExpr, elem: &TrustVcExpr) -> TrustVcExpr {
    let raw = || {
        collection_op_expr(
            CollectionOp::Contains,
            operand.clone(),
            vec![elem.clone()],
            TrustVcType::Bool,
        )
    };
    if !should_expand_membership(operand) {
        return raw();
    }
    match operand {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Insert,
            receiver,
            args,
            ty,
            ..
        } if matches!(ty, TrustVcType::Set(_)) && args.len() == 1 => crate::ir_builder::or(
            crate::ir_builder::eq(elem.clone(), args[0].clone()),
            set_membership_at(receiver, elem),
        ),
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Remove,
            receiver,
            args,
            ty,
            ..
        } if matches!(ty, TrustVcType::Set(_)) && args.len() == 1 => crate::ir_builder::and(
            crate::ir_builder::ne(elem.clone(), args[0].clone()),
            set_membership_at(receiver, elem),
        ),
        _ => raw(),
    }
}

/// Upper bound on the total number of `insert`-key membership conjuncts emitted
/// by the finite-set specialization below. Above this the symbolic FORALL form
/// is retained (its size is independent of the set's cardinality).
const SET_EXT_EQ_FINITE_MEMBERSHIP_CAP: usize = 64;

/// The exact inserted-element expressions of a CONCRETE finite set operand —
/// a `Set::<T>::empty().insert(e_1)…insert(e_n)` chain — innermost-first.
///
/// Returns `None` for any operand that is NOT a pure insert chain rooted at the
/// empty-set constructor: a set VARIABLE, an `Insert` on a symbolic base, a
/// `Remove` layer (whose post-removal membership is not simply its insert keys),
/// or an opaque op-result (`union` / `filter` / comprehension). Those keep the
/// symbolic FORALL membership form unchanged.
fn concrete_set_insert_chain(expr: &TrustVcExpr) -> Option<Vec<TrustVcExpr>> {
    match expr {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } if args.is_empty()
            && name.starts_with(crate::ir_lowering::COLLECTION_CONSTRUCTOR_PREFIX)
            && name.contains("Set_")
            && name.ends_with("_empty")
            && matches!(return_ty, TrustVcType::Set(_)) =>
        {
            Some(Vec::new())
        }
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Insert,
            receiver,
            args,
            ty,
            ..
        } if args.len() == 1 && matches!(ty, TrustVcType::Set(_)) => {
            let mut elems = concrete_set_insert_chain(receiver)?;
            elems.push(args[0].clone());
            Some(elems)
        }
        _ => None,
    }
}

/// Finite, skolem-free extensional equality for two CONCRETE set operands.
///
/// For finite sets `A == B` iff `A ⊆ B ∧ B ⊆ A`, and the elements of a pure
/// `empty().insert(..)` chain are exactly its insert keys. So the equality is the
/// element-wise two-way membership conjunction
/// `(⋀ a∈A. B.contains(a)) ∧ (⋀ b∈B. A.contains(b))` — BOTH inclusions, asserted
/// at the CONCRETE key expressions (no quantifier-bound element).
///
/// WHY this form (soundness-preserving completeness fix): the symbolic FORALL
/// membership encoding skolemizes the bound element to a fresh unconstrained
/// integer; ay's array theory then fails to refute the negated goal for an
/// `Int`-indexed (`Set<int>`) membership array — it can VALIDATE a model in which
/// the skolem read disagrees with the const-array empty base, so a genuinely
/// strict-superset equality `{1,2} == {1}` was unsoundly `Verified`. Replacing the
/// skolem read with membership at the concrete insert keys keeps every `contains`
/// a literal-index array `select`, which the array + EUF layers decide directly
/// (a differing element still refutes; an equal set still verifies), matching the
/// `nat`/`i32`/`usize` element variants that were already sound.
fn build_finite_set_membership_eq(
    lhs: &TrustVcExpr,
    rhs: &TrustVcExpr,
    lhs_elems: &[TrustVcExpr],
    rhs_elems: &[TrustVcExpr],
) -> TrustVcExpr {
    let mut conjunction = crate::ir_builder::bool_lit(true);
    for elem in lhs_elems {
        let rhs_has = collection_op_expr(
            CollectionOp::Contains,
            rhs.clone(),
            vec![elem.clone()],
            TrustVcType::Bool,
        );
        conjunction = crate::ir_builder::and(conjunction, rhs_has);
    }
    for elem in rhs_elems {
        let lhs_has = collection_op_expr(
            CollectionOp::Contains,
            lhs.clone(),
            vec![elem.clone()],
            TrustVcType::Bool,
        );
        conjunction = crate::ir_builder::and(conjunction, lhs_has);
    }
    conjunction
}

fn build_set_ext_eq(lhs: TrustVcExpr, rhs: TrustVcExpr, elem_ty: TrustVcType) -> TrustVcExpr {
    // Finite-set specialization (Int-indexed-array soundness fix). When BOTH
    // operands are concrete `empty().insert(..)` chains, emit the skolem-free
    // two-way membership conjunction instead of the universally-quantified
    // membership biconditional, whose skolemized read is mis-decided by ay's
    // array theory for `Set<int>` (a strict-superset `{1,2} == {1}` was a false
    // `Verified`). Logically equivalent for finite sets and decided directly by
    // the array + EUF layers at the concrete insert keys.
    if let (Some(lhs_elems), Some(rhs_elems)) = (
        concrete_set_insert_chain(&lhs),
        concrete_set_insert_chain(&rhs),
    ) {
        if lhs_elems.len() + rhs_elems.len() <= SET_EXT_EQ_FINITE_MEMBERSHIP_CAP {
            return build_finite_set_membership_eq(&lhs, &rhs, &lhs_elems, &rhs_elems);
        }
    }

    let mut used_names = free_names_in_operands(&lhs, &rhs);
    let elem_name = fresh_bound_name("__trust_vc_ext_set_elem", &mut used_names);
    let elem_var = crate::ir_builder::var(&elem_name, elem_ty.clone());
    let lhs_has = set_membership_at(&lhs, &elem_var);
    let rhs_has = set_membership_at(&rhs, &elem_var);

    crate::ir_builder::forall(
        vec![(elem_name, elem_ty)],
        crate::ir_builder::eq(lhs_has, rhs_has),
        None,
    )
}

fn build_multiset_ext_eq(lhs: TrustVcExpr, rhs: TrustVcExpr, elem_ty: TrustVcType) -> TrustVcExpr {
    // A pure empty().insert(..) chain has finite support consisting exactly of
    // its inserted key expressions. Two such multisets are equal iff their
    // counts agree at every key in the union of those supports; outside that
    // union both empty-rooted count arrays are zero. Emit that exact finite
    // conjunction when the support is small enough, avoiding an unhandled
    // triggerless FORALL over a type parameter while preserving multiplicities.
    if let (Some(lhs_elems), Some(rhs_elems)) = (
        concrete_multiset_insert_chain(&lhs, &elem_ty),
        concrete_multiset_insert_chain(&rhs, &elem_ty),
    ) {
        if lhs_elems.len() + rhs_elems.len() <= MULTISET_EXT_EQ_FINITE_SUPPORT_CAP {
            let mut support = Vec::with_capacity(lhs_elems.len() + rhs_elems.len());
            for elem in lhs_elems.iter().chain(&rhs_elems) {
                if !support.contains(elem) {
                    support.push(elem.clone());
                }
            }
            return support.into_iter().fold(
                crate::ir_builder::bool_lit(true),
                |conjunction, elem| {
                    let lhs_count = collection_op_expr(
                        CollectionOp::Count,
                        lhs.clone(),
                        vec![elem.clone()],
                        TrustVcType::Nat,
                    );
                    let rhs_count = collection_op_expr(
                        CollectionOp::Count,
                        rhs.clone(),
                        vec![elem],
                        TrustVcType::Nat,
                    );
                    crate::ir_builder::and(conjunction, crate::ir_builder::eq(lhs_count, rhs_count))
                },
            );
        }
    }

    let mut used_names = free_names_in_operands(&lhs, &rhs);
    let elem_name = fresh_bound_name("__trust_vc_ext_multiset_elem", &mut used_names);
    let elem_var = crate::ir_builder::var(&elem_name, elem_ty.clone());
    let count_ty = TrustVcType::Nat;

    let lhs_count = collection_op_expr(
        CollectionOp::Count,
        lhs,
        vec![elem_var.clone()],
        count_ty.clone(),
    );
    let rhs_count = collection_op_expr(CollectionOp::Count, rhs, vec![elem_var], count_ty);

    crate::ir_builder::forall(
        vec![(elem_name, elem_ty)],
        crate::ir_builder::eq(lhs_count, rhs_count),
        None,
    )
}

/// Maximum total insert-chain length admitted to finite multiset
/// extensionality. Above this, or for any non-empty-rooted/symbolic operand, the
/// existing quantified formula remains the fail-closed fallback.
const MULTISET_EXT_EQ_FINITE_SUPPORT_CAP: usize = 64;

/// Exact inserted-key sequence for a concrete finite multiset. Duplicate keys
/// are intentionally retained here because each insertion contributes one to
/// multiplicity; only the later comparison support is structurally deduplicated.
fn concrete_multiset_insert_chain(
    expr: &TrustVcExpr,
    elem_ty: &TrustVcType,
) -> Option<Vec<TrustVcExpr>> {
    // `build_ext_eq_expr` establishes equal top-level operand types, but this
    // helper also validates every nested constructor, insert result, and key.
    // That makes the finite-support rule fail closed for malformed hand-built
    // IR instead of mixing counts from different Multiset element sorts.
    let multiset_ty = TrustVcType::Multiset(Box::new(elem_ty.clone()));
    let mut cursor = expr;
    let mut reversed_elems = Vec::new();
    loop {
        match cursor {
            TrustVcExpr::FnCall {
                name,
                args,
                return_ty,
            } if args.is_empty()
                && name.starts_with(crate::ir_lowering::COLLECTION_CONSTRUCTOR_PREFIX)
                && name.ends_with("_empty")
                && return_ty == &multiset_ty =>
            {
                reversed_elems.reverse();
                return Some(reversed_elems);
            }
            TrustVcExpr::CollectionOp {
                op: CollectionOp::Insert,
                receiver,
                args,
                ty,
                ..
            } if args.len() == 1
                && ty == &multiset_ty
                && crate::ir_lowering::infer_expr_type(receiver) == multiset_ty
                && crate::ir_lowering::infer_expr_type(&args[0]) == *elem_ty =>
            {
                // Enforce the resource cap during recognition, before walking
                // or allocating for an arbitrarily deep hostile IR chain.
                if reversed_elems.len() == MULTISET_EXT_EQ_FINITE_SUPPORT_CAP {
                    return None;
                }
                reversed_elems.push(args[0].clone());
                cursor = receiver;
            }
            _ => return None,
        }
    }
}

/// Build the domain predicate `operand.contains_key(key)` by structurally
/// expanding `insert` / `remove` layers into the EXACT Map domain law (the Map
/// analogue of `set_membership_at`):
///
/// * `contains_key(insert(base, k, _), e)  ==  (e == k) || contains_key(base, e)`
/// * `contains_key(remove(base, k), e)     ==  (e != k) && contains_key(base, e)`
///
/// and bottoming out at the raw `contains_key` once the variable base is
/// reached (gated by `should_expand_membership`, like `set_membership_at`). Same
/// soundness/completeness rationale: it eliminates the symbolic-skolem
/// `select(store_chain, key)` over the domain array.
fn map_dom_at(operand: &TrustVcExpr, key: &TrustVcExpr) -> TrustVcExpr {
    let raw = || {
        collection_op_expr(
            CollectionOp::ContainsKey,
            operand.clone(),
            vec![key.clone()],
            TrustVcType::Bool,
        )
    };
    if !should_expand_membership(operand) {
        return raw();
    }
    match operand {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Insert,
            receiver,
            args,
            ty,
            ..
        } if matches!(ty, TrustVcType::Map(_, _)) && args.len() == 2 => crate::ir_builder::or(
            crate::ir_builder::eq(key.clone(), args[0].clone()),
            map_dom_at(receiver, key),
        ),
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Remove,
            receiver,
            args,
            ty,
            ..
        } if matches!(ty, TrustVcType::Map(_, _)) && args.len() == 1 => crate::ir_builder::and(
            crate::ir_builder::ne(key.clone(), args[0].clone()),
            map_dom_at(receiver, key),
        ),
        _ => raw(),
    }
}

/// Build the value projection `operand[key]` (the domain-guarded select used by
/// Map extensionality) by structurally expanding `insert` / `remove` layers into
/// the EXACT Map value law:
///
/// * `value(insert(base, k, v), e)  ==  ite(e == k, v, value(base, e))`
/// * `value(remove(base, k), e)     ==  value(base, e)`  (remove leaves the data
///   array unchanged; the removed key drops out of the domain, so its value is
///   only ever read under a `false` domain guard)
///
/// bottoming out at the raw extensional select (`MAP_EXTENSIONAL_SELECT_RECEIVER`,
/// which guards against leaking `Map::get`'s public precondition) once the
/// variable base is reached. Gated by `should_expand_membership`: a non-variable
/// root (concrete constructor / opaque op-result) returns the raw whole-operand
/// select unchanged — which also avoids emitting a `select` on an unconstrained
/// empty-map data array (an ay Unknown).
fn map_value_at(operand: &TrustVcExpr, key: &TrustVcExpr, value_ty: &TrustVcType) -> TrustVcExpr {
    if !should_expand_membership(operand) {
        return map_extensional_select_expr(operand.clone(), key.clone(), value_ty.clone());
    }
    match operand {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Insert,
            receiver,
            args,
            ty,
            ..
        } if matches!(ty, TrustVcType::Map(_, _)) && args.len() == 2 => crate::ir_builder::ite(
            crate::ir_builder::eq(key.clone(), args[0].clone()),
            args[1].clone(),
            map_value_at(receiver, key, value_ty),
            value_ty.clone(),
        ),
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Remove,
            receiver,
            args,
            ty,
            ..
        } if matches!(ty, TrustVcType::Map(_, _)) && args.len() == 1 => {
            map_value_at(receiver, key, value_ty)
        }
        _ => map_extensional_select_expr(operand.clone(), key.clone(), value_ty.clone()),
    }
}

/// Cap on the combined concrete-key count for the finite-map specialization
/// below; above it the symbolic FORALL form is retained (mirrors
/// `SET_EXT_EQ_FINITE_MEMBERSHIP_CAP`).
const MAP_EXT_EQ_FINITE_MEMBERSHIP_CAP: usize = 64;

/// The inserted KEY expressions of a CONCRETE finite map operand — a
/// `Map::<K,V>::empty().insert(k_1,v_1)…insert(k_n,v_n)` chain — innermost-first.
///
/// Returns `None` for any operand that is NOT a pure insert chain rooted at the
/// empty-map constructor (a map VARIABLE, an `insert`/`remove` on a symbolic
/// base, an opaque op-result). Those keep the symbolic FORALL form. `remove`
/// layers return `None` — like the set analogue, post-removal domain is not
/// simply the insert keys.
fn concrete_map_insert_chain(expr: &TrustVcExpr) -> Option<Vec<TrustVcExpr>> {
    match expr {
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } if args.is_empty()
            && name.starts_with(crate::ir_lowering::COLLECTION_CONSTRUCTOR_PREFIX)
            && name.contains("Map_")
            && name.ends_with("_empty")
            && matches!(return_ty, TrustVcType::Map(_, _)) =>
        {
            Some(Vec::new())
        }
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Insert,
            receiver,
            args,
            ty,
            ..
        } if args.len() == 2 && matches!(ty, TrustVcType::Map(_, _)) => {
            let mut keys = concrete_map_insert_chain(receiver)?;
            keys.push(args[0].clone());
            Some(keys)
        }
        _ => None,
    }
}

/// Finite, skolem-free extensional equality for two CONCRETE map operands.
///
/// Two maps are equal iff they agree on domain membership at every key AND on the
/// value at every key in the (shared) domain. For a pure `empty().insert(..)`
/// chain the ONLY keys at which either map can be present are its insert keys, so
/// the equality is fully decided by the per-key domain+value conjunction over the
/// UNION of both operands' insert keys `K`: for every `k ∈ K`,
/// `(dom_l(k) == dom_r(k)) ∧ (dom_l(k) ⟹ val_l(k) == val_r(k))`. Every key outside
/// `K` is absent in both maps (the `const-array(false)` empty base), so it agrees
/// trivially and need not be asserted — hence this is logically EQUIVALENT to the
/// symbolic-key FORALL body, not a strengthening.
///
/// WHY (soundness-preserving completeness fix, mirroring
/// `build_finite_set_membership_eq`): the symbolic-key FORALL skolemizes `k` to a
/// fresh index; refuting the `==` then needs `select(store_chain, k)` decided at a
/// SYMBOLIC `k`, which ay does not case-split onto the store support, so a genuine
/// counterexample (e.g. `empty.insert(5,_) == empty.insert(6,_)`) stalls to
/// `unknown`. Instantiating the body at the CONCRETE insert keys keeps every read
/// a literal-index `select` that ROW reduces directly (a differing map still
/// refutes; an equal map still verifies).
fn build_finite_map_membership_eq(
    lhs: &TrustVcExpr,
    rhs: &TrustVcExpr,
    keys: &[TrustVcExpr],
    value_ty: &TrustVcType,
) -> TrustVcExpr {
    let mut conjunction = crate::ir_builder::bool_lit(true);
    for key in keys {
        let lhs_has = map_dom_at(lhs, key);
        let rhs_has = map_dom_at(rhs, key);
        let lhs_value = map_value_at(lhs, key, value_ty);
        let rhs_value = map_value_at(rhs, key, value_ty);
        let per_key = crate::ir_builder::and(
            crate::ir_builder::eq(lhs_has.clone(), rhs_has),
            crate::ir_builder::implies(lhs_has, crate::ir_builder::eq(lhs_value, rhs_value)),
        );
        conjunction = crate::ir_builder::and(conjunction, per_key);
    }
    conjunction
}

/// The keys at which a CONCRETE map operand can be present: the insert keys of a
/// `Map::<K,V>::empty().insert(k,v)…` chain (`concrete_map_insert_chain`), or the
/// inserted elements of the concrete `Set::<K>::empty().insert(k)…` chain that a
/// `Set::mk_map(f)` is built over — `dom(S.mk_map(f)) == S` exactly, and the
/// elements of a pure insert chain are exactly its insert keys.
///
/// `None` for anything else (a map/set VARIABLE anywhere in the chain, `remove`,
/// an opaque op-result such as `filter`/`union`), which keeps the symbolic FORALL.
///
/// WHY the `mk_map` arm (soundness-preserving completeness fix, 2026-09-13): the
/// maps.rs `test1_fails2` refutation — `strict_eq!(S1.mk_map(k→10k),
/// S2.mk_map(k→11k))` over two three-element literal sets — timed out (30 s wall,
/// repeated across the retry cascade: the whole suite took 393 s). The strict-eq
/// extensionality bridge `ext_eq(a,b) ⟹ a == b` built its premise in the
/// symbolic-key FORALL form, and the bisected query showed ay 0.26.0 deciding the
/// bare negated store-chain equality in 16 ms and the same query WITHOUT that
/// bridge in 298 ms, but the skolemized bridge together with the `__set_len_insert`
/// cardinality chains came back `incomplete` (5 s) / timeout. The per-key form is
/// ground (every read a literal-index `select`, every value the closure body at a
/// literal key), so the premise is decided outright — here to FALSE, which leaves
/// the bridge vacuous and the raw `==` refuted with a countermodel.
fn concrete_finite_map_keys(expr: &TrustVcExpr) -> Option<Vec<TrustVcExpr>> {
    if let Some(keys) = concrete_map_insert_chain(expr) {
        return Some(keys);
    }
    match expr {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::SetMkMap,
            receiver,
            args,
            ty,
            ..
        } if args.len() == 1 && matches!(ty, TrustVcType::Map(_, _)) => {
            concrete_set_insert_chain(receiver)
        }
        _ => None,
    }
}

fn build_map_ext_eq(
    lhs: TrustVcExpr,
    rhs: TrustVcExpr,
    key_ty: TrustVcType,
    value_ty: TrustVcType,
) -> TrustVcExpr {
    // Finite-map specialization (mirrors the finite-set fix). When BOTH operands
    // are concrete — `empty().insert(..)` chains, or `mk_map` over a concrete
    // `Set::empty().insert(..)` chain (`concrete_finite_map_keys`) — decide
    // equality by the per-key domain+value conjunction over the union of the
    // concrete keys instead of the symbolic-key FORALL, whose skolemized
    // store-chain read ay cannot case-split onto the store support (a genuine CE
    // stalls to `unknown`).
    // Logically equivalent for concrete maps; every read is a literal-index select.
    if let (Some(lhs_keys), Some(rhs_keys)) = (
        concrete_finite_map_keys(&lhs),
        concrete_finite_map_keys(&rhs),
    ) {
        if lhs_keys.len() + rhs_keys.len() <= MAP_EXT_EQ_FINITE_MEMBERSHIP_CAP {
            let mut keys = lhs_keys;
            keys.extend(rhs_keys);
            return build_finite_map_membership_eq(&lhs, &rhs, &keys, &value_ty);
        }
    }

    let mut used_names = free_names_in_operands(&lhs, &rhs);
    let key_name = fresh_bound_name("__trust_vc_ext_map_key", &mut used_names);
    let key_var = crate::ir_builder::var(&key_name, key_ty.clone());

    let lhs_has = map_dom_at(&lhs, &key_var);
    let rhs_has = map_dom_at(&rhs, &key_var);
    let lhs_has_for_values = lhs_has.clone();

    let lhs_value = map_value_at(&lhs, &key_var, &value_ty);
    let rhs_value = map_value_at(&rhs, &key_var, &value_ty);

    crate::ir_builder::forall(
        vec![(key_name, key_ty)],
        crate::ir_builder::and(
            crate::ir_builder::eq(lhs_has, rhs_has),
            crate::ir_builder::implies(
                lhs_has_for_values,
                crate::ir_builder::eq(lhs_value, rhs_value),
            ),
        ),
        None,
    )
}

fn substitute_free_vars(expr: &TrustVcExpr, subst: &HashMap<String, TrustVcExpr>) -> TrustVcExpr {
    struct Substitutor<'a> {
        subst: &'a HashMap<String, TrustVcExpr>,
    }

    impl ScopeAwareTrustVcExprFolder for Substitutor<'_> {
        fn fold_expr_scoped(&mut self, expr: TrustVcExpr, bound: &HashSet<&str>) -> TrustVcExpr {
            match expr {
                TrustVcExpr::Var { ref name, ref ty } if !bound.contains(name.as_str()) => {
                    match self.subst.get(name) {
                        Some(replacement) => {
                            crate::ir_lowering::pin_substituted_value(ty, replacement)
                        }
                        None => expr,
                    }
                }
                other => fold_expr_scoped_children(self, other, bound),
            }
        }
    }

    Substitutor { subst }.fold_expr_scoped(expr.clone(), &HashSet::new())
}

fn spec_fn_operand_matches(expr: &TrustVcExpr, arg_tys: &[TrustVcType]) -> bool {
    match expr {
        TrustVcExpr::SpecClosure { params, .. } => {
            params.len() == arg_tys.len()
                && params
                    .iter()
                    .zip(arg_tys)
                    .all(|((_, param_ty), arg_ty)| param_ty == arg_ty)
        }
        _ => true,
    }
}

fn collect_spec_fn_operand_free_names(expr: &TrustVcExpr, names: &mut HashSet<String>) {
    match expr {
        TrustVcExpr::SpecClosure { params, body, .. } => {
            let bound: HashSet<&str> = params.iter().map(|(name, _)| name.as_str()).collect();
            names.extend(free_root_names_with_initial_bound(body, &bound));
        }
        other => names.extend(free_root_names(other)),
    }
}

fn instantiate_spec_fn_operand(
    expr: TrustVcExpr,
    arg_tys: &[TrustVcType],
    arg_exprs: &[TrustVcExpr],
    ret_ty: &TrustVcType,
) -> TrustVcExpr {
    match expr {
        TrustVcExpr::SpecClosure { params, body, .. } => {
            let subst = params
                .into_iter()
                .zip(arg_exprs.iter().cloned())
                .map(|((name, _), arg)| (name, arg))
                .collect();
            substitute_free_vars(&body, &subst)
        }
        other => {
            crate::ir_builder::spec_fn_apply(other, arg_tys, arg_exprs.to_vec(), ret_ty.clone())
        }
    }
}

fn is_internal_spec_fn_apply_call(
    name: &str,
    args: &[TrustVcExpr],
    return_ty: &TrustVcType,
) -> bool {
    let Some((function, application_args)) = args.split_first() else {
        return false;
    };
    let TrustVcType::SpecFn(param_tys, declared_return_ty) =
        crate::ir_lowering::infer_expr_type(function)
    else {
        return false;
    };
    application_args.len() == param_tys.len()
        && declared_return_ty.as_ref() == return_ty
        && name == crate::ir_builder::spec_fn_apply_symbol(&param_tys, return_ty)
}

fn normalize_spec_fn_apply_args(expr: TrustVcExpr) -> TrustVcExpr {
    struct ApplyArgNormalizer;

    impl TrustVcExprFolder for ApplyArgNormalizer {
        fn fold_expr(&mut self, expr: TrustVcExpr) -> TrustVcExpr {
            match expr {
                TrustVcExpr::FnCall {
                    name,
                    args,
                    return_ty,
                } if is_internal_spec_fn_apply_call(&name, &args, &return_ty) => {
                    let mut normalized_args = Vec::with_capacity(args.len());
                    let mut args = args.into_iter();
                    if let Some(function_arg) = args.next() {
                        normalized_args.push(self.fold_expr(function_arg));
                    }
                    normalized_args.extend(args.map(|arg| {
                        let folded = self.fold_expr(arg);
                        crate::encoder::normalize_int_expr(&folded)
                    }));

                    TrustVcExpr::FnCall {
                        name,
                        args: normalized_args,
                        return_ty,
                    }
                }
                other => fold_expr_children(self, other),
            }
        }
    }

    ApplyArgNormalizer.fold_expr(expr)
}

fn build_spec_fn_ext_eq(
    lhs: TrustVcExpr,
    rhs: TrustVcExpr,
    arg_tys: Vec<TrustVcType>,
    ret_ty: TrustVcType,
) -> TrustVcExpr {
    if !spec_fn_operand_matches(&lhs, &arg_tys) || !spec_fn_operand_matches(&rhs, &arg_tys) {
        return crate::ir_builder::eq(lhs, rhs);
    }

    let mut used_names = HashSet::new();
    collect_spec_fn_operand_free_names(&lhs, &mut used_names);
    collect_spec_fn_operand_free_names(&rhs, &mut used_names);

    let mut bound_vars = Vec::with_capacity(arg_tys.len());
    let mut arg_exprs = Vec::with_capacity(arg_tys.len());
    for (idx, arg_ty) in arg_tys.iter().cloned().enumerate() {
        let bound_name =
            fresh_bound_name(&format!("__trust_vc_ext_spec_arg{idx}"), &mut used_names);
        arg_exprs.push(crate::ir_builder::var(&bound_name, arg_ty.clone()));
        bound_vars.push((bound_name, arg_ty));
    }

    let lhs_body = normalize_spec_fn_apply_args(instantiate_spec_fn_operand(
        lhs, &arg_tys, &arg_exprs, &ret_ty,
    ));
    let rhs_body = normalize_spec_fn_apply_args(instantiate_spec_fn_operand(
        rhs, &arg_tys, &arg_exprs, &ret_ty,
    ));

    crate::ir_builder::forall(bound_vars, build_ext_eq_expr(lhs_body, rhs_body), None)
}

fn strict_set_mk_map_parts(
    expr: &TrustVcExpr,
) -> Option<(&TrustVcExpr, &[TrustVcExpr], &TrustVcType)> {
    match expr {
        TrustVcExpr::CollectionOp {
            op: CollectionOp::SetMkMap,
            receiver,
            args,
            ty,
            ..
        } if matches!(ty, TrustVcType::Map(_, _)) && args.len() == 1 => {
            Some((receiver.as_ref(), args.as_slice(), ty))
        }
        _ => None,
    }
}

fn value_fits_int_lit_type(value: i128, ty: &TrustVcType) -> bool {
    match ty {
        TrustVcType::MathInt => true,
        TrustVcType::Int { width } if (1..128).contains(width) => {
            let min = -(1i128 << (*width - 1));
            let max = (1i128 << (*width - 1)) - 1;
            min <= value && value <= max
        }
        TrustVcType::Int { width: 128 } => true,
        TrustVcType::Uint { width } if *width < 128 => {
            0 <= value && value <= ((1i128 << *width) - 1)
        }
        TrustVcType::Uint { width: 128 } => 0 <= value,
        _ => false,
    }
}

/// An integer literal — a bare `IntLit`, or one pinned at its type by an
/// identity cast (a source `4i32`, `ir_lowering::atoms::typed_int_literal`):
/// `(value, type, pinned)`.
fn strict_int_literal(expr: &TrustVcExpr) -> Option<(i128, &TrustVcType, bool)> {
    match expr {
        TrustVcExpr::IntLit { value, ty } => Some((*value, ty, false)),
        TrustVcExpr::Cast {
            expr,
            from_ty,
            to_ty,
        } if from_ty == to_ty => match expr.as_ref() {
            TrustVcExpr::IntLit { value, ty } if ty == to_ty => Some((*value, ty, true)),
            _ => None,
        },
        _ => None,
    }
}

/// The folded literal, pinned again when an operand was (`2i32 + 2i32` folds
/// to the `4i32` a source `4i32` lowers to, never to a bare placeholder).
fn strict_folded_int_literal(value: i128, ty: TrustVcType, pinned: bool) -> TrustVcExpr {
    let literal = TrustVcExpr::IntLit {
        value,
        ty: ty.clone(),
    };
    if pinned {
        TrustVcExpr::Cast {
            expr: Box::new(literal),
            from_ty: ty.clone(),
            to_ty: ty,
        }
    } else {
        literal
    }
}

fn fold_strict_local_int_constants(expr: TrustVcExpr) -> TrustVcExpr {
    struct LocalIntFolder;

    impl TrustVcExprFolder for LocalIntFolder {
        fn fold_expr(&mut self, expr: TrustVcExpr) -> TrustVcExpr {
            match expr {
                TrustVcExpr::Arith {
                    op,
                    left,
                    right,
                    ty,
                } => {
                    let left = self.fold_expr(*left);
                    let right = self.fold_expr(*right);
                    if let (
                        Some((left_value, left_ty, left_pinned)),
                        Some((right_value, right_ty, right_pinned)),
                    ) = (strict_int_literal(&left), strict_int_literal(&right))
                    {
                        let (left_value, right_value) = (&left_value, &right_value);
                        // A closed tree of UNSUFFIXED literals has no value of
                        // its own: its literals are typed by the peer it meets
                        // (design-trust-proof-backend.md §5b rule 2) — `x +
                        // (200 + 100)` with `x: u8` is `u8` arithmetic (44),
                        // not `x + 300`. It folds only to a value every type
                        // it may take agrees on (`2 + 2` is 4 in all of them).
                        let typed =
                            ty != TrustVcType::Int { width: 32 } || left_pinned || right_pinned;
                        if !typed {
                            let tree = TrustVcExpr::Arith {
                                op,
                                left: Box::new(left.clone()),
                                right: Box::new(right.clone()),
                                ty: ty.clone(),
                            };
                            if let Some(value) =
                                crate::ir_lowering::untyped_operation_value_all_types_agree(&tree)
                            {
                                return TrustVcExpr::IntLit { value, ty };
                            }
                        }
                        if typed && left_ty == &ty && right_ty == &ty {
                            let folded_value = match op {
                                ArithOp::Add => left_value.checked_add(*right_value),
                                ArithOp::Sub => left_value.checked_sub(*right_value),
                                ArithOp::Mul => left_value.checked_mul(*right_value),
                                ArithOp::Div if *right_value != 0 => {
                                    left_value.checked_div(*right_value)
                                }
                                ArithOp::Rem if *right_value != 0 => {
                                    left_value.checked_rem(*right_value)
                                }
                                _ => None,
                            };
                            if let Some(value) = folded_value {
                                if value_fits_int_lit_type(value, &ty) {
                                    return strict_folded_int_literal(
                                        value,
                                        ty,
                                        left_pinned || right_pinned,
                                    );
                                }
                            }
                        }
                    }

                    TrustVcExpr::Arith {
                        op,
                        left: Box::new(left),
                        right: Box::new(right),
                        ty,
                    }
                }
                TrustVcExpr::Neg(inner) => {
                    let inner = self.fold_expr(*inner);
                    if let Some((value, ty, pinned)) = strict_int_literal(&inner) {
                        if let Some(negated) = value.checked_neg() {
                            if value_fits_int_lit_type(negated, ty) {
                                return strict_folded_int_literal(negated, ty.clone(), pinned);
                            }
                        }
                    }
                    TrustVcExpr::Neg(Box::new(inner))
                }
                other => fold_expr_children(self, other),
            }
        }
    }

    LocalIntFolder.fold_expr(expr)
}

fn normalize_strict_unary_spec_closure_body(
    expr: &TrustVcExpr,
    canonical_key_name: &str,
) -> Option<(TrustVcType, TrustVcType, TrustVcExpr)> {
    let TrustVcExpr::SpecClosure { params, body, ty } = expr else {
        return None;
    };
    let [(param_name, param_ty)] = params.as_slice() else {
        return None;
    };
    let TrustVcType::SpecFn(arg_tys, ret_ty) = ty else {
        return None;
    };
    if arg_tys.len() != 1 || arg_tys.first() != Some(param_ty) {
        return None;
    }

    let canonical_key = crate::ir_builder::var(canonical_key_name, param_ty.clone());
    let subst = HashMap::from([(param_name.clone(), canonical_key)]);
    let body = substitute_free_vars(body, &subst);
    Some((
        param_ty.clone(),
        ret_ty.as_ref().clone(),
        fold_strict_local_int_constants(body),
    ))
}

fn build_strict_set_mk_map_known_eq(lhs: &TrustVcExpr, rhs: &TrustVcExpr) -> Option<TrustVcExpr> {
    let (lhs_receiver, lhs_args, lhs_ty) = strict_set_mk_map_parts(lhs)?;
    let (rhs_receiver, rhs_args, rhs_ty) = strict_set_mk_map_parts(rhs)?;
    if lhs_ty != rhs_ty || lhs_receiver != rhs_receiver {
        return None;
    }

    let mut used_names = HashSet::new();
    collect_spec_fn_operand_free_names(&lhs_args[0], &mut used_names);
    collect_spec_fn_operand_free_names(&rhs_args[0], &mut used_names);
    let canonical_key_name = fresh_bound_name("__trust_vc_strict_mk_map_key", &mut used_names);

    let lhs_body = normalize_strict_unary_spec_closure_body(&lhs_args[0], &canonical_key_name)?;
    let rhs_body = normalize_strict_unary_spec_closure_body(&rhs_args[0], &canonical_key_name)?;

    Some(TrustVcExpr::BoolLit(lhs_body == rhs_body))
}

/// Builds a typed extensional-equality formula from two lowered operands.
#[doc(hidden)]
#[must_use]
pub fn build_ext_eq_expr(lhs: TrustVcExpr, rhs: TrustVcExpr) -> TrustVcExpr {
    let (lhs, lhs_ty) = normalize_extensional_operand(lhs);
    let (rhs, rhs_ty) = normalize_extensional_operand(rhs);

    if lhs_ty != rhs_ty {
        return crate::ir_builder::eq(lhs, rhs);
    }

    match lhs_ty {
        TrustVcType::Seq(elem_ty) => build_seq_ext_eq(lhs, rhs, *elem_ty),
        TrustVcType::Set(elem_ty) => build_set_ext_eq(lhs, rhs, *elem_ty),
        TrustVcType::Multiset(elem_ty) => build_multiset_ext_eq(lhs, rhs, *elem_ty),
        TrustVcType::Map(key_ty, value_ty) => build_map_ext_eq(lhs, rhs, *key_ty, *value_ty),
        TrustVcType::SpecFn(arg_tys, ret_ty) => build_spec_fn_ext_eq(lhs, rhs, arg_tys, *ret_ty),
        _ => crate::ir_builder::eq(lhs, rhs),
    }
}

/// Builds a typed extensional-inequality formula from two lowered operands.
#[doc(hidden)]
#[must_use]
pub fn build_ext_ne_expr(lhs: TrustVcExpr, rhs: TrustVcExpr) -> TrustVcExpr {
    crate::ir_builder::not(build_ext_eq_expr(lhs, rhs))
}

/// True iff `expr` is structurally a collection extensional-equality formula as
/// produced by `build_ext_eq_expr` — a universally-quantified pointwise
/// agreement (Set membership / Map key+value / Multiset count / SpecFn
/// application), or, for `Seq`, a length agreement conjoined with such a
/// quantified body.
///
/// Used to scope sequential body-assert carry-forward: only a discharged
/// extensional equality (`=~=` / `ext_eq!` / collection `==`) is forwarded as an
/// assumption, so the strict-eq extensionality bridge can consume it via modus
/// ponens. Restricting to this shape (and requiring an actual collection
/// reference) keeps unrelated straight-line asserts — e.g. a `choose`-bearing
/// `s.contains(s.choose())` — OUT of the forwarded set, where adding them as
/// hypotheses can degrade a later obligation's solver outcome (turning a crisp
/// counterexample into Unknown). Conservative by construction: any expression it
/// does not recognize is simply not forwarded.
#[must_use]
pub(crate) fn is_collection_extensional_eq(expr: &TrustVcExpr) -> bool {
    fn contains_forall(expr: &TrustVcExpr) -> bool {
        match expr {
            TrustVcExpr::Quantifier {
                kind: QuantifierKind::Forall,
                ..
            } => true,
            TrustVcExpr::Logic {
                op: LogicOp::And,
                left,
                right,
            } => contains_forall(left) || contains_forall(right),
            _ => false,
        }
    }

    contains_forall(expr) && expr.references_collection()
}

/// Builds strict equality: raw solver equality over the encoded operands.
///
/// Unlike `build_ext_eq_expr`, this intentionally does not expand Seq/Set/Map
/// equality into extensional formulas. It is the Rust-valid stand-in for Verus
/// strict equality surfaces such as `===` / `equal(...)`.
#[doc(hidden)]
#[must_use]
pub fn build_strict_eq_expr(lhs: TrustVcExpr, rhs: TrustVcExpr) -> TrustVcExpr {
    if let Some(known_eq) = build_strict_set_mk_map_known_eq(&lhs, &rhs) {
        return known_eq;
    }

    TrustVcExpr::FnCall {
        name: STRICT_EQ_FN.to_string(),
        args: vec![lhs, rhs],
        return_ty: TrustVcType::Bool,
    }
}

#[cfg(test)]
#[path = "extensional_eq_tests.rs"]
mod tests;
