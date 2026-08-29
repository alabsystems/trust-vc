//! THE single sort gate for broadcast / lemma ground instantiation.
//!
//! # Why this module exists
//!
//! A broadcast `forall` (or any ground-replayed quantified axiom) is discharged
//! by asserting ground *instances* of it into the query. Every such instance is
//! sound for exactly one reason: it is a **universal instantiation** of a
//! premise the solver already holds. That argument has a silent side condition —
//! the substituted witness must be a **value of the bound variable's sort**.
//!
//! Nothing enforced that side condition, and violating it is not a completeness
//! loss but a *cardinal false verify*. Two independent mechanisms turn an
//! out-of-sort substitution into a false ground fact:
//!
//! 1. **Literal widening.** `encode_int_lit` deliberately does NOT wrap an
//!    out-of-range literal (wrapping would silently redefine the constant — the
//!    casts-bitvec cluster); it WIDENS. So `x <= 255u8` instantiated at the
//!    `u64`-derived witness `2^64-1` encodes as the 64-bit comparison
//!    `2^64-1 <= 255`, i.e. FALSE.
//! 2. **Expression widening.** Substituting a *wider-typed expression* is worse,
//!    because the result is not even visibly false: `forall|x: u8| x <= 255u8`
//!    instantiated at a `u64` variable `w` asserts `w <= 255` — a perfectly
//!    consistent, perfectly unjustified fact about `w`. The vacuity guard cannot
//!    see it (nothing is contradictory), and the goal `w <= 255u64` then
//!    "verifies" for an arbitrary `u64`.
//!
//! Mechanism (2) is why this gate lives in its own module instead of inside one
//! caller: witnesses reach broadcast instantiation from *seven* independent
//! sources across three files, and a per-source filter closes only the source it
//! was written for. Round 1 filtered S1–S3 inside
//! `build_premise_ground_instances` and the reproducer it was aimed at stopped
//! reproducing — while S4 stayed wide open, in the very same call chain.
//!
//! # The witness sources, and where each is gated
//!
//! | # | Source | Producer | Gated at |
//! |---|--------|----------|----------|
//! | S1 | fixed integer type boundaries | `int_type_boundaries` | `instantiate_bound_vars_in_sort` |
//! | S2 | literal int constants harvested from the premise text | `collect_literal_int_constants` | `instantiate_bound_vars_in_sort` |
//! | S3 | scalars harvested from a candidate SAT model | `collect_int_witnesses` | `instantiate_bound_vars_in_sort` |
//! | S4 | IR trigger matches against goal/assumption exprs | `collect_interpreted_trigger_binding_tuples` | `instantiate_bound_vars_in_sort` |
//! | S5 | ground-pool bindings (`match_trigger_args` on registered ground args, or `equality_assumptions`) | `GroundTermPool::pending_instantiations` | `instantiate_bound_vars_in_sort` |
//! | S6 | native-seq small-index literals | `instantiate_small_native_seq_index_cases` | `instantiate_bound_vars_in_sort` |
//! | S7 | ground-pool seed-symbol **solver terms** (no IR form) | `GroundTermPool::pending_instantiations` | `term_sort_inhabits_type` |
//!
//! S1–S3 were the only ones a per-source filter covered. S4 is the reproducer in
//! `broadcast_goal_witness_sort_soundness`; S5–S7 are its siblings, closed here
//! by construction rather than by patching each call site: **substitution for a
//! broadcast bound variable now happens only inside
//! `instantiate_bound_vars_in_sort`**, so a new witness source cannot bypass the
//! check without deliberately re-implementing the substitution.
//!
//! # The rule
//!
//! `witness_inhabits_type(witness, declared)` answers "is every value this
//! witness can take a value of `declared`?".
//!
//! * Integer-like `declared`: an `IntLit` is checked by VALUE; any other
//!   expression is checked by RANGE INCLUSION of its inferred type. This is
//!   deliberately *not* the encoder's `fits_in_bv` "representable at this width"
//!   test — `-1` is representable in `BV8` but is not a `u8`, and the encoder's
//!   rendering of it as `255` is only accidentally sound.
//! * `Bool`: the witness must be `Bool`-typed.
//! * `TypeParam` / `Poly` / `Opaque`: type-erased; every value inhabits them, so
//!   accept (declining here would break polymorphic ground replay, which routes
//!   *all* its axioms through this path).
//! * Everything else: the witness's inferred type must map to the SAME backend
//!   sort as the declared type.
//!
//! When the bound variable has no declared type, or the witness's type cannot be
//! established, the instance is DECLINED. Declining costs completeness only: the
//! premise's live `forall` (where one exists) is untouched, and the remaining
//! in-sort witnesses still fire.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashMap;

use ay_dpll::api::Sort;

use crate::encoder::types::sort_for_type;
use crate::ir::{TrustVcExpr, TrustVcType};
use crate::ir_lowering::infer_expr_type;

/// Inclusive value range of a *bounded* integer-like type, as `i128`.
///
/// `None` for the unbounded sorts (`MathInt`, `Nat`) and for everything that is
/// not integer-like. Widths at or above the `i128` horizon saturate: that is
/// conservative in the only direction that matters, because a saturated source
/// range is *wider* (so inclusion into a narrower target still fails) and a
/// saturated target range is *narrower* than the true one only above `2^127`,
/// where no `i128`-representable witness lives anyway.
fn bounded_int_range(ty: &TrustVcType) -> Option<(i128, i128)> {
    match ty {
        TrustVcType::Int { width } => {
            let width = *width;
            if width == 0 {
                return None;
            }
            if width >= 128 {
                return Some((i128::MIN, i128::MAX));
            }
            Some((-(1i128 << (width - 1)), (1i128 << (width - 1)) - 1))
        }
        TrustVcType::Uint { width } => {
            let width = *width;
            if width == 0 {
                return None;
            }
            if width >= 127 {
                return Some((0, i128::MAX));
            }
            Some((0, (1i128 << width) - 1))
        }
        // A `char` is a Unicode scalar value, encoded as a 32-bit BV.
        TrustVcType::Char => Some((0, 0x0010_FFFF)),
        _ => None,
    }
}

/// True iff `ty` is one of the integer-like sorts this gate reasons about.
fn is_int_like(ty: &TrustVcType) -> bool {
    matches!(
        ty,
        TrustVcType::Int { .. }
            | TrustVcType::Uint { .. }
            | TrustVcType::MathInt
            | TrustVcType::Nat
            | TrustVcType::Char
    )
}

/// True iff `value` is a value OF the integer-like sort `ty` — i.e. whether
/// substituting it for a bound variable of that type yields a genuine universal
/// instantiation of the premise.
///
/// This is deliberately the *sort membership* test, NOT the encoder's
/// `fits_in_bv` "representable as signed or unsigned at this width" test:
/// `-1` is representable in `BV8` but is not a `u8`, and instantiating a `u8`
/// forall at `-1` is not an entailed instance (the encoder happens to render it
/// as `255`, which is only accidentally sound). Anything outside the sort is
/// rejected outright.
pub(crate) fn value_inhabits_int_type(value: i128, ty: &TrustVcType) -> bool {
    match ty {
        TrustVcType::MathInt => true,
        TrustVcType::Nat => value >= 0,
        _ => match bounded_int_range(ty) {
            Some((low, high)) => value >= low && value <= high,
            // Not an integer-like sort: the integer witness path must not reach it.
            None => false,
        },
    }
}

/// True iff EVERY value of `from` is also a value of `into` — the type-level
/// form of the same membership question, used when the witness is a symbolic
/// expression rather than a literal.
fn int_type_includes(from: &TrustVcType, into: &TrustVcType) -> bool {
    if from == into {
        return is_int_like(from);
    }
    if !is_int_like(from) {
        return false;
    }
    match into {
        // Unbounded mathematical integer: every integer-like value is an int.
        TrustVcType::MathInt => true,
        // Unbounded non-negative: only a source that cannot be negative.
        TrustVcType::Nat => match from {
            TrustVcType::Nat => true,
            other => bounded_int_range(other).is_some_and(|(low, _)| low >= 0),
        },
        // Bounded target: the source must be bounded and range-included. An
        // unbounded source (`int`, `nat`) is NOT included in any finite width.
        _ => match (bounded_int_range(from), bounded_int_range(into)) {
            (Some((from_low, from_high)), Some((into_low, into_high))) => {
                from_low >= into_low && from_high <= into_high
            }
            _ => false,
        },
    }
}

/// THE gate. True iff substituting `witness` for a bound variable declared with
/// type `declared` is a genuine universal instantiation.
///
/// See the module docs for the rule and for why declining is always safe.
pub(crate) fn witness_inhabits_type(witness: &TrustVcExpr, declared: &TrustVcType) -> bool {
    match declared {
        // Type-erased sorts: every value inhabits them. Declining here would
        // break polymorphic ground replay, whose axioms are routed to the
        // ground-instantiation path precisely BECAUSE they are type-erased.
        TrustVcType::TypeParam(_) | TrustVcType::Poly | TrustVcType::Opaque(_) => true,
        TrustVcType::Bool => matches!(infer_expr_type(witness), TrustVcType::Bool),
        _ if is_int_like(declared) => match witness {
            // A literal carries its value, so check the value: this is strictly
            // sharper than the type test (a `u64`-typed literal `7` IS a `u8`).
            TrustVcExpr::IntLit { value, .. } => value_inhabits_int_type(*value, declared),
            TrustVcExpr::Neg(inner) => match inner.as_ref() {
                TrustVcExpr::IntLit { value, .. } => value
                    .checked_neg()
                    .is_some_and(|negated| value_inhabits_int_type(negated, declared)),
                _ => int_type_includes(&infer_expr_type(witness), declared),
            },
            _ => int_type_includes(&infer_expr_type(witness), declared),
        },
        // Non-scalar sorts (Seq/Set/Map/Datatype/Real/Float/…): the false-verify
        // mechanism above is arithmetic, but a mismatch here is still not an
        // instantiation. Require the witness to land on the same backend sort.
        _ => sort_for_type(&infer_expr_type(witness)) == sort_for_type(declared),
    }
}

/// Term-level counterpart of `witness_inhabits_type`, for the one ground-pool
/// path that binds solver `Term`s directly (S7) and therefore has no IR witness
/// expression to inspect.
///
/// Only the backend sort is observable here, so this is necessarily coarser than
/// the IR gate: it cannot separate `-1` from `255` inside `BV8`. It still closes
/// the *width* channel, which is the one that manufactures false ground facts.
pub(crate) fn term_sort_inhabits_type(term_sort: &Sort, declared: &TrustVcType) -> bool {
    match declared {
        TrustVcType::TypeParam(_) | TrustVcType::Poly | TrustVcType::Opaque(_) => true,
        // An unbounded `int` bound variable admits any integer value, however
        // the backend chose to represent it.
        TrustVcType::MathInt => {
            matches!(term_sort, Sort::Int | Sort::BitVec(_))
                || *term_sort == sort_for_type(declared)
        }
        _ => *term_sort == sort_for_type(declared),
    }
}

/// True iff every `(bound var, witness)` pair is in sort. A bound variable with
/// no declared type DECLINES the whole tuple: the sort cannot be established, so
/// the substitution cannot be shown to be an instantiation.
pub(crate) fn binding_tuple_is_in_sort(
    bound_vars: &[String],
    witnesses: &[TrustVcExpr],
    var_types: &HashMap<String, TrustVcType>,
) -> bool {
    if bound_vars.len() != witnesses.len() {
        return false;
    }
    bound_vars
        .iter()
        .zip(witnesses)
        .all(|(name, witness)| match var_types.get(name.as_str()) {
            Some(declared) => witness_inhabits_type(witness, declared),
            None => false,
        })
}

/// **The single point every witness source converges on.** Substitutes
/// `witnesses` for `bound_vars` in `body` — and returns `None` instead when any
/// witness is not a value of its bound variable's sort.
///
/// Callers must not call `substitute_vars_in_expr` on broadcast bound variables
/// directly; routing through here is what makes the sort check unbypassable.
pub(crate) fn instantiate_bound_vars_in_sort(
    body: &TrustVcExpr,
    bound_vars: &[String],
    witnesses: &[TrustVcExpr],
    var_types: &HashMap<String, TrustVcType>,
) -> Option<TrustVcExpr> {
    if !binding_tuple_is_in_sort(bound_vars, witnesses, var_types) {
        return None;
    }
    let bindings: HashMap<&str, &TrustVcExpr> = bound_vars
        .iter()
        .map(String::as_str)
        .zip(witnesses.iter())
        .collect();
    Some(crate::encoder::eval::substitute_vars_in_expr(
        body, &bindings,
    ))
}

#[cfg(test)]
#[path = "witness_sort_tests.rs"]
mod tests;
