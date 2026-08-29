//! Model re-validation against quantified broadcast `forall` premises.
//!
//! ay's SAT model validation deliberately SKIPS quantified assertions
//! (`ValidationSkipKind::Quantifier` — see ay-dpll
//! `executor/model/validation/pipeline.rs`), trusting that E-matching / CEGQI
//! verified them during solving. When E-matching fails to instantiate a
//! broadcast `forall` at the witness a counterexample assigns, the returned
//! model can violate the premise even though `sat_model_validated == true`.
//! trust-vc historically trusted that flag and emitted a *definitive*
//! counterexample whose model violated an assumed (un-instantiated) premise —
//! a false refutation (#1, soundness).
//!
//! This module closes that gap. Before a SAT model is promoted to a
//! counterexample, each live broadcast `forall` premise is instantiated at a
//! witness set drawn from three sources — (1) the candidate model's scalar
//! values, (2) **fixed type boundaries** for each bound variable (e.g.
//! `i32::MIN, -1, 0, 1, i32::MAX`; `0, 1, max` for unsigned; non-negative only
//! for `nat`), and (3) small integer constants appearing literally in the
//! premise guard/body — the resulting ground facts are asserted, and the query
//! is re-checked **once**:
//!
//! * **UNSAT ⟹ Verified.** Each instance is a *logical consequence* of the
//!   universally-quantified premise already asserted in the solver, so
//!   `(assumptions ∧ instances ∧ ¬goal)` is equisatisfiable with
//!   `(assumptions ∧ ¬goal)`. An UNSAT re-check therefore proves the goal was
//!   genuinely valid — the original SAT model was a spurious counterexample
//!   that violated the (un-instantiated) premise. Sound: nothing was added that
//!   the assumptions did not already entail.
//! * **Anything else ⟹ keep the original counterexample.** Because the
//!   instances are entailed, a *genuine* counterexample (a model that truly
//!   satisfies the foralls and negates the goal) satisfies every instance too,
//!   so the re-check can never turn it UNSAT. Thus the only way to reach UNSAT
//!   is a spurious model, and any non-UNSAT result means we found no refutation:
//!   the candidate counterexample is preserved unchanged. This single-round,
//!   only-upgrade-to-Verified policy CANNOT over-suppress a real refutation and
//!   CANNOT manufacture a false Verified.
//!
//! Adding the type boundaries / premise constants only *enlarges* the witness
//! set; soundness is unchanged because every added instance is still a universal
//! instantiation of the asserted `forall` **at a value of the bound variable's
//! sort** — enforced by `encoder::witness_sort::instantiate_bound_vars_in_sort`,
//! the single gate every witness source in the encoder now routes through, which
//! refuses to substitute any witness outside that sort. Each surviving instance
//! is therefore a logical consequence and a genuine counterexample satisfies all
//! of them — it can never be flipped to UNSAT, so genuine refutations are still
//! preserved.
//!
//! That range filter is load-bearing, not hygiene. Integer literals do NOT
//! re-wrap to the bound variable's width: `encode_int_lit` deliberately widens
//! an out-of-range literal instead of wrapping it (wrapping would silently
//! redefine the constant — the casts-bitvec cluster). So a `u64`-derived model
//! witness `2^64-1` substituted into a `u8` bound variable turned `x <= 255u8`
//! into the 64-bit comparison `2^64-1 <= 255` — a FALSE ground fact asserted
//! into the query, making the context contradictory and every obligation
//! `Verified`. That was a cardinal false verify; the gate closes it.
//!
//! **This module is only ONE of the witness sources.** The witnesses built here
//! are literals, so a value-range filter sufficed for them — but broadcast
//! premises are also instantiated at witness EXPRESSIONS harvested from the goal
//! (`verification/broadcast.rs`) and from the ground pool
//! (`encoder/ground_pool.rs`), where the same class of defect appears with a
//! consistent-but-unjustified fact instead of a visibly false one. See
//! `encoder::witness_sort` for the full source inventory and the shared rule.
//!
//! Residual (documented) incompleteness: a model that violates the premise only
//! at a witness value that is neither in the model's scalars, nor a type
//! boundary, nor a literal premise constant is not detected and is still
//! emitted — strictly better than the previous behavior (no check at all), and
//! never a false *Verified*.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use ay_dpll::api::Model;
use num_bigint::BigInt;

use super::solve::try_check_sat_with_details;
use crate::encoder::encoder_state::BroadcastForallPremise;
use crate::encoder::witness_sort::{instantiate_bound_vars_in_sort, value_inhabits_int_type};
use crate::encoder::AYEncoder;
use crate::ir::{TrustVcExpr, TrustVcType};
use crate::ir_expr_traversal::{walk_expr, TrustVcExprVisitor};

/// Maximum distinct integer witness values harvested from the candidate model.
const MAX_INT_WITNESSES: usize = 8;

/// Maximum distinct literal integer constants harvested from a premise's
/// guard/body to seed additional boundary witnesses.
const MAX_PREMISE_CONSTANTS: usize = 8;

/// Maximum ground instances built per premise (caps the cartesian product over
/// multi-variable broadcast foralls).
const MAX_INSTANCES_PER_PREMISE: usize = 64;

/// Outcome of re-validating a candidate SAT model against broadcast premises.
pub(in crate::encoder) enum BroadcastModelRevalidation {
    /// No refutation found — keep and emit the original counterexample model
    /// unchanged. Covers: no quantified premises, no usable witnesses, or the
    /// candidate model survived re-validation (re-check stayed SAT/Unknown).
    KeepOriginal,
    /// A model-derived (entailed) premise instance refuted the negated goal: the
    /// candidate model violated an assumed premise; the obligation is Verified.
    Refuted,
}

impl AYEncoder {
    /// Re-validate a candidate SAT model against the live broadcast `forall`
    /// premises asserted into this encoder's solver. See the module docs for
    /// the soundness argument. Operates within the caller's current solver
    /// scope (the one holding the negated goal); the caller pops it afterward.
    ///
    /// Single round, fail-open: only ever upgrades to `Refuted` (Verified) when
    /// the entailed premise instances make the query UNSAT; otherwise keeps the
    /// original counterexample. This can neither suppress a genuine refutation
    /// nor produce a false Verified.
    pub(in crate::encoder) fn revalidate_broadcast_premises_against_model(
        &mut self,
        witness_model: &Model,
    ) -> BroadcastModelRevalidation {
        if self.state.broadcast_premises.is_empty() {
            return BroadcastModelRevalidation::KeepOriginal;
        }

        // Snapshot premises so we can encode against `&mut self` without holding
        // a borrow of `self.state`.
        let premises = self.state.broadcast_premises.clone();

        let int_witnesses = collect_int_witnesses(witness_model, MAX_INT_WITNESSES);
        // A bound bool variable's violating witness need not appear in the
        // model, so always try both polarities.
        let bool_witnesses = [true, false];

        let mut added_any = false;
        for premise in &premises {
            let instances =
                self.build_premise_ground_instances(premise, &int_witnesses, &bool_witnesses);
            for instance in instances {
                let encoded = crate::encoder::with_flag_unwind_safe!(
                    self.state.in_assumption_context,
                    true,
                    { self.resolve_condition_typed(&instance) }
                );
                if let Ok(term) = encoded {
                    if self.solver.try_assert_term(term).is_ok() {
                        added_any = true;
                    }
                }
            }
        }

        if !added_any {
            // No instantiable premise (e.g. only non-scalar bound-variable
            // sorts) — nothing to check against. Keep the original CE.
            return BroadcastModelRevalidation::KeepOriginal;
        }

        // Re-check with the entailed premise instances added. UNSAT proves the
        // goal (the original model was spurious); any other result means we
        // found no refutation, so the candidate counterexample stands.
        match try_check_sat_with_details(&mut self.solver) {
            Ok(details) if details.result.result().is_unsat() => {
                BroadcastModelRevalidation::Refuted
            }
            _ => BroadcastModelRevalidation::KeepOriginal,
        }
    }

    /// Build ground instantiations of one broadcast `forall` premise at the
    /// supplied scalar witness values, augmented per bound variable with fixed
    /// type-boundary witnesses and any literal integer constants appearing in
    /// the premise guard/body.
    ///
    /// Each instance is `(guard ==> body)[bound_vars := witnesses]` — a valid
    /// universal instantiation, hence a logical consequence of the asserted
    /// `forall`. Only integer-like and boolean bound variables are instantiated;
    /// a premise with any other bound-variable sort yields no instances (so the
    /// original counterexample is preserved rather than unsoundly discharged).
    /// Also reused by the interpreted-op dead-trigger broadcast ground replay
    /// (`add_typed_broadcast`) with an empty witness list, yielding the fixed
    /// type-boundary + premise-constant instances as the canonical battery.
    pub(in crate::encoder) fn build_premise_ground_instances(
        &self,
        premise: &BroadcastForallPremise,
        int_witnesses: &[i128],
        bool_witnesses: &[bool],
    ) -> Vec<TrustVcExpr> {
        // Literal integer constants appearing in the premise text. A premise
        // violated at a guard/body boundary (e.g. `n < 5`) is caught even when
        // that value is absent from the candidate model.
        let premise_constants = collect_literal_int_constants(premise, MAX_PREMISE_CONSTANTS);

        let mut per_var: Vec<Vec<TrustVcExpr>> = Vec::with_capacity(premise.bound_vars.len());
        for name in &premise.bound_vars {
            let ty = match self.var_types.get(name) {
                Some(ty) => ty.clone(),
                // Bound variable sort unknown — cannot instantiate soundly.
                None => return Vec::new(),
            };
            let literals: Vec<TrustVcExpr> = match &ty {
                TrustVcType::Int { .. }
                | TrustVcType::Uint { .. }
                | TrustVcType::MathInt
                | TrustVcType::Nat => {
                    let mut values: Vec<i128> = Vec::new();
                    // (1) Fixed type boundaries FIRST, so the most diagnostic
                    //     values are always exercised even when the cartesian
                    //     product cap truncates later combinations.
                    for value in int_type_boundaries(&ty) {
                        push_unique(&mut values, value, usize::MAX);
                    }
                    // (2) Literal constants harvested from the premise text.
                    for value in &premise_constants {
                        push_unique(&mut values, *value, usize::MAX);
                    }
                    // (3) Witnesses harvested from the candidate model.
                    for value in int_witnesses {
                        push_unique(&mut values, *value, usize::MAX);
                    }
                    // SOUNDNESS (cardinal): only values that actually INHABIT the
                    // bound variable's sort may be substituted. An instance is a
                    // logical consequence of the asserted `forall` only when the
                    // substituted literal is a value of the quantified sort — a
                    // model witness harvested from an unrelated `u64` term
                    // (2^64-1, or its signed reading -1) is NOT a `u8`, and
                    // likewise a literal constant harvested from the premise text
                    // may exceed the bound variable's width.
                    //
                    // Substituting an out-of-sort value does not merely lose
                    // completeness: `encode_int_lit` deliberately does NOT wrap
                    // an out-of-range literal (wrapping would silently redefine
                    // the constant — the casts-bitvec cluster), it WIDENS to the
                    // smallest width that preserves the value. So `x <= 255u8`
                    // instantiated at 2^64-1 encodes as the 64-bit unsigned
                    // comparison `2^64-1 <= 255`, i.e. a FALSE ground fact
                    // asserted into the query context. A false premise entails
                    // everything, so the negated goal goes UNSAT and the
                    // obligation is reported Verified — a cardinal false verify.
                    //
                    // This `retain` is an EFFICIENCY pre-filter only: it keeps
                    // out-of-sort values from consuming the cartesian-product
                    // cap. The AUTHORITATIVE check is the shared gate applied at
                    // substitution time below (`instantiate_bound_vars_in_sort`),
                    // so removing this line cannot reopen the hole — and a new
                    // witness source added here inherits the gate for free.
                    values.retain(|value| value_inhabits_int_type(*value, &ty));
                    values
                        .into_iter()
                        .map(|value| TrustVcExpr::IntLit {
                            value,
                            ty: ty.clone(),
                        })
                        .collect()
                }
                TrustVcType::Bool => bool_witnesses
                    .iter()
                    .map(|value| TrustVcExpr::BoolLit(*value))
                    .collect(),
                // Unsupported witness sort (Seq/Set/Map/Datatype/Float/…): skip
                // the whole premise so we never drop a genuine counterexample.
                _ => return Vec::new(),
            };
            if literals.is_empty() {
                return Vec::new();
            }
            per_var.push(literals);
        }

        let full = match &premise.guard {
            Some(guard) => TrustVcExpr::Implies {
                premise: Box::new(guard.clone()),
                conclusion: Box::new(premise.body.clone()),
            },
            None => premise.body.clone(),
        };

        let total_combos = per_var
            .iter()
            .fold(1usize, |acc, values| acc.saturating_mul(values.len()));
        let cap = total_combos.min(MAX_INSTANCES_PER_PREMISE);

        let mut instances: Vec<TrustVcExpr> = Vec::with_capacity(cap);
        let mut indices = vec![0usize; per_var.len()];
        for _ in 0..cap {
            // `instantiate_bound_vars_in_sort` applies the shared sort gate and
            // then substitutes via `substitute_vars_in_expr`, which is
            // scope-aware and recurses into *all* subexpressions (function-call
            // arguments, indexing, etc.) while respecting nested quantifier
            // binders — unlike the arithmetic-only `normalize::substitute_vars`,
            // which leaves `FnCall` args untouched and would yield unsound
            // partial instances like `g(x, y) == 60`.
            let witnesses: Vec<TrustVcExpr> = (0..per_var.len())
                .map(|position| per_var[position][indices[position]].clone())
                .collect();
            if let Some(instance) = instantiate_bound_vars_in_sort(
                &full,
                &premise.bound_vars,
                &witnesses,
                &self.var_types,
            ) {
                instances.push(instance);
            }

            // Advance the mixed-radix odometer to the next witness combination.
            let mut position = 0;
            while position < per_var.len() {
                indices[position] += 1;
                if indices[position] < per_var[position].len() {
                    break;
                }
                indices[position] = 0;
                position += 1;
            }
        }
        instances
    }
}

/// Harvest distinct integer witness values from a model: every `Int` value and
/// both the signed (two's complement) and unsigned interpretations of every
/// bitvector value. The `IntLit` encoder re-wraps to each bound variable's
/// width, so a single correct candidate suffices; gathering both interpretations
/// maximizes the chance of hitting the value a spurious model intended.
fn collect_int_witnesses(model: &Model, cap: usize) -> Vec<i128> {
    let mut out: Vec<i128> = Vec::new();
    for (_, value) in model.iter_ints() {
        if let Ok(value) = i128::try_from(value) {
            push_unique(&mut out, value, cap);
        }
    }
    for (_, (value, width)) in model.iter_bvs() {
        if let Some(unsigned) = bv_to_unsigned_i128(value, *width) {
            push_unique(&mut out, unsigned, cap);
        }
        if let Some(signed) = bv_to_signed_i128(value, *width) {
            push_unique(&mut out, signed, cap);
        }
    }
    out
}

fn push_unique(out: &mut Vec<i128>, value: i128, cap: usize) {
    if out.len() < cap && !out.contains(&value) {
        out.push(value);
    }
}

/// Fixed boundary witnesses for an integer-like bound-variable type.
///
/// These are returned in addition to the model-scalar witnesses so that a
/// premise contradicted only at a domain boundary (e.g. a `forall n:i32. n >= 0`
/// that is false at `n = -1`) is detected even when the candidate model never
/// assigned that boundary value. Every value returned is a legal value of the
/// type's SMT sort: signed/unsigned bitvector literals re-wrap to the bound
/// variable's own width, and `MathInt`/`nat` are unbounded `Int`. For `nat` only
/// non-negative boundaries are returned because its sort excludes negative
/// values. Boundaries that are not representable as `i128` (e.g. `u128::MAX`)
/// are simply omitted — this affects completeness only, never soundness.
///
/// Every candidate additionally passes through the shared witness-sort gate;
/// `every_type_boundary_survives_the_gate` (in `encoder::witness_sort`) pins that
/// this battery is never emptied by it.
pub(in crate::encoder) fn int_type_boundaries(ty: &TrustVcType) -> Vec<i128> {
    match ty {
        TrustVcType::Int { width } => {
            let width = *width;
            let mut values = vec![-1i128, 0, 1];
            if (1..=128).contains(&width) {
                let (min, max) = if width >= 128 {
                    (i128::MIN, i128::MAX)
                } else {
                    (-(1i128 << (width - 1)), (1i128 << (width - 1)) - 1)
                };
                values.push(min);
                values.push(max);
            }
            values
        }
        TrustVcType::Uint { width } => {
            let width = *width;
            let mut values = vec![0i128, 1];
            if (1..=126).contains(&width) {
                values.push((1i128 << width) - 1);
            } else if width == 127 {
                values.push(i128::MAX);
            }
            // width >= 128: `2^width - 1` is not representable as i128; omit the
            // max boundary (model/other witnesses still apply).
            values
        }
        // Unbounded mathematical integer: no min/max, but the boundaries around
        // zero are still the most diagnostic values.
        TrustVcType::MathInt => vec![-1, 0, 1],
        // Unbounded non-negative integer: no finite max, and negative values are
        // out of sort, so only the low non-negative boundaries.
        TrustVcType::Nat => vec![0, 1],
        _ => Vec::new(),
    }
}

/// Harvest up to `cap` distinct literal integer constants appearing anywhere in
/// a premise's guard and body. Used to seed additional boundary witnesses so a
/// premise violated at a constant mentioned in its own guard/body is caught even
/// when that value is absent from the candidate model.
fn collect_literal_int_constants(premise: &BroadcastForallPremise, cap: usize) -> Vec<i128> {
    struct LitCollector {
        out: Vec<i128>,
        cap: usize,
    }
    impl TrustVcExprVisitor for LitCollector {
        fn visit_expr(&mut self, expr: &TrustVcExpr) {
            if let TrustVcExpr::IntLit { value, .. } = expr {
                push_unique(&mut self.out, *value, self.cap);
            }
            walk_expr(self, expr);
        }
    }
    let mut collector = LitCollector {
        out: Vec::new(),
        cap,
    };
    if let Some(guard) = &premise.guard {
        collector.visit_expr(guard);
    }
    collector.visit_expr(&premise.body);
    collector.out
}

/// Unsigned (`value mod 2^width`) interpretation of a bitvector as `i128`.
fn bv_to_unsigned_i128(value: &BigInt, width: u32) -> Option<i128> {
    if width == 0 {
        return Some(0);
    }
    let modulus = BigInt::from(1) << width;
    let unsigned = ((value % &modulus) + &modulus) % &modulus;
    i128::try_from(&unsigned).ok()
}

/// Two's-complement signed interpretation of a bitvector as `i128`.
fn bv_to_signed_i128(value: &BigInt, width: u32) -> Option<i128> {
    if width == 0 {
        return Some(0);
    }
    let modulus = BigInt::from(1) << width;
    let half = BigInt::from(1) << (width - 1);
    let unsigned = ((value % &modulus) + &modulus) % &modulus;
    let signed = if unsigned >= half {
        unsigned - modulus
    } else {
        unsigned
    };
    i128::try_from(&signed).ok()
}

#[cfg(test)]
mod tests {
    //! The value-membership pins that used to live here moved to
    //! `encoder::witness_sort` together with `value_inhabits_int_type` itself,
    //! because that check is now shared by every witness source rather than
    //! owned by this module. `every_type_boundary_survives_the_gate` there still
    //! cross-checks `int_type_boundaries` from this file, so the battery cannot
    //! silently empty out.
    use super::{bv_to_signed_i128, bv_to_unsigned_i128, int_type_boundaries};
    use crate::ir::TrustVcType;
    use num_bigint::BigInt;

    /// `int_type_boundaries` must always offer at least the zero-neighbourhood,
    /// or a premise contradicted at a boundary yields no instance at all.
    #[test]
    fn boundaries_are_never_empty_for_integer_sorts() {
        for ty in [
            TrustVcType::Uint { width: 8 },
            TrustVcType::Uint { width: 128 },
            TrustVcType::Int { width: 8 },
            TrustVcType::Int { width: 128 },
            TrustVcType::MathInt,
            TrustVcType::Nat,
        ] {
            assert!(
                !int_type_boundaries(&ty).is_empty(),
                "no boundaries for {ty:?}"
            );
        }
        // Non-integer sorts contribute no integer boundaries.
        assert!(int_type_boundaries(&TrustVcType::Bool).is_empty());
    }

    /// Both readings of a model bitvector are harvested; the sort gate — not
    /// this harvest — decides which may be substituted.
    #[test]
    fn bitvector_witnesses_expose_both_readings() {
        let value = BigInt::from(255);
        assert_eq!(bv_to_unsigned_i128(&value, 8), Some(255));
        assert_eq!(bv_to_signed_i128(&value, 8), Some(-1));
    }
}
