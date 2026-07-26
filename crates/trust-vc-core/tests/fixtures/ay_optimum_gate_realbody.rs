// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// =====================================================================
// NON-VACUOUS native-deductive verification of the REAL ay-pb
// `OptimumFound` upgrade gate `optimum_upgrade_guard` (portfolio.rs:77) —
// the actual BODY `value <= floor && verify_all_constraints(constraints,
// assignment)` carrying the actual functional-correctness `#[ensures]`,
// discharged by trust-vc on the pure-Rust `ay` SMT solver.
// =====================================================================
//
// WHAT THIS EXERCISES:
//   The gate decision is pinned to EXACTLY `value <= floor &&
//   verify_all_constraints(..)`: the `Satisfiable -> OptimumFound` upgrade can
//   NEVER fire when `value > floor` (the sound objective lower bound is not met)
//   or when the incumbent fails the Verified Incumbent Gate. The proof combines
//   the i128/BV128 `value <= floor` comparison, the boolean `&&`, and a
//   congruent spec-fn call to the VIG predicate `verify_all_constraints`. The
//   body's `value <= floor && ..` tail (a comparison-then-`&&`) is the shape the
//   `result == (..)` return-binding parenthesization was built to handle.
//
// HOW `verify_all_constraints` IS MODELED (Verus mechanism):
//   declared `#[trust_vc::spec] #[trust_vc::opaque]` — a PURE UNINTERPRETED
//   (congruent) bool predicate over the same `(&[PbConstraint], &[bool])` the
//   live VIG takes (its real `.iter().all(..)` body is verified against its own
//   `#[ensures]` in `verify_all_constraints_realbody.rs`). The gate-soundness
//   property being proven (`result == value <= floor && VIG`) holds for an
//   ARBITRARY congruent VIG, hence for the real one in particular — the same
//   sound "opaque spec fn, no reveal" abstraction used for `eval_terms` /
//   `eval_constraint` elsewhere in this proof suite.
//
// HOW THIS IS VERIFIED: `trust_vc_core::verify_function_from_file`. `Verified` ==
//   ay returned UNSAT and the trust-vc-kernel accepted the proof; `Counterexample`
//   == ay returned a concrete falsifying model.

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PbLit {
    pub var: u32,
    pub negated: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PbTerm {
    pub coeff: i128,
    pub lits: Vec<PbLit>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum PbRel {
    Ge,
    Eq,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PbConstraint {
    pub terms: Vec<PbTerm>,
    pub rel: PbRel,
    pub rhs: i128,
}

// The Verified Incumbent Gate, modeled as an OPAQUE (uninterpreted, congruent)
// bool predicate. Its real `.iter().all(..)` body is verified separately.
#[trust_vc::spec]
#[trust_vc::opaque]
fn verify_all_constraints(constraints: &[PbConstraint], assignment: &[bool]) -> bool {
    false
}

// ===========================================================================
// TARGET — optimum_upgrade_guard (portfolio.rs:77), VERBATIM REAL BODY.
//
// CONTRACT: `result` is EXACTLY `value <= floor && verify_all_constraints(..)`.
// The upgrade fires IFF the cheap sound-bound test holds AND the VIG re-passes.
// PROVES by congruence + i128/BV128 comparison.
// ===========================================================================
#[trust_vc::ensures(result == (value <= floor && verify_all_constraints(constraints, assignment)))]
// CONFORMANCE: src/portfolio.rs:77-84
pub fn optimum_upgrade_guard(
    value: i128,
    floor: i128,
    constraints: &[PbConstraint],
    assignment: &[bool],
) -> bool {
    value <= floor && verify_all_constraints(constraints, assignment)
}

// NEGATIVE CONTROL — drop the lower-bound guard: claims `result` IFF the VIG
// passes, REGARDLESS of `value <= floor`. This is UNSOUND (it would upgrade any
// VIG-feasible incumbent to OPTIMUM even when `value > floor`, fabricating a
// false optimum), so it MUST NOT verify. trust-vc fails closed (does NOT return
// `Verified`): the obligation `(value <= floor && VIG) == VIG` is genuinely
// solver-checked and false when `value > floor` and `VIG` holds.
#[trust_vc::ensures(result == verify_all_constraints(constraints, assignment))]
pub fn optimum_upgrade_guard_drop_floor(
    value: i128,
    floor: i128,
    constraints: &[PbConstraint],
    assignment: &[bool],
) -> bool {
    value <= floor && verify_all_constraints(constraints, assignment)
}

// CONCRETE-WITNESS non-vacuity: the SAME gate decision with the VIG abstracted as
// a predicate over a SCALAR witness (so ay can construct a falsifying model —
// refuting an inequality whose only free terms are i128/BV128 + an uninterpreted
// bool needs no Seq-of-datatype model value, which is the documented ay model-
// construction boundary the `_drop_floor` control above runs into). Dropping the
// floor here yields a concrete `Counterexample` (`value > floor`, `vig == true`),
// pinning that the gate postcondition obligation is genuinely refuted, not merely
// left `Unknown`.
#[trust_vc::spec]
#[trust_vc::opaque]
fn vig_scalar(witness: i128) -> bool {
    false
}

#[trust_vc::ensures(result == vig_scalar(witness))]
pub fn optimum_upgrade_guard_scalar_drop_floor(value: i128, floor: i128, witness: i128) -> bool {
    value <= floor && vig_scalar(witness)
}
