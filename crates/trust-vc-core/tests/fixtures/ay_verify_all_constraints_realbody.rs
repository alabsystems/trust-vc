// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// =====================================================================
// NON-VACUOUS native-deductive verification of the REAL ay-pb Verified
// Incumbent Gate `verify_all_constraints` (eval.rs:11) — the actual
// BODY `constraints.iter().all(|c| eval_constraint(c, assignment))`
// carrying the actual functional-correctness `#[ensures]`, discharged by
// trust-vc on the pure-Rust `ay` SMT solver.
// =====================================================================
//
// WHAT THIS EXERCISES (the trust-vc capability built for the verdict chain):
//   The contract is the literal VIG soundness statement — `result` is TRUE iff
//   EVERY constraint is satisfied:
//
//       result == forall|i: usize| (i < constraints.len()) ==>
//                     eval_constraint(&constraints[i], assignment)
//
//   and the body is the real `Iterator::all` fold over the slice. The proof is
//   the make-or-break body<->spec link: trust-vc lowers
//
//       constraints.iter().all(|c| eval_constraint(c, assignment))
//
//   to the SAME bounded universal quantifier the contract spells out
//   (`forall|i| i < seq.len() ==> eval_constraint(&seq[i], assignment)`), so the
//   obligation `all_body == forall_spec` is alpha-equivalent and discharges. The
//   `.iter().all(..)` -> forall-over-Seq lowering (with slice indexing `seq[i]`
//   and `seq.len()`) is the new general capability; `&[PbConstraint]` resolves to
//   `Seq(Datatype PbConstraint)` via the registry-aware slice element resolution.
//
// HOW `eval_constraint` IS MODELED (Verus mechanism):
//   declared `#[trust_vc::spec] #[trust_vc::opaque]` — a PURE UNINTERPRETED
//   (congruent) predicate, NEVER `reveal!`-ed. The VIG-faithfulness property
//   being proven (`all == forall over the slice`) holds for an ARBITRARY such
//   predicate, hence for the real `eval_constraint` in particular. This is the
//   SAME sound "opaque spec fn, no reveal" abstraction the eval_constraint proof
//   uses for `eval_terms` (gate_and_eval_lemmas.rs / eval_verdict_realbody.rs);
//   it is exactly why the negative control below is REJECTED, not vacuously
//   accepted.
//
// HOW THIS IS VERIFIED (engine path, no Trust fork sysroot required):
//   `trust_vc_core::verify_function_from_file(<this file>, <fn name>)`. `Verified`
//   == ay returned UNSAT and the trust-vc-kernel accepted the proof.

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

// The per-constraint decision, modeled as an OPAQUE (uninterpreted, congruent)
// predicate. Its body is an inert placeholder — never revealed, never used.
#[trust_vc::spec]
#[trust_vc::opaque]
fn eval_constraint(constraint: &PbConstraint, assignment: &[bool]) -> bool {
    false
}

// ===========================================================================
// TARGET — verify_all_constraints (eval.rs:11), VERBATIM REAL BODY.
//
// CONTRACT: `result` is TRUE iff EVERY constraint is satisfied under the
// assignment (the universal quantifier over the slice). PROVES: the body's
// `.iter().all(..)` lowers to the identical bounded `forall`.
// ===========================================================================
#[trust_vc::ensures(result == forall|i: usize| (i < constraints.len()) ==>
    eval_constraint(&constraints[i], assignment))]
pub fn verify_all_constraints(constraints: &[PbConstraint], assignment: &[bool]) -> bool {
    constraints.iter().all(|c| eval_constraint(c, assignment))
}

// NEGATIVE CONTROL — the WRONG (existential) gate: claims `result` is TRUE iff
// SOME constraint is satisfied. This is the unsound reading that would pass a
// MODEL violating a constraint, so it MUST NOT verify. trust-vc fails closed
// here (the `forall` body and the `exists` spec are NOT alpha-equivalent, so the
// equivalence is handed to ay, which returns a non-`Verified` verdict rather
// than admitting the false gate). Guards against a vacuous discharge of the VIG.
#[trust_vc::ensures(result == exists|i: usize| (i < constraints.len()) &&
    eval_constraint(&constraints[i], assignment))]
pub fn verify_all_constraints_wrong_exists(
    constraints: &[PbConstraint],
    assignment: &[bool],
) -> bool {
    constraints.iter().all(|c| eval_constraint(c, assignment))
}
