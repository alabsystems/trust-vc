// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// =====================================================================
// NON-VACUOUS NATIVE-DEDUCTIVE VERIFICATION of the REAL ay-pb verdict
// functions `eval_constraint` and `eval_objective_exact` — the actual
// solver.rs BODIES, carrying the actual functional-correctness
// `#[ensures]`, discharged by trust-vc (the first-party Verus-style
// verifier) on the pure-Rust `ay` SMT solver (i128 => BV128), with the
// proof re-checked by the independent trust-vc-kernel.
// =====================================================================
//
// WHAT MAKES THIS DIFFERENT FROM THE SURROGATE LEMMAS
// (`gate_and_eval_lemmas.rs` / `ay_real_gate_eval_lemmas.rs`):
//   The surrogate lemmas model `eval_constraint`'s DECISION on a SYMBOLIC
//   `lhs: i128` parameter. Here the contract CALLS `eval_terms` and the
//   function BODY also calls `eval_terms`, so the obligation is the literal
//   `result == match c.rel { Ge => eval_terms(&c.terms,a) >= c.rhs, Eq => … }`
//   over the REAL body `let lhs = eval_terms(&c.terms,a); match c.rel { … }`.
//   The proof is non-vacuous ONLY because the body's `eval_terms(&c.terms,a)`
//   and the spec's `eval_terms(&c.terms,a)` are the SAME uninterpreted symbol
//   applied to the SAME (provably equal) arguments — function CONGRUENCE is the
//   make-or-break link. trust-vc capabilities exercised, all on the REAL types:
//     1. MATCH over the fieldless enum `PbRel` -> ite over the discriminant.
//     2. SPEC-FN CALLS in a contract AND the body (`eval_terms`,
//        `eval_terms_checked`) lowered to a congruent uninterpreted application.
//     3. i128/BV128 integer theory for the `>= / ==` decision and the
//        `Result<i128, ObjectiveEvalError>` carrier.
//
// HOW `eval_terms` / `eval_terms_checked` ARE MODELED (Verus mechanism):
//   declared `#[trust_vc::spec] #[trust_vc::opaque]` and NEVER `reveal!`-ed, so
//   they are PURE UNINTERPRETED functions: the proof uses ONLY their
//   determinism (congruence — equal args => equal result), NEVER their bodies
//   (the `0i128` placeholder bodies are inert). Proving the contract for an
//   ARBITRARY such function proves it for the real fold in particular. This is
//   the sound "opaque spec fn, no reveal" abstraction; it is exactly why the
//   negative controls below are never accepted. Controls whose falsifying
//   values are inside the current model-extraction fragment are concretely
//   refuted; the exact UF-sequence wrong body fails closed as a model-less
//   `NotProved` when AY cannot extract its witness.
//
// HOW THIS IS VERIFIED (engine path, no Trust fork sysroot required):
//   `trust_vc_core::verify_function_from_file(<this file>, <fn name>)` parses
//   THIS file, collects the type defs into the source registry, lowers each
//   function to typed IR (i128 => BV128, PbConstraint/PbRel/… => native SMT
//   datatypes, Vec<PbTerm>/&[PbTerm] => Seq(Datatype), Result<…> => the Result
//   datatype carrier), encodes the verification condition to `ay`, refutes the
//   negation, and re-checks the UNSAT proof in trust-vc-kernel. `Verified` ==
//   ay returned UNSAT and the kernel accepted the proof; `Counterexample` == ay
//   returned a concrete falsifying model.

// ---------------------------------------------------------------------------
// Real ay-pb types — verbatim shape from crates/ay-pb/src/types.rs and the
// `ObjectiveEvalError` from solver.rs.
// ---------------------------------------------------------------------------
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PbObjective {
    pub terms: Vec<PbTerm>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ObjectiveEvalError {
    Overflow,
}

// ---------------------------------------------------------------------------
// The pure folds, modeled as OPAQUE (uninterpreted, congruent) spec functions.
// The bodies are inert placeholders — never revealed, never used by any proof.
// ---------------------------------------------------------------------------
#[trust_vc::spec]
#[trust_vc::opaque]
fn eval_terms(terms: &[PbTerm], assignment: &[bool]) -> i128 {
    0i128
}

#[trust_vc::spec]
#[trust_vc::opaque]
fn eval_terms_checked(terms: &[PbTerm], assignment: &[bool]) -> Result<i128, ObjectiveEvalError> {
    Ok(0i128)
}

#[trust_vc::spec]
#[trust_vc::opaque]
fn eval_terms_saturating(
    terms: &[PbTerm],
    assignment: &[bool],
) -> Result<i128, ObjectiveEvalError> {
    Ok(0i128)
}

// The per-literal variable lookup `assignment.get(lit.var - 1)` (defaulting to
// false), modeled as an OPAQUE (uninterpreted, congruent) bool function. The
// `eval_lit` NEGATION logic below is verified against an ARBITRARY such lookup,
// so it holds for the real bounds-checked `assignment.get(..)` in particular.
#[trust_vc::spec]
#[trust_vc::opaque]
fn lit_value(lit: PbLit, assignment: &[bool]) -> bool {
    false
}

// ===========================================================================
// TARGET 1 — eval_constraint (solver.rs:15), VERBATIM REAL BODY.
//
// CONTRACT: `result` is EXACTLY the Ge/Eq decision over the i128 term sum.
// Discharges because the body's `lhs == eval_terms(&c.terms,a)` and the spec's
// `eval_terms(&c.terms,a)` are the same congruent symbol, so both sides reduce
// to the identical match. PROVES (correct).
// ===========================================================================
#[trust_vc::ensures(result == match constraint.rel {
    PbRel::Ge => eval_terms(&constraint.terms, assignment) >= constraint.rhs,
    PbRel::Eq => eval_terms(&constraint.terms, assignment) == constraint.rhs,
})]
pub fn eval_constraint(constraint: &PbConstraint, assignment: &[bool]) -> bool {
    let lhs = eval_terms(&constraint.terms, assignment);
    let rhs = constraint.rhs;

    match constraint.rel {
        PbRel::Ge => lhs >= rhs,
        PbRel::Eq => lhs == rhs,
    }
}

// NEGATIVE CONTROL for TARGET 1 — same contract, WRONG body: the Ge arm decides
// with `>` instead of `>=`. The two disagree exactly when `lhs == rhs`, so the
// postcondition is FALSE and MUST FAIL CLOSED. AY cannot always extract a
// concrete model for the opaque UF application over sequence inputs, so this
// exact real-shape control admits the model-less `NotProved` verdict while
// guarding against a vacuous discharge of `eval_constraint`.
#[trust_vc::ensures(result == match constraint.rel {
    PbRel::Ge => eval_terms(&constraint.terms, assignment) >= constraint.rhs,
    PbRel::Eq => eval_terms(&constraint.terms, assignment) == constraint.rhs,
})]
pub fn eval_constraint_wrong_ge(constraint: &PbConstraint, assignment: &[bool]) -> bool {
    let lhs = eval_terms(&constraint.terms, assignment);
    let rhs = constraint.rhs;

    match constraint.rel {
        PbRel::Ge => lhs > rhs, // BUG: should be `>=`
        PbRel::Eq => lhs == rhs,
    }
}

// DECISIVE NEGATIVE CONTROL for TARGET 1 — isolates the same Ge decision
// boundary on explicit scalar inputs. This avoids asking model extraction to
// synthesize an opaque-UF-over-sequences value, while retaining the exact
// `>`-versus-`>=` semantic bug. The concrete witness is rel=Ge and lhs=rhs.
#[trust_vc::ensures(result == match rel {
    PbRel::Ge => lhs >= rhs,
    PbRel::Eq => lhs == rhs,
})]
pub fn eval_constraint_scalar_wrong_ge(lhs: i128, rel: PbRel, rhs: i128) -> bool {
    match rel {
        PbRel::Ge => lhs > rhs, // BUG: should be `>=`
        PbRel::Eq => lhs == rhs,
    }
}

// ===========================================================================
// TARGET 1b — eval_lit (solver.rs:182, the `litVal`-with-negation), VERBATIM
// REAL BODY shape `let value = <lookup>; if lit.negated { !value } else { value }`.
//
// CONTRACT: the per-literal value flips EXACTLY under the `negated` flag — the
// soundness primitive every PB term sum is built from (a dropped/mis-applied
// negation silently corrupts every constraint and objective evaluation). The
// proof is non-vacuous because the body's `value` and the spec's
// `lit_value(lit, assignment)` are the same congruent symbol, so the obligation
// reduces to `result == if lit.negated { !v } else { v }` over the real PbLit
// datatype (the `lit.negated` field read is a datatype selector). PROVES.
//
// trust-vc capability this exercises: the body's `let value = ..; if lit.negated
// { !value } else { value }` return tail is an `if`/`else` over a LET-bound
// local; lowering it as the `result ==` obligation requires scope-substituting
// the let binding through BOTH branch arms (the `Expr::If` return-tail rendering
// built for this proof — without it the encoder rejects the obligation with
// "unresolved variable `value`").
// ===========================================================================
#[trust_vc::ensures(result == (if lit.negated {
    !lit_value(lit, assignment)
} else {
    lit_value(lit, assignment)
}))]
pub fn eval_lit(lit: PbLit, assignment: &[bool]) -> bool {
    let value = lit_value(lit, assignment);
    if lit.negated { !value } else { value }
}

// NEGATIVE CONTROL for TARGET 1b — same contract, WRONG body: ignores the
// `negated` flag entirely (returns the raw looked-up value). This disagrees with
// the contract exactly when `lit.negated` holds, so it MUST be REFUTED with a
// CONCRETE counterexample binding `lit = PbLit { var, negated: true }` and
// `lit_value(lit, assignment) = true` (correct = false, wrong = true). Guards
// against a vacuous discharge of `eval_lit` and exhibits AY constructing a
// concrete falsifying PbLit datatype value.
#[trust_vc::ensures(result == (if lit.negated {
    !lit_value(lit, assignment)
} else {
    lit_value(lit, assignment)
}))]
pub fn eval_lit_ignore_negation(lit: PbLit, assignment: &[bool]) -> bool {
    lit_value(lit, assignment) // BUG: drops the `if lit.negated { !value }` flip
}

// ===========================================================================
// TARGET 2 — eval_objective_exact (solver.rs:40), VERBATIM REAL BODY.
//
// CONTRACT: the result is EXACTLY the checked accumulating fold (fail-closed,
// never silently wrapped/saturated). Discharges by congruence: body and spec
// are the same `eval_terms_checked(&objective.terms, assignment)`. PROVES.
// ===========================================================================
#[trust_vc::ensures(result == eval_terms_checked(&objective.terms, assignment))]
pub fn eval_objective_exact(
    objective: &PbObjective,
    assignment: &[bool],
) -> Result<i128, ObjectiveEvalError> {
    eval_terms_checked(&objective.terms, assignment)
}

// NEGATIVE CONTROL for TARGET 2 — same body, deliberately WRONG (negated)
// contract: it claims the result is NEVER the checked fold. Since the body IS
// the checked fold, `result != eval_terms_checked(..)` is `X != X`, which MUST
// be REFUTED. Proves the `eval_objective_exact` postcondition obligation is
// genuinely solver-checked (non-vacuous), not silently dropped.
#[trust_vc::ensures(result != eval_terms_checked(&objective.terms, assignment))]
pub fn eval_objective_exact_negated_contract(
    objective: &PbObjective,
    assignment: &[bool],
) -> Result<i128, ObjectiveEvalError> {
    eval_terms_checked(&objective.terms, assignment)
}

// SATURATING-SUBSTITUTION CONTROL for TARGET 2 — the correct contract is
// `result == eval_terms_checked(..)` but the body returns the SATURATING fold.
// This is UNSOUND (saturation clamps instead of failing closed, fabricating a
// smaller objective and a false `OptimumFound`), so it MUST NOT verify. Refuting
// it is the NAMED model-construction gap: the obligation negation
// `eval_terms_saturating(..) != eval_terms_checked(..)` is a disequality between
// two DISTINCT `Result<i128,_>`-valued uninterpreted-function applications, which
// AY must SATISFY by giving them distinct datatype values. With the SAT-direction
// datatype model-distinguishability built for this task (assumption-rooted
// element synthesis + the opaque-disequality acceptance `dt_diseq_opaque_
// satisfiable`), AY now returns a concrete `Counterexample` here instead of
// `Unknown`. (The `_distinguishable_bare` companion below exhibits the concrete
// `result = @Result<..>!0` binding directly.)
#[trust_vc::ensures(result == eval_terms_checked(&objective.terms, assignment))]
pub fn eval_objective_exact_wrong_saturating(
    objective: &PbObjective,
    assignment: &[bool],
) -> Result<i128, ObjectiveEvalError> {
    eval_terms_saturating(&objective.terms, assignment) // BUG: should be the checked fold
}

// CONCRETE-WITNESS form of the saturating-substitution gap, stated at the
// `eval_terms`/`&[PbTerm]` level (no `PbObjective` wrapper) so the falsifying
// model binds the function's own `result`. The contract claims the SATURATING
// fold equals the CHECKED fold; the body IS the saturating fold, so the
// obligation negation is `eval_terms_saturating(terms,a) != eval_terms_checked(
// terms,a)` — two distinct `Result<i128,_>`-valued UF applications. AY refutes it
// with a CONCRETE datatype counterexample binding `result` (the saturating fold's
// value) to a concrete `Result` element distinct from the checked fold's value —
// the SAT-direction datatype model construction this task built. MUST be refuted.
#[trust_vc::ensures(result == eval_terms_checked(terms, assignment))]
pub fn eval_terms_saturating_distinguishable_bare(
    terms: &[PbTerm],
    assignment: &[bool],
) -> Result<i128, ObjectiveEvalError> {
    eval_terms_saturating(terms, assignment) // BUG: distinguishable from the checked fold
}
