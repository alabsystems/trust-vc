// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// =====================================================================
// NON-VACUOUS native-deductive lift of the in-production cutting-planes
// REFUTATION SELF-CHECK from PER-STEP soundness to WHOLE-LOOP soundness.
// The checker `Refutation::check` / `replay_derivation`
// (crates/ay-pb/src/proof/refutation_check.rs) runs a LOOP that applies
// `RefStep`s, merging per-variable coefficients in a `BTreeMap`, until the
// accumulated constraint is `0 >= c` (`c >= 1`). The PER-STEP rules
// (`add`/`scale`/`divide_ceil`/`saturate`/`is_contradiction`) are already
// proven entailment-preserving in `refutation_step_realbody.rs` /
// `saturate_step_realbody.rs`. This fixture lifts that to the LOOP:
//   it proves the LOOP INVARIANT "every constraint the loop has derived is
//   ENTAILED by the original input DB" is PRESERVED by each iteration (using
//   the proven per-step rules), and that terminating at `0 >= c (c>=1)`
//   ENTAILS the inputs are UNSAT. Discharged by trust-vc on the pure-Rust
//   `ay` SMT solver, kernel-rechecked.
// =====================================================================
//
// THE ENTAILMENT MODEL (how a "loop invariant" is stated to trust-vc)
// ------------------------------------------------------------------
// Fix an arbitrary assignment `x`. Write `db_sat` for "x satisfies EVERY original
// input constraint". A normalized `>=` constraint with LHS value `eval` at `x` and
// degree `rhs` HOLDS at `x` iff `eval >= rhs`. A derived constraint is ENTAILED by
// the inputs iff it holds at every `x` that satisfies the inputs — i.e.
// `db_sat ==> (eval >= rhs)`. The loop invariant of `replay_derivation` is then:
//
//     for every constraint currently in `db`,   db_sat ==> (eval >= rhs).
//
// On entry `db == inputs`, so the invariant is the definition of `db_sat`. Each
// iteration pushes ONE constraint computed by a kernel rule from earlier `db`
// entries; PRESERVATION is: the pushed constraint is again `db_sat`-entailed. The
// proven per-step rules supply exactly the arithmetic that closes this.
//
// SCOPE — WHAT IS AND IS NOT THE UNBOUNDED BTreeMap LOOP
// -----------------------------------------------------
// trust-vc's loop reasoning is a frame-condition inductive step; it does not
// encode the unbounded `Vec<LinConstraint>`-of-`BTreeMap` heap mutation of the
// real `db.push(..)` loop. So the lift is delivered as:
//   (i)  the INVARIANT-PRESERVATION step (the crux), proven per rule and once
//        rule-AGNOSTICALLY (entailment is closed under any sound step), composing
//        the per-step arithmetic already proven elsewhere; and
//   (ii) an ACTUAL trust-vc `while`-loop, verified by the engine's inductive
//        machinery, that maintains the entailment invariant across an ARBITRARY
//        (symbolic `n`) number of homogeneous ADD iterations — the iteration
//        count is unbounded; what is bounded/abstracted is the heterogeneous
//        match-dispatch and the coefficient `BTreeMap` (collapsed to the LHS
//        value `eval` at the fixed point); and
//   (iii) a concrete BOUNDED-N END-TO-END replay of the canonical 3-cycle parity
//        refutation (the `parity_contradiction_checks_positive` test) at a fixed
//        point, deriving `0 >= 1` and hence UNSAT.
// The `while`-loop in (ii) was the toolchain GATE: the frame-condition inductive
// step dropped the function preconditions, so the entailment of the
// repeatedly-added step (`step_eval >= step_rhs`, over loop-INVARIANT params) was
// havoc'd away and the invariant refuted. trust-vc was extended to CARRY
// preconditions over UNMODIFIED (frame-preserved) variables into the inductive
// step (sound: such a predicate has one truth value for the whole call); see
// `crates/trust-vc-core/.../invariants/frame_condition.rs` and the regression
// `loop_invariant_unmodified_precondition_soundness.rs`.
//
// WHY THE LEMMAS ARE OVER `int` (Verus ℤ), NOT i128 — identical to the per-step
// fixture: the checker uses i128 `checked_*` + `?`, so any overflow REJECTS the
// step (`RefError::BadStep`); every ACCEPTED step did exact ℤ arithmetic.
//
// HOW THIS IS VERIFIED: `trust_vc_core::verify_function_from_file(<this file>,
// <fn>)`. `Verified` == ay returned UNSAT and the trust-vc-kernel accepted the
// proof; `Counterexample` == ay returned a concrete falsifying model.

// =====================================================================
// VERBATIM real checker LOOP source (copied from crates/ay-pb/src/proof/
// refutation_check.rs; the conformance test byte-pins these blocks to the live
// source). This is the loop whose invariant the proofs below lift.
// =====================================================================
//
// --- Refutation::check (refutation_check.rs:299-306) ---
// CONFORMANCE: src/proof/refutation_check.rs:299-306
//     pub fn check(&self) -> Result<(), RefError> {
//         let last = replay_derivation(&self.inputs, &self.steps)?;
//         if last.is_contradiction() {
//             Ok(())
//         } else {
//             Err(RefError::NotContradiction)
//         }
//     }
//
// --- replay_derivation (refutation_check.rs:315-347) ---
// CONFORMANCE: src/proof/refutation_check.rs:315-347
// pub(crate) fn replay_derivation(
//     inputs: &[LinConstraint],
//     steps: &[RefStep],
// ) -> Result<LinConstraint, RefError> {
//     if steps.is_empty() {
//         return Err(RefError::Empty);
//     }
//     let mut db: Vec<LinConstraint> = inputs.to_vec();
//     for (idx, step) in steps.iter().enumerate() {
//         let derived = match *step {
//             RefStep::Add(i, j) => {
//                 let a = db.get(i).ok_or(RefError::BadRef { step: idx })?;
//                 let b = db.get(j).ok_or(RefError::BadRef { step: idx })?;
//                 a.add(b).ok_or(RefError::BadStep { step: idx })?
//             }
//             RefStep::Scale(i, k) => {
//                 let a = db.get(i).ok_or(RefError::BadRef { step: idx })?;
//                 a.scale(k).ok_or(RefError::BadStep { step: idx })?
//             }
//             RefStep::Divide(i, d) => {
//                 let a = db.get(i).ok_or(RefError::BadRef { step: idx })?;
//                 a.divide_ceil(d).ok_or(RefError::BadStep { step: idx })?
//             }
//             RefStep::Saturate(i) => {
//                 let a = db.get(i).ok_or(RefError::BadRef { step: idx })?;
//                 a.saturate().ok_or(RefError::BadStep { step: idx })?
//             }
//         };
//         db.push(derived);
//     }
//     // `db` is non-empty here (inputs may be empty but steps >= 1 appended).
//     Ok(db.last().expect("at least one derived step").clone())
// }
// =====================================================================

// ---------------------------------------------------------------------------
// Kernel-trivial ring axiom (same as refutation_step_realbody.rs): right-
// multiplication monotonicity, the NIA fact ay cannot derive itself. Trusted
// body (`external_body`); its `#[requires]` is CHECKED at the call site.
// ---------------------------------------------------------------------------
#[trust_vc::external_body]
#[trust_vc::requires(lo <= hi && f >= 0)]
#[trust_vc::ensures(lo * f <= hi * f)]
pub fn lemma_mul_le_mono_right(lo: int, hi: int, f: int) {}

// ===========================================================================
// (i) INVARIANT PRESERVATION — per rule. At a fixed point, the operands are the
// `db` entries the step reads; their ENTAILMENT `db_sat ==> eval >= rhs` is the
// inductive HYPOTHESIS. Each lemma proves the PUSHED constraint is again entailed,
// composing the proven per-step arithmetic (add/scale/divide). This is the body
// of the loop's inductive step, the soundness CRUX of the whole-loop lift.
// ===========================================================================

/// PRESERVATION for ADD. Pushed constraint has LHS value `eval_a + eval_b` and
/// degree `rhs_a + rhs_b` (`impliedGe_add`, refutation_check.rs:127-134). If both
/// operands are entailed, so is the sum. PROVES.
#[trust_vc::ensures(
    ((db_sat ==> eval_a >= rhs_a) && (db_sat ==> eval_b >= rhs_b))
        ==> (db_sat ==> result >= rhs_a + rhs_b)
)]
pub fn invariant_preserved_add(
    db_sat: bool,
    eval_a: int,
    rhs_a: int,
    eval_b: int,
    rhs_b: int,
) -> int {
    eval_a + eval_b
}

/// NON-VACUITY CONTROL for ADD preservation — overclaim the pushed degree by 1.
/// REFUTED (operands entailed, `db_sat` holds, both tight: result == rhs_a+rhs_b).
#[trust_vc::ensures(
    ((db_sat ==> eval_a >= rhs_a) && (db_sat ==> eval_b >= rhs_b))
        ==> (db_sat ==> result >= rhs_a + rhs_b + 1)
)]
pub fn invariant_preserved_add_overclaim(
    db_sat: bool,
    eval_a: int,
    rhs_a: int,
    eval_b: int,
    rhs_b: int,
) -> int {
    eval_a + eval_b
}

/// PRESERVATION for SCALE (`k >= 1`). Pushed constraint has LHS `k * eval_a` and
/// degree `k * rhs_a` (`impliedGe_scale`, refutation_check.rs:137-146). If the
/// operand is entailed then so is the scaled fact, via the monotonicity axiom
/// (`rhs_a <= eval_a`, `k >= 0`). PROVES.
#[trust_vc::ensures(
    (k >= 1 && (db_sat ==> eval_a >= rhs_a)) ==> (db_sat ==> result >= k * rhs_a)
)]
pub fn invariant_preserved_scale(db_sat: bool, k: int, eval_a: int, rhs_a: int) -> int {
    if db_sat && k >= 1 && eval_a >= rhs_a {
        lemma_mul_le_mono_right(rhs_a, eval_a, k);
    }
    k * eval_a
}

/// NON-VACUITY CONTROL for SCALE preservation (lemma is load-bearing) — SAME body
/// and contract WITHOUT the monotonicity lemma. ay cannot derive the nonlinear
/// `k*eval_a >= k*rhs_a`, so this MUST NOT verify (non-vacuous discharge).
#[trust_vc::ensures(
    (k >= 1 && (db_sat ==> eval_a >= rhs_a)) ==> (db_sat ==> result >= k * rhs_a)
)]
pub fn invariant_preserved_scale_no_lemma(db_sat: bool, k: int, eval_a: int, rhs_a: int) -> int {
    k * eval_a
}

/// PRESERVATION for DIVIDE by `d = 2` (`impliedGe_division`,
/// refutation_check.rs:150-159). The coefficient `BTreeMap` merge is collapsed to
/// the divided LHS value `div_eval` and degree `div_rhs` at the fixed point, with
/// the proven per-step facts supplied as preconditions:
///   * `2 * div_eval >= eval_a` — the per-coefficient ceiling DOMINATION
///     `2*ceil(c/2) >= c` (`ceil_div_by2_rounds_up`, proven in
///     refutation_step_realbody.rs) summed over `x >= 0`; and
///   * `2 * div_rhs >= rhs_a && 2 * div_rhs <= rhs_a + 1` — `div_rhs == ceil(rhs_a/2)`.
/// Then operand entailment `db_sat ==> eval_a >= rhs_a` lifts to the divided
/// constraint: `2*div_eval >= eval_a >= rhs_a` and `2*div_rhs <= rhs_a + 1` give
/// `div_eval >= div_rhs` over ℤ. PROVES.
#[trust_vc::requires(2 * div_eval >= eval_a)]
#[trust_vc::requires(2 * div_rhs >= rhs_a && 2 * div_rhs <= rhs_a + 1)]
#[trust_vc::ensures((db_sat ==> eval_a >= rhs_a) ==> (db_sat ==> result >= div_rhs))]
pub fn invariant_preserved_divide2(
    db_sat: bool,
    eval_a: int,
    rhs_a: int,
    div_eval: int,
    div_rhs: int,
) -> int {
    div_eval
}

/// NON-VACUITY CONTROL for DIVIDE preservation — DROP the per-coefficient
/// domination premise (`2 * div_eval >= eval_a`). Without it the divided LHS is
/// unconstrained vs the operand, so the divided fact need not be entailed.
/// REFUTED (e.g. operand tight, `div_eval` far below `div_rhs`).
#[trust_vc::requires(2 * div_rhs >= rhs_a && 2 * div_rhs <= rhs_a + 1)]
#[trust_vc::ensures((db_sat ==> eval_a >= rhs_a) ==> (db_sat ==> result >= div_rhs))]
pub fn invariant_preserved_divide2_drop_domination(
    db_sat: bool,
    eval_a: int,
    rhs_a: int,
    div_eval: int,
    div_rhs: int,
) -> int {
    div_eval
}

// ===========================================================================
// (i') INVARIANT PRESERVATION — rule-AGNOSTIC crux. The cleanest statement that
// the per-step rules LIFT to the loop: entailment by the inputs is CLOSED under
// any SOUND step. Given the two operands are entailed (`db_sat ==> *_holds`) and
// the rule is sound at the point (`op_a_holds && op_b_holds ==> derived_holds` —
// exactly what add/scale/divide/saturate each prove), the pushed constraint is
// entailed. PROVES (propositional); holds for EVERY rule, hence preserves the loop
// invariant whatever step the loop applies.
// ===========================================================================
#[trust_vc::ensures(
    ((db_sat ==> op_a_holds) && (db_sat ==> op_b_holds)
        && (op_a_holds && op_b_holds ==> derived_holds))
        ==> (db_sat ==> result)
)]
pub fn invariant_preserved_general(
    db_sat: bool,
    op_a_holds: bool,
    op_b_holds: bool,
    derived_holds: bool,
) -> bool {
    derived_holds
}

/// NON-VACUITY CONTROL for the crux — DROP the rule-soundness conjunct
/// (`op_a_holds && op_b_holds ==> derived_holds`). Entailment is NOT closed under
/// an arbitrary (possibly unsound) step. REFUTED (`db_sat`, both operands hold,
/// `derived_holds == false`).
#[trust_vc::ensures(
    ((db_sat ==> op_a_holds) && (db_sat ==> op_b_holds)) ==> (db_sat ==> result)
)]
pub fn invariant_preserved_general_drop_rule(
    db_sat: bool,
    op_a_holds: bool,
    op_b_holds: bool,
    derived_holds: bool,
) -> bool {
    derived_holds
}

// ===========================================================================
// (ii) THE WHOLE LOOP — engine-verified inductive proof. An ACTUAL trust-vc
// `while` loop that mirrors `replay_derivation`'s accumulate-and-continue shape:
// `acc_eval`/`acc_rhs` are the running derived constraint's LHS value and degree
// at the fixed point; each iteration ADDs one entailed step (`step_eval`/
// `step_rhs`, the loop-INVARIANT consequence of `db_sat`). The loop INVARIANT
// `acc_eval >= acc_rhs` ("the accumulated derived constraint still holds at x, so
// it stays entailed by the inputs") is maintained across an ARBITRARY (symbolic
// `n`) number of iterations. Verified by trust-vc's frame-condition inductive
// step (using the preconditions-over-unmodified-vars capability built for this).
// ===========================================================================
#[trust_vc::requires(acc_eval >= acc_rhs)]
#[trust_vc::requires(step_eval >= step_rhs)]
#[trust_vc::ensures(acc_eval >= acc_rhs)]
pub fn replay_accumulate_entailed(
    mut acc_eval: int,
    mut acc_rhs: int,
    step_eval: int,
    step_rhs: int,
    mut k: int,
    n: int,
) {
    while k < n {
        trust_vc::invariant!(acc_eval >= acc_rhs);
        acc_eval = acc_eval + step_eval;
        acc_rhs = acc_rhs + step_rhs;
        k = k + 1;
    }
}

/// NON-VACUITY CONTROL for the loop — DROP the step-entailment precondition
/// (`step_eval >= step_rhs`). The added step may lower the accumulator below its
/// degree, so the invariant is NOT preserved. REFUTED at the inductive step.
#[trust_vc::requires(acc_eval >= acc_rhs)]
#[trust_vc::ensures(acc_eval >= acc_rhs)]
pub fn replay_accumulate_unsound(
    mut acc_eval: int,
    mut acc_rhs: int,
    step_eval: int,
    step_rhs: int,
    mut k: int,
    n: int,
) {
    while k < n {
        trust_vc::invariant!(acc_eval >= acc_rhs);
        acc_eval = acc_eval + step_eval;
        acc_rhs = acc_rhs + step_rhs;
        k = k + 1;
    }
}

// ===========================================================================
// (ii-LIT) THE LITERAL `Vec`-PUSH LOOP — engine-verified over the ACTUAL heap
// mutation. Unlike (ii)'s SCALAR `acc_eval` abstraction, this drives trust-vc's
// frame-condition inductive step over the REAL growing `Vec` `db` mutated by
// `db.push(..)` — the literal shape of `replay_derivation`
// (refutation_check.rs:322-343). `db` is the running derivation DB; each element
// is the SLACK `eval - rhs` of a derived constraint at a fixed feasible point (the
// per-constraint coefficient `BTreeMap` collapsed to that slack — the SAME
// abstraction (ii) makes, now applied per-ELEMENT of the literal Vec). Across an
// ARBITRARY (symbolic `n`) number of `db.push` iterations the engine carries:
//   * EXACT GROWTH `db.len() == start + count` — the DB grows by exactly one
//     derived constraint per replay step (one `db.push(derived)` per step); and
//   * APPENDED-ENTAILED `db.index(db.len()-1) == step && step >= 0` — the pushed
//     constraint IS the entailed step (its slack is non-negative).
//
// THIS WAS PREVIOUSLY IMPOSSIBLE: a `db.push(..)` loop body left `db` FULLY
// havoc'd (the single-iteration transition capture admitted only flat SCALAR
// assignments), so NO invariant about the literal Vec was inductive — every such
// invariant came back Unknown. trust-vc was extended to CAPTURE the collection
// `push` single-iteration transition `db == db_pre.push(value)`
// (vc_extraction/body_extract.rs: `stmt_is_flat_scalar_assignment_or_spec` now
// also admits a flat `db.push(<pure>)` re-binding), threading the push facts
// (len+1, appended element, element preservation) into the frame-condition step.
//
// FULLY-QUANTIFIED invariant (was the disclosed residual): the per-element
// `forall i: (i < db.len()) ==> db.index(i) is entailed` is now DISCHARGED — over
// the opaque Int-domain family in (ii-FQ), AND over the ACTUAL `Vec<i128>` object
// (`db.index(i)` == `select db (int2bv_64 i)`) in (ii-FQ-LIT), which CLOSES the
// disclosed residual #2. The ay-dpll forall-GOAL boundary limitation that blocked
// it (the skolemized boundary index `k = old_len` was not pinned across the
// inductive push) is FIXED (ground integer strict-bound normalization;
// crates/ay-dpll/.../forall_goal_int_boundary_discharge.rs), and the literal
// `select db (int2bv old_len)` boundary read is pinned by the int2bv/bv2nat
// forward range-injectivity bridge. The per-STEP appended-entailment + exact
// growth here remain the literal-`Vec` content trust-vc discharges over the ACTUAL
// `db.push`; (ii-FQ)/(ii-FQ-LIT) lift them to the whole-db universal.
// ===========================================================================

// CONFORMANCE: src/proof/refutation_check.rs:322-323
//     let mut db: Vec<LinConstraint> = inputs.to_vec();
//     for (idx, step) in steps.iter().enumerate() {
// CONFORMANCE: src/proof/refutation_check.rs:343-343
//         db.push(derived);

/// EXACT GROWTH of the literal `db` Vec across the unbounded push loop:
/// `db.len() == start + count` is maintained by the engine's inductive step over
/// the REAL `db.push(..)` (using the captured push transition `db.len() ==
/// db_pre.len() + 1`). PROVES.
#[trust_vc::requires(db.len() == start)]
#[trust_vc::requires(count == 0)]
pub fn replay_push_db_grows_exact(mut db: Vec<i128>, start: int, mut count: int, n: int) {
    while count < n {
        trust_vc::invariant!(db.len() == start + count);
        db.push(0i128);
        count = count + 1;
    }
}

/// NON-VACUITY CONTROL for exact growth — overclaim the length by one
/// (`start + count + 1`). The push grows `db` by exactly one, so the claim is
/// false on entry. REFUTED with a concrete counterexample.
#[trust_vc::requires(db.len() == start)]
#[trust_vc::requires(count == 0)]
pub fn replay_push_db_grows_exact_overclaim(
    mut db: Vec<i128>,
    start: int,
    mut count: int,
    n: int,
) {
    while count < n {
        trust_vc::invariant!(db.len() == start + count + 1);
        db.push(0i128);
        count = count + 1;
    }
}

/// MONOTONE GROWTH of the literal `db` Vec: `db.len() >= start` is maintained
/// across the push loop (the DB never shrinks). PROVES.
#[trust_vc::requires(db.len() >= start)]
pub fn replay_push_db_monotone(mut db: Vec<i128>, start: int, mut count: int, n: int) {
    while count < n {
        trust_vc::invariant!(db.len() >= start);
        db.push(0i128);
        count = count + 1;
    }
}

/// APPENDED-ENTAILED: each replay step pushes an ENTAILED constraint — its slack
/// `step` (`>= 0`) lands at the new last slot `db.index(db.len()-1)`. Verified
/// over the literal `db.push(step)` via the captured push transition's
/// appended-element fact. PROVES (composes with exact growth).
#[trust_vc::requires(step >= 0i128)]
#[trust_vc::requires(db.len() == start)]
#[trust_vc::requires(count == 0)]
pub fn replay_push_appends_entailed(
    mut db: Vec<i128>,
    step: i128,
    start: int,
    mut count: int,
    n: int,
) {
    while count < n {
        trust_vc::invariant!(db.len() == start + count);
        db.push(step);
        trust_vc::assert!(db.index(db.len() - 1) == step);
        trust_vc::assert!(db.index(db.len() - 1) >= 0i128);
        count = count + 1;
    }
}

/// NON-VACUITY CONTROL for appended-entailment — DROP the step-entailment
/// precondition (`step >= 0`). A `db.push(step)` of a NON-entailed constraint
/// (negative slack) breaks the appended-element entailment, so the per-step
/// `db.index(db.len()-1) >= 0` is NOT provable. MUST NOT verify.
#[trust_vc::requires(db.len() == start)]
#[trust_vc::requires(count == 0)]
pub fn replay_push_appends_entailed_unsound(
    mut db: Vec<i128>,
    step: i128,
    start: int,
    mut count: int,
    n: int,
) {
    while count < n {
        trust_vc::invariant!(db.len() == start + count);
        db.push(step);
        trust_vc::assert!(db.index(db.len() - 1) >= 0i128);
        count = count + 1;
    }
}

// ===========================================================================
// (ii-FQ) THE FULLY-QUANTIFIED PER-ELEMENT INVARIANT — now DISCHARGED.
// The whole-loop invariant in its STRONGEST form: EVERY constraint currently in
// `db` is entailed by the inputs —
//     forall i. (0 <= i < db.len()) ==> (db_sat ==> slack(i) >= 0)
// where `slack(i) = eval_i - rhs_i` is the LHS-minus-degree of the i-th derived
// constraint at a fixed feasible point (the per-constraint coefficient `BTreeMap`
// collapsed to that slack — the SAME abstraction (ii)/(ii-LIT) make, now applied
// PER-ELEMENT under a universal). A derived constraint is entailed iff it holds at
// every `x` satisfying the inputs, i.e. `db_sat ==> slack >= 0`.
//
// This forall-OVER-the-whole-db invariant was the disclosed residual: maintaining
// it across one `db.push` extends the index range by one, and the NEW boundary
// index `db.len()` reads the just-appended element — which ay-dpll's forall-GOAL
// instantiation could not pin across the inductive step. That ay-dpll limitation
// is now FIXED (ground integer strict-bound normalization pins the skolemized
// boundary `k = old_len`; see crates/ay-dpll/tests/group_quantifiers/
// forall_goal_int_boundary_discharge.rs), so the per-element invariant maintained
// across the append now DISCHARGES (`fq_invariant_preserved_append`, PROVES).
//
// CARRIER NOTE — why the db is modeled as an INDEXED FAMILY here. trust-vc lowers
// a literal `Vec<i128>` to a BV-INDEXED SMT array; `db.push` stores at
// `int2bv(old_len)` and relates pre/post `db` through an element-preservation
// forall. The (ii-FQ) lemmas in THIS section route the per-element universal
// through the opaque Int-domain family `db_slack_at: int -> int` — the SAME slack
// abstraction indexed by an Int position, the carrier the ay-dpll forall-goal fix
// was first validated on. They retain the CLEAN concrete-counterexample controls
// (`db_slack_at` is uninterpreted, so a dropped premise yields an explicit
// falsifying model), pinning the LOGIC of the lift as non-vacuous.
//
// The SAME universal is now ALSO discharged over the ACTUAL `Vec<i128>` object —
// the quantifier body is the literal `db.index(i)` (lowered to
// `select db (int2bv_64 i)` over the real `db : (Array (BitVec 64) (BitVec 128))`,
// NOT an opaque function) — in the (ii-FQ-LIT) section below. That CLOSES the
// disclosed residual #2 (the per-element invariant over the literal carrier was
// previously Unknown), including residual #2(a) (folding the ground length
// equation `db.len() == old_len + 1` into the boundary bound). Composing (ii-FQ-
// LIT) with the literal-`Vec` (ii-LIT) proofs (exact growth + appended-entailment
// over the ACTUAL `db.push`) lifts the WHOLE loop with the fully-quantified
// invariant ABOUT THE REAL Vec.
// ===========================================================================

/// The i-th derived constraint's SLACK (`eval_i - rhs_i`) at a fixed feasible
/// point — OPAQUE (uninterpreted), the same abstraction the per-step rules reason
/// about. The FQ invariant holds for an ARBITRARY such family, hence for the real
/// derivation DB; opaqueness is exactly why the controls below are REFUTED, not
/// vacuously accepted.
#[trust_vc::spec]
#[trust_vc::opaque]
fn db_slack_at(i: int) -> int {
    0
}

/// PRESERVATION of the FULLY-QUANTIFIED invariant across ONE `db.push`. Inductive
/// hypothesis: every element in `[0, old_len)` is entailed (`db_sat ==> slack >= 0`);
/// the appended element at index `old_len` is entailed; THEN every element in
/// `[0, old_len + 1)` is entailed — the invariant on the grown db. The boundary
/// index `old_len` (the just-pushed element) is pinned by the ay-dpll forall-goal
/// fix. PROVES. (`probe` only anchors `db_slack_at`'s return type; it adds no
/// entailment information.)
#[trust_vc::requires(old_len >= 0)]
#[trust_vc::requires(probe == db_slack_at(old_len))]
#[trust_vc::requires(db_sat ==> db_slack_at(old_len) >= 0)]
#[trust_vc::requires(forall|i: int| (0 <= i && i < old_len) ==> (db_sat ==> db_slack_at(i) >= 0))]
#[trust_vc::ensures(forall|i: int| (0 <= i && i < old_len + 1) ==> (db_sat ==> db_slack_at(i) >= 0))]
pub fn fq_invariant_preserved_append(db_sat: bool, old_len: int, probe: int) {}

/// NON-VACUITY CONTROL for FQ preservation — DROP the appended-element entailment
/// premise (`db_sat ==> db_slack_at(old_len) >= 0`). A NON-entailed constraint
/// (negative slack) then enters `db` at the boundary, so the grown forall is
/// FALSE. REFUTED with a concrete counterexample (e.g. `db_sat`, `old_len = 0`,
/// `slack(0) < 0`): proves the per-step entailment premise is LOAD-BEARING — the
/// FQ discharge is NOT vacuous.
#[trust_vc::requires(old_len >= 0)]
#[trust_vc::requires(probe == db_slack_at(old_len))]
#[trust_vc::requires(forall|i: int| (0 <= i && i < old_len) ==> (db_sat ==> db_slack_at(i) >= 0))]
#[trust_vc::ensures(forall|i: int| (0 <= i && i < old_len + 1) ==> (db_sat ==> db_slack_at(i) >= 0))]
pub fn fq_invariant_preserved_append_unsound(db_sat: bool, old_len: int, probe: int) {}

/// TERMINAL CONNECTION — the FULLY-QUANTIFIED invariant INSTANTIATED at the last
/// slot: if every element in `[0, len)` is entailed then the LAST derived
/// constraint (index `len - 1`, the one `replay_derivation` returns and
/// `is_contradiction` inspects) is entailed. This universal-elimination is what
/// feeds `terminal_entails_unsat` from the whole-db invariant. PROVES.
#[trust_vc::requires(len >= 1)]
#[trust_vc::requires(probe == db_slack_at(len - 1))]
#[trust_vc::requires(forall|i: int| (0 <= i && i < len) ==> (db_sat ==> db_slack_at(i) >= 0))]
#[trust_vc::ensures(db_sat ==> db_slack_at(len - 1) >= 0)]
pub fn fq_invariant_implies_last_entailed(db_sat: bool, len: int, probe: int) {}

/// NON-VACUITY CONTROL for the instantiation — claim the element at the
/// OUT-OF-RANGE index `len` is entailed. The invariant only ranges over
/// `[0, len)`, so index `len` is NOT covered. REFUTED (concrete model with
/// `slack(len) < 0`): the universal is used SOUNDLY, with no over-instantiation.
#[trust_vc::requires(len >= 1)]
#[trust_vc::requires(probe == db_slack_at(len))]
#[trust_vc::requires(forall|i: int| (0 <= i && i < len) ==> (db_sat ==> db_slack_at(i) >= 0))]
#[trust_vc::ensures(db_sat ==> db_slack_at(len) >= 0)]
pub fn fq_invariant_implies_last_entailed_wrong(db_sat: bool, len: int, probe: int) {}

// ===========================================================================
// (ii-FQ-LIT) THE FULLY-QUANTIFIED INVARIANT OVER THE LITERAL `Vec` CARRIER —
// residual #2 CLOSED. The (ii-FQ) lemmas route the per-element universal through
// the opaque `db_slack_at: int -> int` Int-domain family. This section discharges
// the SAME universal over the ACTUAL `Vec<i128>` object: the quantifier body is
// the literal `db.index(i)`, which trust-vc lowers to `select db (int2bv_64 i)`
// over the real `db : (Array (BitVec 64) (BitVec 128))` carrier — a genuine array
// read, NOT an opaque function. The element `db.index(i)` is the SLACK
// `eval_i - rhs_i` of the i-th derived constraint at a fixed feasible point; a
// derived constraint is entailed iff `db_sat ==> slack >= 0`.
//
// WHY THIS NOW DISCHARGES — the two landed ay-dpll fixes:
//   * forall-GOAL ground-int strict-bound normalization (crates/ay-dpll/.../
//     quantifier_loop/preprocess.rs): the grown goal
//     `forall i. 0<=i<db.len() ==> ...` skolemizes to a boundary witness `k` with
//     `k < db.len()`; with `db.len() == old_len + 1` the normalization FOLDS that
//     ground length equation into the bound and pins `k = old_len`, so the boundary
//     case reads the just-appended element (the IH covers `k < old_len`). This is
//     residual #2(a) — folding `db.len()==old_len+1` into the bound — RESOLVED.
//   * int2bv/bv2nat forward range-injectivity (crates/ay-dpll/.../combined/mod.rs):
//     pins the BV boundary index from the Int length so the literal
//     `select db (int2bv_64 i)` boundary read resolves to the pushed element.
//
// HONEST RESIDUAL — the next ay-dpll target. The push effect is supplied here as
// the abstract frame `db.len() == old_len + 1` + `db_sat ==> db.index(old_len)
// >= 0` (EXACTLY the per-step facts the (ii-LIT) section discharges over the
// ACTUAL `db.push`), then composed — the same decomposition (ii-FQ) uses. The
// FULLY-INTEGRATED single query (an ACTUAL `db.push(step)` THEN the grown forall
// in one shot) stays Unknown: the nested
// `select (store db (int2bv old_len) step) (int2bv k)` needs int2bv injectivity in
// the NON-boundary direction (`k != old_len ==> int2bv k != int2bv old_len`) AND
// the store element-preservation forall UNDER the goal quantifier, which the
// current E-matching does not compose. The BV-SORTED quantifier form
// (`forall|i: usize|`, body `select db i` guarded by `bv2nat(i) < len`) also stays
// Unknown — E-matching cannot invert the uninterpreted `bv2nat`. The INT-sorted
// form proved here (`forall|i: int|`, body `select db (int2bv i)`) is the shape the
// forall-goal fix reaches; lifting the integrated-push / BV-sorted forms is the
// minimal next ay-dpll step.
// ===========================================================================

/// LITERAL-CARRIER FQ PRESERVATION across one `db.push`, over the ACTUAL
/// `Vec<i128>` (`db.index(i)` == `select db (int2bv_64 i)`). Inductive hypothesis:
/// every element in `[0, old_len)` is entailed; the appended element at the new
/// last slot `old_len` is entailed (`db_sat ==> db.index(old_len) >= 0` — the
/// per-step fact (ii-LIT) discharges over the real `db.push`); the push grew the
/// db by one (`db.len() == old_len + 1`). THEN every element in `[0, db.len())` is
/// entailed — the grown invariant over the REAL Vec. PROVES (forall-goal boundary
/// pin + folded length equation + int2bv boundary injectivity).
#[trust_vc::requires(old_len >= 0)]
#[trust_vc::requires(db.len() == old_len + 1)]
#[trust_vc::requires(db_sat ==> db.index(old_len) >= 0i128)]
#[trust_vc::requires(forall|i: int| (0 <= i && i < old_len) ==> (db_sat ==> db.index(i) >= 0i128))]
#[trust_vc::ensures(forall|i: int| (0 <= i && i < db.len()) ==> (db_sat ==> db.index(i) >= 0i128))]
pub fn fq_lit_invariant_preserved_append(db: Vec<i128>, old_len: int, db_sat: bool) {}

/// NON-VACUITY CONTROL for the LITERAL-CARRIER FQ preservation — DROP the
/// appended-element entailment premise (`db_sat ==> db.index(old_len) >= 0`). A
/// NON-entailed constraint (negative slack) then sits at the boundary slot, so the
/// grown forall over the real Vec is FALSE. MUST NOT verify (the per-step
/// entailment premise is LOAD-BEARING — the literal-carrier discharge is not
/// vacuous). Over the int2bv array carrier ay returns a non-`Verified` verdict
/// (Unknown) rather than admitting the false universal.
#[trust_vc::requires(old_len >= 0)]
#[trust_vc::requires(db.len() == old_len + 1)]
#[trust_vc::requires(forall|i: int| (0 <= i && i < old_len) ==> (db_sat ==> db.index(i) >= 0i128))]
#[trust_vc::ensures(forall|i: int| (0 <= i && i < db.len()) ==> (db_sat ==> db.index(i) >= 0i128))]
pub fn fq_lit_invariant_preserved_append_unsound(db: Vec<i128>, old_len: int, db_sat: bool) {}

/// TERMINAL CONNECTION over the LITERAL carrier — the whole-db invariant
/// INSTANTIATED at the last slot: if every element in `[0, db.len())` is entailed
/// then the LAST derived constraint (index `db.len() - 1`, the one
/// `replay_derivation` returns and `is_contradiction` inspects) is entailed. The
/// last index is named by a symbolic `last_idx == db.len() - 1` so the universal-
/// elimination instantiates cleanly through the `select db (int2bv last_idx)`
/// trigger. PROVES — feeds `terminal_entails_unsat` from the real-Vec invariant.
#[trust_vc::requires(db.len() >= 1)]
#[trust_vc::requires(last_idx == db.len() - 1)]
#[trust_vc::requires(forall|i: int| (0 <= i && i < db.len()) ==> (db_sat ==> db.index(i) >= 0i128))]
#[trust_vc::ensures(db_sat ==> db.index(last_idx) >= 0i128)]
pub fn fq_lit_invariant_implies_last_entailed(db: Vec<i128>, db_sat: bool, last_idx: int) {}

/// NON-VACUITY CONTROL for the literal-carrier instantiation — claim the element
/// at the OUT-OF-RANGE index `db.len()` is entailed. The invariant only ranges
/// over `[0, db.len())`, so index `db.len()` is NOT covered AND the literal read
/// `db.index(db.len())` is itself out of bounds. MUST NOT verify (the index
/// bounds-check obligation cannot be discharged) — the universal is used SOUNDLY,
/// with no over-instantiation past the real Vec's length.
#[trust_vc::requires(db.len() >= 1)]
#[trust_vc::requires(forall|i: int| (0 <= i && i < db.len()) ==> (db_sat ==> db.index(i) >= 0i128))]
#[trust_vc::ensures(db_sat ==> db.index(db.len()) >= 0i128)]
pub fn fq_lit_invariant_implies_last_entailed_wrong(db: Vec<i128>, db_sat: bool) {}

// ===========================================================================
// TERMINAL — `0 >= c (c>=1)` ENTAILS UNSAT. At loop end the invariant gives
// `db_sat ==> final_eval >= final_rhs`; `is_contradiction` accepted because
// `final_eval == 0` (empty LHS) and `final_rhs >= 1`. Then `db_sat` would force
// `0 >= 1`, impossible — so `!db_sat`: NO assignment satisfies the inputs (UNSAT).
// PROVES.
// ===========================================================================
#[trust_vc::ensures(
    ((db_sat ==> (final_eval >= final_rhs)) && final_eval == 0 && final_rhs >= 1) ==> !db_sat
)]
pub fn terminal_entails_unsat(db_sat: bool, final_eval: int, final_rhs: int) -> bool {
    db_sat
}

/// NON-VACUITY CONTROL for TERMINAL — accept `final_rhs >= 0` instead of `>= 1`.
/// `0 >= 0` IS satisfiable, so the empty-LHS constraint is no contradiction and
/// the inputs need not be UNSAT. REFUTED (`final_rhs == 0`, `db_sat` may hold).
#[trust_vc::ensures(
    ((db_sat ==> (final_eval >= final_rhs)) && final_eval == 0 && final_rhs >= 0) ==> !db_sat
)]
pub fn terminal_entails_unsat_wrong(db_sat: bool, final_eval: int, final_rhs: int) -> bool {
    db_sat
}

// ===========================================================================
// (iii) BOUNDED-N END-TO-END — the canonical 3-cycle parity refutation
// (`parity_contradiction_checks_positive`, refutation_check.rs tests) replayed at
// an ARBITRARY point `(x1,x2,x3)` over ℤ. Inputs are the six `>=` halves of
// x1+x2=1, x2+x3=1, x1+x3=1. The replay derives `x1+x2+x3 >= 2` (sum the three
// `>=` halves, ceil-divide by 2) and `x1+x2+x3 <= 1` (sum the three `<=` halves,
// ceil-divide by 2); adding them yields `0 >= 1`. Each derived fact is its own
// lemma, then composed into the UNSAT conclusion.
// ===========================================================================

/// Steps 6,7 (add the three `>=` halves: `2(x1+x2+x3) >= 3`) then 10 (divide by 2:
/// `x1+x2+x3 >= 2`). PROVES `S >= 2` over ℤ (`2S >= 3 ==> S >= 2`).
#[trust_vc::ensures(
    (x1 + x2 >= 1 && x2 + x3 >= 1 && x1 + x3 >= 1) ==> (result >= 2)
)]
pub fn three_cycle_derive_sum_ge(x1: int, x2: int, x3: int) -> int {
    x1 + x2 + x3
}

/// NON-VACUITY CONTROL — overclaim `S >= 3`. REFUTED (x1=1,x2=0,x3=1 gives
/// x1+x2=1, x2+x3=1, x1+x3=2 all `>= 1` but S = 2 < 3).
#[trust_vc::ensures(
    (x1 + x2 >= 1 && x2 + x3 >= 1 && x1 + x3 >= 1) ==> (result >= 3)
)]
pub fn three_cycle_derive_sum_ge_overclaim(x1: int, x2: int, x3: int) -> int {
    x1 + x2 + x3
}

/// Steps 8,9 (add the three `<=` halves: `-2(x1+x2+x3) >= -3`) then 11 (divide by
/// 2: `-(x1+x2+x3) >= -1`, i.e. `S <= 1`). PROVES `S <= 1` over ℤ.
#[trust_vc::ensures(
    (-x1 - x2 >= -1 && -x2 - x3 >= -1 && -x1 - x3 >= -1) ==> (result <= 1)
)]
pub fn three_cycle_derive_sum_le(x1: int, x2: int, x3: int) -> int {
    x1 + x2 + x3
}

/// Step 12 (add the two divided facts): `S >= 2` and `S <= 1` is `0 >= 1`, which
/// no `S` satisfies. PROVES `!(S >= 2 && S <= 1)`.
#[trust_vc::ensures(!(s >= 2 && s <= 1))]
pub fn three_cycle_contradiction(s: int) -> bool {
    s >= 2 && s <= 1
}

/// END-TO-END: the six input halves are jointly UNSATISFIABLE — no assignment
/// `(x1,x2,x3)` satisfies them — which is the refutation's conclusion (the replay
/// reduced them to `0 >= 1`). `result` is "x satisfies all six inputs"; PROVES
/// `result == false` (ay does the ℤ-infeasibility the cutting-planes steps mirror).
#[trust_vc::ensures(result == false)]
pub fn three_cycle_inputs_unsat(x1: int, x2: int, x3: int) -> bool {
    x1 + x2 >= 1
        && -x1 - x2 >= -1
        && x2 + x3 >= 1
        && -x2 - x3 >= -1
        && x1 + x3 >= 1
        && -x1 - x3 >= -1
}

/// NON-VACUITY CONTROL — DROP one half (`-x1 - x3 >= -1`), leaving a SATISFIABLE
/// five-constraint set. `result == false` is then FALSE, so it MUST be REFUTED
/// with a concrete satisfying point (pinning that the UNSAT above is genuine, not
/// a vacuous discharge).
#[trust_vc::ensures(result == false)]
pub fn three_cycle_inputs_satisfiable_drop_one(x1: int, x2: int, x3: int) -> bool {
    x1 + x2 >= 1
        && -x1 - x2 >= -1
        && x2 + x3 >= 1
        && -x2 - x3 >= -1
        && x1 + x3 >= 1
}
