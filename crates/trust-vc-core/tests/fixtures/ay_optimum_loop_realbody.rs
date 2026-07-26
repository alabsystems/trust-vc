// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// =====================================================================
// NON-VACUOUS native-deductive lift of the in-production cutting-planes
// OPTIMUM SELF-CHECK from PER-STEP soundness to WHOLE-LOOP soundness — the
// SCORE-CRITICAL DUAL of the refutation whole-loop lift
// (refutation_loop_realbody.rs). A wrong OPTIMUM is a wrong answer on the
// verdict that wins medals, so the floor-derivation REPLAY loop must be sound
// as a WHOLE, not merely per step.
//
// `ObjectiveBound::check_floor` (crates/ay-pb/src/proof/optimum_check.rs:90-110)
// establishes an objective FLOOR `F` by REPLAYING a cutting-planes derivation
// (`replay_derivation`, refutation_check.rs:315-347 — the SAME accumulate-and-
// continue loop the refutation checker runs) and accepting `F` IFF the derived
// constraint is IDENTICAL to the objective form at degree `F`
// (`derived == target`). `certify_optimum` (optimum_check.rs:120-127) then
// promotes to OPTIMUM IFF a VIG-verified incumbent attains `F` (`LB == UB`).
//
// The PER-STEP cut rules (`add`/`scale`/`divide_ceil`/`saturate`) are already
// proven entailment-preserving (refutation_step_realbody.rs /
// saturate_step_realbody.rs); the per-point terminal transport + tightness gate
// are proven in optimum_floor_realbody.rs. This fixture lifts those to the LOOP:
//   it proves the LOOP INVARIANT "the accumulated/derived constraint stays a
//   SOUND consequence of the original DB (entailed at every feasible point)" is
//   PRESERVED by each iteration (per rule, rule-agnostically, and across an
//   arbitrary-length engine-verified `while` loop), and that TERMINATING with a
//   derived bound `sum obj_coeff[v] x_v >= F` makes `F` a VALID LOWER BOUND on
//   the objective over the whole feasible region — so a feasible incumbent with
//   value `== F` is PROVABLY optimal (`LB == UB`). Discharged by trust-vc on the
//   pure-Rust `ay` SMT solver, kernel-rechecked.
// =====================================================================
//
// THE ENTAILMENT MODEL (how a "loop invariant" is stated to trust-vc)
// ------------------------------------------------------------------
// Fix an arbitrary feasible assignment `x` (one satisfying EVERY original input
// constraint). A normalized `>=` constraint with LHS value `eval` at `x` and
// degree `rhs` HOLDS at `x` iff `eval >= rhs`. A derived constraint is ENTAILED
// by the inputs iff it holds at every feasible `x`. The floor-derivation loop's
// invariant is: the running accumulated constraint is entailed, i.e. at the fixed
// feasible `x` its LHS value `acc_eval` satisfies `acc_eval >= floor` (its current
// degree). On entry the accumulator is a (scaled) input row, entailed by
// definition. Each iteration ADDs one entailed step; PRESERVATION is: the new
// accumulator is again entailed. The proven per-step cut rules supply exactly the
// arithmetic that closes this.
//
// WHY THIS IS THE DUAL OF THE REFUTATION LOOP
// -------------------------------------------
// Same accumulate loop (`replay_derivation`); the DIFFERENCE is the TERMINAL:
//   * refutation: terminal `0 >= c (c>=1)` (`is_contradiction`) ENTAILS UNSAT;
//   * OPTIMUM:    terminal `derived == target` (the objective form at degree `F`)
//                 makes `F` a valid lower bound on the objective; with a feasible
//                 incumbent at `F`, `LB == UB` ⟹ OPTIMUM.
// The loop-PRESERVATION half is therefore shared with refutation_loop_realbody.rs
// (re-stated here in the floor-derivation framing so this fixture is self-
// contained and the CONFORMANCE pins the shared loop body); the NEW, score-
// critical half is the FLOOR/OPTIMALITY terminal connected to the loop's final
// accumulated state.
//
// SCOPE — WHAT IS AND IS NOT THE UNBOUNDED BTreeMap LOOP (honest)
// --------------------------------------------------------------
// trust-vc's loop reasoning is a frame-condition inductive step; it does not
// encode the unbounded `Vec<LinConstraint>`-of-`BTreeMap` heap mutation of the
// real `db.push(..)` loop. So the lift is delivered as:
//   (i)   the INVARIANT-PRESERVATION step (the crux), proven per rule and once
//         rule-AGNOSTICALLY (entailment is closed under any sound step),
//         composing the per-step arithmetic already proven elsewhere; and
//   (ii)  an ACTUAL trust-vc `while`-loop, verified by the engine's inductive
//         machinery, that maintains the entailment invariant
//         (`acc_eval >= floor`) — and, in `accumulate_floor_monotone`, ALSO that
//         the running floor only STRENGTHENS (`floor >= start_floor`) — across an
//         ARBITRARY (symbolic `n`) number of homogeneous ADD iterations; the
//         iteration count is unbounded, what is bounded/abstracted is the
//         heterogeneous match-dispatch and the coefficient `BTreeMap` (collapsed
//         to the LHS value `acc_eval` at the fixed point); and
//   (iii) a concrete BOUNDED-N END-TO-END replay of the canonical Lean OPTIMUM
//         example (`aggregation_certifies_lean_division_example`, optimum_check.rs
//         :862) at a fixed point: `min x+y` s.t. `2x+2y>=3` ⟹ divide-by-2 ceil
//         cut derives the floor `x+y >= 2 = F`; incumbent `x=y=1` has value
//         `2 == F` ⟹ OPTIMUM.
// The `while`-loop in (ii) rides on the toolchain capability built for the
// refutation lift: trust-vc carries function PRECONDITIONS over UNMODIFIED
// (frame-preserved) variables into the inductive step (sound: such a predicate
// has one truth value for the whole call), so the entailment of the repeatedly-
// added step (`step_eval >= step_rhs`, over loop-INVARIANT params) survives the
// frame-condition havoc; see
// `crates/trust-vc-core/.../invariants/frame_condition.rs` and the regression
// `loop_invariant_unmodified_precondition_soundness.rs`. `accumulate_floor_
// monotone` additionally exercises a TWO-CLAUSE conjunctive invariant carried
// over an unmodified `start_floor` — the dual loop is strictly richer than the
// refutation one.
//
// WHY THE LEMMAS ARE OVER `int` (Verus ℤ), NOT i128 — identical to the per-step
// fixtures: the checker uses i128 `checked_*` + `?`, so any overflow REJECTS the
// step (`RefError::BadStep`); every ACCEPTED step did exact ℤ arithmetic. The
// `lemma_mul_le_mono_right` AXIOM closes ay's NIA incompleteness on the scale /
// lift product `k*x`, with its `#[requires]` CHECKED at every call site.
//
// HOW THIS IS VERIFIED: `trust_vc_core::verify_function_from_file(<this file>,
// <fn>)`. `Verified` == ay returned UNSAT and the trust-vc-kernel accepted the
// proof; `Counterexample` == ay returned a concrete falsifying model.

// =====================================================================
// VERBATIM real checker source (copied from crates/ay-pb/src/proof/
// optimum_check.rs and refutation_check.rs; the conformance test byte-pins these
// blocks to the live source). This is the floor-derivation REPLAY loop and its
// OPTIMUM terminal whose whole-loop soundness the proofs below lift.
// =====================================================================
//
// --- ObjectiveBound::check_floor (optimum_check.rs:90-110) — runs the replay
//     loop, accepts `derived == target` (the objective form at degree F) ---
// CONFORMANCE: src/proof/optimum_check.rs:90-110
//   pub fn check_floor(&self) -> Result<i128, OptError> {
//       // The objective normalized as the target `>= claimed_floor` constraint.
//       let target = pb_ge(&PbConstraint {
//           terms: self.objective_terms.clone(),
//           rel: PbRel::Ge,
//           rhs: self.claimed_floor,
//       })
//       .ok_or(OptError::UnmodeledObjective)?;
//
//       let derived = replay_derivation(&self.inputs, &self.steps).map_err(OptError::Replay)?;
//
//       // The derived constraint must be IDENTICAL to the objective floor: same
//       // per-variable coefficients AND the same RHS. Equality (not `>=`) is the
//       // dual of the refutation checker's `0 >= c` terminal: a builder that
//       // claims a floor the derivation does not actually reach is rejected.
//       if derived == target {
//           Ok(self.claimed_floor)
//       } else {
//           Err(OptError::NotObjectiveFloor)
//       }
//   }
//
// --- ObjectiveBound::certify_optimum (optimum_check.rs:120-127) — LB == UB ---
// CONFORMANCE: src/proof/optimum_check.rs:120-127
//   pub fn certify_optimum(&self, incumbent_value: i128) -> Result<i128, OptError> {
//       let floor = self.check_floor()?;
//       if incumbent_value == floor {
//           Ok(floor)
//       } else {
//           Err(OptError::NotTight)
//       }
//   }
//
// --- replay_derivation (refutation_check.rs:315-347) — the ACCUMULATE loop the
//     floor derivation drives (shared with the refutation checker) ---
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
// Kernel-trivial ring axiom (same as refutation_step_realbody.rs /
// optimum_floor_realbody.rs): right-multiplication monotonicity, the NIA fact ay
// cannot derive itself. Trusted body (`external_body`); its `#[requires]` is
// CHECKED at the call site.
// ---------------------------------------------------------------------------
#[trust_vc::external_body]
#[trust_vc::requires(lo <= hi && f >= 0)]
#[trust_vc::ensures(lo * f <= hi * f)]
pub fn lemma_mul_le_mono_right(lo: int, hi: int, f: int) {}

// ===========================================================================
// (i) INVARIANT PRESERVATION — per rule. The floor derivation grows the
// accumulated constraint via the SAME cut rules as the refutation checker. At a
// fixed feasible point, the operands a step reads are `db` entries whose
// ENTAILMENT `db_sat ==> eval >= rhs` is the inductive HYPOTHESIS; each lemma
// proves the PUSHED constraint is again entailed, composing the proven per-step
// arithmetic (add/scale/divide). This is the body of the floor-derivation loop's
// inductive step — the soundness CRUX of the whole-loop OPTIMUM lift.
// ===========================================================================

/// PRESERVATION for ADD (the floor derivation's row-aggregation AND lift steps:
/// `impliedGe_add`, refutation_check.rs:127-134). Pushed constraint has LHS value
/// `eval_a + eval_b` and degree `rhs_a + rhs_b`. If both operands are entailed, so
/// is the sum. PROVES.
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

/// PRESERVATION for SCALE (`k >= 1`; the floor derivation's surrogate-multiplier
/// and per-row multiplier steps: `impliedGe_scale`, refutation_check.rs:137-146).
/// Pushed constraint has LHS `k * eval_a` and degree `k * rhs_a`. If the operand is
/// entailed then so is the scaled fact, via the monotonicity axiom. PROVES.
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
/// refutation_check.rs:150-159) — THE cut that produces ceil floors (e.g.
/// `2x+2y>=3` ⟹ `x+y>=2`). The coefficient `BTreeMap` merge is collapsed to the
/// divided LHS value `div_eval` and degree `div_rhs` at the fixed point, with the
/// proven per-step facts supplied as preconditions:
///   * `2 * div_eval >= eval_a` — the per-coefficient ceiling DOMINATION
///     `2*ceil(c/2) >= c` (`ceil_div_by2_rounds_up`, proven in
///     refutation_step_realbody.rs) summed over `x >= 0`; and
///   * `2 * div_rhs >= rhs_a && 2 * div_rhs <= rhs_a + 1` — `div_rhs == ceil(rhs_a/2)`.
/// Then operand entailment lifts to the divided constraint: `2*div_eval >= eval_a
/// >= rhs_a` and `2*div_rhs <= rhs_a + 1` give `div_eval >= div_rhs` over ℤ. PROVES.
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
// the per-step cut rules LIFT to the floor-derivation loop: entailment by the
// inputs is CLOSED under any SOUND step. Given the two operands are entailed
// (`db_sat ==> *_holds`) and the rule is sound at the point (`op_a_holds &&
// op_b_holds ==> derived_holds` — exactly what add/scale/divide/saturate each
// prove), the pushed constraint is entailed. PROVES (propositional); holds for
// EVERY rule, hence preserves the loop invariant whatever step the loop applies.
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
// (ii) THE WHOLE FLOOR-DERIVATION LOOP — engine-verified inductive proof. An
// ACTUAL trust-vc `while` loop that mirrors the floor derivation's accumulate-
// and-continue shape: `acc_eval` is the running derived constraint's LHS value at
// the fixed feasible point, `floor` its running degree (the objective floor being
// built up). Each iteration ADDs one entailed cut contribution (`step_eval >=
// step_rhs`, the loop-INVARIANT consequence of `db_sat`). The loop INVARIANT
// `acc_eval >= floor` ("the accumulated derived constraint still holds at x, so it
// stays entailed by the inputs") is maintained across an ARBITRARY (symbolic `n`)
// number of iterations. Verified by trust-vc's frame-condition inductive step.
// ===========================================================================
#[trust_vc::requires(acc_eval >= floor)]
#[trust_vc::requires(step_eval >= step_rhs)]
#[trust_vc::ensures(acc_eval >= floor)]
pub fn accumulate_floor_entailed(
    mut acc_eval: int,
    mut floor: int,
    step_eval: int,
    step_rhs: int,
    mut k: int,
    n: int,
) {
    while k < n {
        trust_vc::invariant!(acc_eval >= floor);
        acc_eval = acc_eval + step_eval;
        floor = floor + step_rhs;
        k = k + 1;
    }
}

/// WRONG-CONTROL — OVER-STRONG FLOOR. DROP the step-entailment precondition
/// (`step_eval >= step_rhs`): a cut step then contributes MORE to the floor than
/// its LHS supports (an over-strong floor that exceeds what the derivation
/// actually yields). The accumulator drops below its degree, so the entailment
/// invariant is NOT preserved. REFUTED at the inductive step — the over-strong
/// floor is exactly the unsound OPTIMUM the whole-loop soundness rules out.
#[trust_vc::requires(acc_eval >= floor)]
#[trust_vc::ensures(acc_eval >= floor)]
pub fn accumulate_floor_overstrong(
    mut acc_eval: int,
    mut floor: int,
    step_eval: int,
    step_rhs: int,
    mut k: int,
    n: int,
) {
    while k < n {
        trust_vc::invariant!(acc_eval >= floor);
        acc_eval = acc_eval + step_eval;
        floor = floor + step_rhs;
        k = k + 1;
    }
}

/// THE DUAL LOOP, STRICTLY RICHER THAN THE REFUTATION ONE — a TWO-CLAUSE
/// conjunctive invariant. Beyond entailment (`acc_eval >= floor`), it carries that
/// the running floor only STRENGTHENS (`floor >= start_floor`): each entailed cut
/// with non-negative degree contribution (`step_rhs >= 0`) raises the floor, never
/// lowering it. Exercises the frame-condition inductive step carrying TWO invariant
/// clauses plus the precondition over the UNMODIFIED `start_floor`. PROVES.
#[trust_vc::requires(acc_eval >= floor)]
#[trust_vc::requires(floor >= start_floor)]
#[trust_vc::requires(step_eval >= step_rhs)]
#[trust_vc::requires(step_rhs >= 0)]
#[trust_vc::ensures(acc_eval >= floor && floor >= start_floor)]
pub fn accumulate_floor_monotone(
    mut acc_eval: int,
    mut floor: int,
    step_eval: int,
    step_rhs: int,
    start_floor: int,
    mut k: int,
    n: int,
) {
    while k < n {
        trust_vc::invariant!(acc_eval >= floor);
        trust_vc::invariant!(floor >= start_floor);
        acc_eval = acc_eval + step_eval;
        floor = floor + step_rhs;
        k = k + 1;
    }
}

/// NON-VACUITY CONTROL for the monotone loop — DROP the non-negative-contribution
/// precondition (`step_rhs >= 0`). A step with a NEGATIVE degree contribution
/// lowers the running floor below `start_floor`, breaking the monotonicity clause.
/// REFUTED at the inductive step (the floor strengthening is genuine, not blanket).
#[trust_vc::requires(acc_eval >= floor)]
#[trust_vc::requires(floor >= start_floor)]
#[trust_vc::requires(step_eval >= step_rhs)]
#[trust_vc::ensures(acc_eval >= floor && floor >= start_floor)]
pub fn accumulate_floor_monotone_unsound(
    mut acc_eval: int,
    mut floor: int,
    step_eval: int,
    step_rhs: int,
    start_floor: int,
    mut k: int,
    n: int,
) {
    while k < n {
        trust_vc::invariant!(acc_eval >= floor);
        trust_vc::invariant!(floor >= start_floor);
        acc_eval = acc_eval + step_eval;
        floor = floor + step_rhs;
        k = k + 1;
    }
}

// ===========================================================================
// (ii-LIT) THE LITERAL `Vec`-PUSH FLOOR-DERIVATION LOOP — engine-verified over the
// ACTUAL heap mutation, the DUAL of refutation_loop_realbody.rs's (ii-LIT). Unlike
// (ii)'s SCALAR `acc_eval` abstraction, this drives trust-vc's frame-condition
// inductive step over the REAL growing `Vec` `db` mutated by `db.push(..)` — the
// shared accumulate loop of `replay_derivation` (refutation_check.rs:322-343) that
// the floor-derivation REPLAY runs. `db` is the running floor-derivation DB; each
// element is the SLACK `eval - rhs` of a derived constraint at a fixed feasible
// point (the per-constraint coefficient `BTreeMap` collapsed to that slack, the
// SAME abstraction (ii) makes, now per-ELEMENT of the literal Vec). Across an
// ARBITRARY (symbolic `n`) number of `db.push` iterations the engine carries:
//   * EXACT GROWTH `db.len() == start + count` — the floor DB grows by exactly one
//     derived cut per replay step (one `db.push(derived)` per step); and
//   * APPENDED-ENTAILED `db.index(db.len()-1) == step && step >= 0` — the pushed
//     cut contribution IS entailed (its slack is non-negative), so the running
//     floor only strengthens.
//
// This was previously impossible (a `db.push(..)` loop body left `db` FULLY
// havoc'd). trust-vc was extended to CAPTURE the collection `push` single-iteration
// transition `db == db_pre.push(value)` (vc_extraction/body_extract.rs), threading
// the push facts (len+1, appended element, element preservation) into the
// frame-condition step. FULLY-QUANTIFIED invariant (was the disclosed residual,
// same as the refutation dual): the per-element `forall i. i < db.len() ==>
// db.index(i) is entailed` is now DISCHARGED — over the opaque Int-domain family
// in (ii-FQ), AND over the ACTUAL `Vec<i128>` object (`db.index(i)` ==
// `select db (int2bv_64 i)`) in (ii-FQ-LIT), which CLOSES the disclosed residual
// #2. The ay-dpll forall-GOAL boundary limitation that blocked it is FIXED (ground
// integer strict-bound normalization pins the skolemized boundary `k = old_len`;
// crates/ay-dpll/.../forall_goal_int_boundary_discharge.rs), and the literal
// `select db (int2bv old_len)` boundary read is pinned by the int2bv/bv2nat forward
// range-injectivity bridge. The per-STEP appended-entailment + exact growth here
// remain the literal-`Vec` content trust-vc discharges over the ACTUAL `db.push`;
// (ii-FQ)/(ii-FQ-LIT) lift them to the whole-db universal.
// ===========================================================================

// CONFORMANCE: src/proof/refutation_check.rs:322-323
//     let mut db: Vec<LinConstraint> = inputs.to_vec();
//     for (idx, step) in steps.iter().enumerate() {
// CONFORMANCE: src/proof/refutation_check.rs:343-343
//         db.push(derived);

/// EXACT GROWTH of the literal floor-derivation `db` Vec across the unbounded push
/// loop: `db.len() == start + count` maintained by the engine's inductive step over
/// the REAL `db.push(..)` (via the captured push transition `db.len() ==
/// db_pre.len() + 1`). PROVES.
#[trust_vc::requires(db.len() == start)]
#[trust_vc::requires(count == 0)]
pub fn floor_push_db_grows_exact(mut db: Vec<i128>, start: int, mut count: int, n: int) {
    while count < n {
        trust_vc::invariant!(db.len() == start + count);
        db.push(0i128);
        count = count + 1;
    }
}

/// NON-VACUITY CONTROL for exact growth — overclaim the length by one. The push
/// grows `db` by exactly one, so the claim is false on entry. REFUTED.
#[trust_vc::requires(db.len() == start)]
#[trust_vc::requires(count == 0)]
pub fn floor_push_db_grows_exact_overclaim(
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

/// APPENDED-ENTAILED: each floor-derivation step pushes an ENTAILED cut — its slack
/// `step` (`>= 0`) lands at the new last slot. PROVES (composes with exact growth).
#[trust_vc::requires(step >= 0i128)]
#[trust_vc::requires(db.len() == start)]
#[trust_vc::requires(count == 0)]
pub fn floor_push_appends_entailed(
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
/// precondition (`step >= 0`). A `db.push(step)` of a NON-entailed cut (negative
/// slack) breaks the appended-element entailment. MUST NOT verify.
#[trust_vc::requires(db.len() == start)]
#[trust_vc::requires(count == 0)]
pub fn floor_push_appends_entailed_unsound(
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
// (ii-FQ) THE FULLY-QUANTIFIED PER-ELEMENT INVARIANT — now DISCHARGED (the
// score-critical dual of refutation_loop_realbody.rs's (ii-FQ)). The floor-
// derivation whole-loop invariant in its STRONGEST form: EVERY cut currently in
// the floor DB is entailed by the inputs —
//     forall i. (0 <= i < db.len()) ==> (db_sat ==> slack(i) >= 0)
// where `slack(i) = eval_i - rhs_i` is the i-th derived cut's contribution at a
// fixed feasible point (the per-cut coefficient `BTreeMap` collapsed to that
// slack — the SAME abstraction (ii)/(ii-LIT) make, now PER-ELEMENT under a
// universal). A cut is entailed iff it holds at every feasible `x`, i.e.
// `db_sat ==> slack >= 0`; entailed cuts only STRENGTHEN the running floor.
//
// This whole-db forall was the disclosed residual: maintaining it across one
// `db.push` extends the index range by one and the NEW boundary index `db.len()`
// reads the just-appended cut — which ay-dpll's forall-GOAL instantiation could
// not pin across the inductive step. That limitation is now FIXED (ground integer
// strict-bound normalization pins the skolemized boundary `k = old_len`; see
// crates/ay-dpll/tests/group_quantifiers/forall_goal_int_boundary_discharge.rs),
// so the per-element invariant maintained across the append DISCHARGES
// (`fq_floor_invariant_preserved_append`, PROVES).
//
// CARRIER NOTE — why the floor DB is modeled as an INDEXED FAMILY here. trust-vc
// lowers a literal `Vec<i128>` to a BV-INDEXED SMT array; `db.push` stores at
// `int2bv(old_len)`, relating pre/post `db` through an element-preservation forall.
// The (ii-FQ) lemmas in THIS section route the per-element universal through the
// opaque Int-domain family `floor_slack_at: int -> int` — the SAME slack
// abstraction indexed by an Int position, the carrier the ay-dpll forall-goal fix
// was first validated on. They retain the CLEAN concrete-counterexample controls
// (`floor_slack_at` is uninterpreted, so a dropped premise yields an explicit
// falsifying model), pinning the LOGIC of the floor lift as non-vacuous.
//
// The SAME universal is now ALSO discharged over the ACTUAL `Vec<i128>` object —
// the quantifier body is the literal `db.index(i)` (lowered to
// `select db (int2bv_64 i)` over the real `db : (Array (BitVec 64) (BitVec 128))`,
// NOT an opaque function) — in the (ii-FQ-LIT) section below. That CLOSES the
// disclosed residual #2 (the per-element invariant over the literal carrier was
// previously Unknown), including residual #2(a) (folding the ground length
// equation `db.len() == old_len + 1` into the boundary bound). Composing (ii-FQ-
// LIT) with the literal-`Vec` (ii-LIT) proofs (exact growth + appended-entailment
// over the ACTUAL `db.push`) lifts the WHOLE floor-derivation loop with the
// fully-quantified invariant ABOUT THE REAL Vec.
// ===========================================================================

/// The i-th derived cut's SLACK (`eval_i - rhs_i`) at a fixed feasible point —
/// OPAQUE (uninterpreted), the same abstraction the per-step rules reason about.
/// The FQ invariant holds for an ARBITRARY such family, hence for the real floor
/// DB; opaqueness is why the controls below are REFUTED, not vacuously accepted.
#[trust_vc::spec]
#[trust_vc::opaque]
fn floor_slack_at(i: int) -> int {
    0
}

/// PRESERVATION of the FULLY-QUANTIFIED floor invariant across ONE `db.push`.
/// Inductive hypothesis: every cut in `[0, old_len)` is entailed (`db_sat ==>
/// slack >= 0`); the appended cut at index `old_len` is entailed; THEN every cut
/// in `[0, old_len + 1)` is entailed — the invariant on the grown floor DB. The
/// boundary index `old_len` (the just-pushed cut) is pinned by the ay-dpll
/// forall-goal fix. PROVES. (`probe` only anchors `floor_slack_at`'s return type.)
#[trust_vc::requires(old_len >= 0)]
#[trust_vc::requires(probe == floor_slack_at(old_len))]
#[trust_vc::requires(db_sat ==> floor_slack_at(old_len) >= 0)]
#[trust_vc::requires(forall|i: int| (0 <= i && i < old_len) ==> (db_sat ==> floor_slack_at(i) >= 0))]
#[trust_vc::ensures(forall|i: int| (0 <= i && i < old_len + 1) ==> (db_sat ==> floor_slack_at(i) >= 0))]
pub fn fq_floor_invariant_preserved_append(db_sat: bool, old_len: int, probe: int) {}

/// NON-VACUITY CONTROL for FQ floor preservation — DROP the appended-cut
/// entailment premise. A NON-entailed cut (negative slack, which would FALSELY
/// strengthen the floor) then enters `db`, so the grown forall is FALSE. REFUTED
/// with a concrete counterexample: the per-step entailment premise is
/// LOAD-BEARING — the FQ discharge is NOT vacuous.
#[trust_vc::requires(old_len >= 0)]
#[trust_vc::requires(probe == floor_slack_at(old_len))]
#[trust_vc::requires(forall|i: int| (0 <= i && i < old_len) ==> (db_sat ==> floor_slack_at(i) >= 0))]
#[trust_vc::ensures(forall|i: int| (0 <= i && i < old_len + 1) ==> (db_sat ==> floor_slack_at(i) >= 0))]
pub fn fq_floor_invariant_preserved_append_unsound(db_sat: bool, old_len: int, probe: int) {}

/// TERMINAL CONNECTION — the FULLY-QUANTIFIED floor invariant INSTANTIATED at the
/// last slot: if every cut in `[0, len)` is entailed then the LAST derived cut
/// (index `len - 1`, the accumulated floor `replay_derivation` returns and
/// `check_floor` inspects against `target`) is entailed. This universal-
/// elimination is what feeds the OPTIMUM terminal from the whole-db invariant.
/// PROVES.
#[trust_vc::requires(len >= 1)]
#[trust_vc::requires(probe == floor_slack_at(len - 1))]
#[trust_vc::requires(forall|i: int| (0 <= i && i < len) ==> (db_sat ==> floor_slack_at(i) >= 0))]
#[trust_vc::ensures(db_sat ==> floor_slack_at(len - 1) >= 0)]
pub fn fq_floor_invariant_implies_last_entailed(db_sat: bool, len: int, probe: int) {}

/// NON-VACUITY CONTROL for the instantiation — claim the cut at the OUT-OF-RANGE
/// index `len` is entailed. The invariant only ranges over `[0, len)`, so index
/// `len` is NOT covered. REFUTED (concrete model with `slack(len) < 0`): the
/// universal is used SOUNDLY, with no over-instantiation.
#[trust_vc::requires(len >= 1)]
#[trust_vc::requires(probe == floor_slack_at(len))]
#[trust_vc::requires(forall|i: int| (0 <= i && i < len) ==> (db_sat ==> floor_slack_at(i) >= 0))]
#[trust_vc::ensures(db_sat ==> floor_slack_at(len) >= 0)]
pub fn fq_floor_invariant_implies_last_entailed_wrong(db_sat: bool, len: int, probe: int) {}

// ===========================================================================
// (ii-FQ-LIT) THE FULLY-QUANTIFIED FLOOR INVARIANT OVER THE LITERAL `Vec`
// CARRIER — residual #2 CLOSED (the score-critical dual of refutation_loop_
// realbody.rs's (ii-FQ-LIT)). The (ii-FQ) lemmas route the per-element universal
// through the opaque `floor_slack_at: int -> int` Int-domain family. This section
// discharges the SAME universal over the ACTUAL `Vec<i128>` floor DB: the
// quantifier body is the literal `db.index(i)`, lowered to `select db (int2bv_64
// i)` over the real `db : (Array (BitVec 64) (BitVec 128))` carrier — a genuine
// array read, NOT an opaque function. The element `db.index(i)` is the SLACK
// `eval_i - rhs_i` of the i-th derived cut at a fixed feasible point; a cut is
// entailed iff `db_sat ==> slack >= 0`, and entailed cuts only STRENGTHEN the
// running floor.
//
// WHY THIS NOW DISCHARGES — the two landed ay-dpll fixes:
//   * forall-GOAL ground-int strict-bound normalization (crates/ay-dpll/.../
//     quantifier_loop/preprocess.rs): the grown goal
//     `forall i. 0<=i<db.len() ==> ...` skolemizes to a boundary witness `k` with
//     `k < db.len()`; with `db.len() == old_len + 1` the normalization FOLDS that
//     ground length equation into the bound and pins `k = old_len`, so the boundary
//     case reads the just-appended cut (the IH covers `k < old_len`). This is
//     residual #2(a) — folding `db.len()==old_len+1` into the bound — RESOLVED.
//   * int2bv/bv2nat forward range-injectivity (crates/ay-dpll/.../combined/mod.rs):
//     pins the BV boundary index from the Int length so the literal
//     `select db (int2bv_64 i)` boundary read resolves to the pushed cut.
//
// HONEST RESIDUAL — the next ay-dpll target. The push effect is supplied here as
// the abstract frame `db.len() == old_len + 1` + `db_sat ==> db.index(old_len)
// >= 0` (EXACTLY the per-step facts the (ii-LIT) section discharges over the
// ACTUAL `db.push`), then composed. The FULLY-INTEGRATED single query (an ACTUAL
// `db.push(step)` THEN the grown forall in one shot) stays Unknown: the nested
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

/// LITERAL-CARRIER FQ FLOOR PRESERVATION across one `db.push`, over the ACTUAL
/// `Vec<i128>` (`db.index(i)` == `select db (int2bv_64 i)`). Inductive hypothesis:
/// every cut in `[0, old_len)` is entailed; the appended cut at the new last slot
/// `old_len` is entailed (`db_sat ==> db.index(old_len) >= 0` — the per-step fact
/// (ii-LIT) discharges over the real `db.push`); the push grew the floor DB by one
/// (`db.len() == old_len + 1`). THEN every cut in `[0, db.len())` is entailed — the
/// grown invariant over the REAL Vec. PROVES (forall-goal boundary pin + folded
/// length equation + int2bv boundary injectivity).
#[trust_vc::requires(old_len >= 0)]
#[trust_vc::requires(db.len() == old_len + 1)]
#[trust_vc::requires(db_sat ==> db.index(old_len) >= 0i128)]
#[trust_vc::requires(forall|i: int| (0 <= i && i < old_len) ==> (db_sat ==> db.index(i) >= 0i128))]
#[trust_vc::ensures(forall|i: int| (0 <= i && i < db.len()) ==> (db_sat ==> db.index(i) >= 0i128))]
pub fn fq_lit_floor_invariant_preserved_append(db: Vec<i128>, old_len: int, db_sat: bool) {}

/// NON-VACUITY CONTROL for the LITERAL-CARRIER FQ floor preservation — DROP the
/// appended-cut entailment premise. A NON-entailed cut (negative slack, which would
/// FALSELY strengthen the floor) then sits at the boundary slot, so the grown
/// forall over the real Vec is FALSE. MUST NOT verify (the per-step entailment
/// premise is LOAD-BEARING). Over the int2bv array carrier ay returns a
/// non-`Verified` verdict (Unknown) rather than admitting the false universal.
#[trust_vc::requires(old_len >= 0)]
#[trust_vc::requires(db.len() == old_len + 1)]
#[trust_vc::requires(forall|i: int| (0 <= i && i < old_len) ==> (db_sat ==> db.index(i) >= 0i128))]
#[trust_vc::ensures(forall|i: int| (0 <= i && i < db.len()) ==> (db_sat ==> db.index(i) >= 0i128))]
pub fn fq_lit_floor_invariant_preserved_append_unsound(db: Vec<i128>, old_len: int, db_sat: bool) {}

/// TERMINAL CONNECTION over the LITERAL carrier — the whole-db floor invariant
/// INSTANTIATED at the last slot: if every cut in `[0, db.len())` is entailed then
/// the LAST derived cut (index `db.len() - 1`, the accumulated floor
/// `replay_derivation` returns and `check_floor` inspects against `target`) is
/// entailed. The last index is named by a symbolic `last_idx == db.len() - 1` so
/// the universal-elimination instantiates cleanly through the
/// `select db (int2bv last_idx)` trigger. PROVES — feeds the OPTIMUM terminal from
/// the real-Vec invariant.
#[trust_vc::requires(db.len() >= 1)]
#[trust_vc::requires(last_idx == db.len() - 1)]
#[trust_vc::requires(forall|i: int| (0 <= i && i < db.len()) ==> (db_sat ==> db.index(i) >= 0i128))]
#[trust_vc::ensures(db_sat ==> db.index(last_idx) >= 0i128)]
pub fn fq_lit_floor_invariant_implies_last_entailed(db: Vec<i128>, db_sat: bool, last_idx: int) {}

/// NON-VACUITY CONTROL for the literal-carrier instantiation — claim the cut at
/// the OUT-OF-RANGE index `db.len()` is entailed. The invariant only ranges over
/// `[0, db.len())`, so index `db.len()` is NOT covered AND the literal read
/// `db.index(db.len())` is itself out of bounds. MUST NOT verify (the index
/// bounds-check obligation cannot be discharged) — the universal is used SOUNDLY,
/// with no over-instantiation past the real Vec's length.
#[trust_vc::requires(db.len() >= 1)]
#[trust_vc::requires(forall|i: int| (0 <= i && i < db.len()) ==> (db_sat ==> db.index(i) >= 0i128))]
#[trust_vc::ensures(db_sat ==> db.index(db.len()) >= 0i128)]
pub fn fq_lit_floor_invariant_implies_last_entailed_wrong(db: Vec<i128>, db_sat: bool) {}

// ===========================================================================
// TERMINAL — the whole-loop OPTIMUM conclusion (the score-critical dual of the
// refutation `0 >= 1` ⟹ UNSAT terminal). At loop end the invariant gives the
// accumulated derived constraint is entailed: at the fixed feasible `x`,
// `acc_eval >= floor`. `check_floor` accepted `derived == target`, i.e. the
// accumulator was lifted to the EXACT objective form (so `acc_eval == obj_eval` at
// `x`) at degree `floor == big_f`. Hence `obj_eval >= big_f`: `big_f` is a VALID
// LOWER BOUND on the objective over EVERY feasible `x`. `certify_optimum` then
// requires a VIG-verified incumbent attaining `big_f` (`incumbent == big_f`); since
// `incumbent == big_f <= obj_eval` for every feasible `x`, NO feasible point beats
// the incumbent — it is OPTIMAL (`LB == UB`). PROVES.
// ===========================================================================
#[trust_vc::requires(acc_eval >= floor)]
#[trust_vc::ensures(
    (acc_eval == obj_eval && floor == big_f && incumbent == big_f) ==> (obj_eval >= incumbent)
)]
pub fn optimum_terminal_lb_eq_ub(
    acc_eval: int,
    floor: int,
    obj_eval: int,
    big_f: int,
    incumbent: int,
) -> bool {
    acc_eval == obj_eval && floor == big_f && incumbent == big_f
}

/// NON-VACUITY CONTROL — WRONG OBJECTIVE FORM: drop the coefficient-equality half
/// of `derived == target` (`acc_eval == obj_eval`), accepting a derived bound on a
/// DIFFERENT linear form. The loop's bound then says nothing about THIS objective:
/// REFUTED (`acc_eval >= floor == big_f == incumbent` but `obj_eval < incumbent`).
/// Mirrors `negative_control_wrong_objective_form_is_rejected` (optimum_check.rs:920).
#[trust_vc::requires(acc_eval >= floor)]
#[trust_vc::ensures(
    (floor == big_f && incumbent == big_f) ==> (obj_eval >= incumbent)
)]
pub fn optimum_terminal_wrong_form(
    acc_eval: int,
    floor: int,
    obj_eval: int,
    big_f: int,
    incumbent: int,
) -> bool {
    floor == big_f && incumbent == big_f
}

/// NON-VACUITY CONTROL — OVERCOUNTED FLOOR: replace the checker's `floor == big_f`
/// by the unsound `big_f >= floor` (claim a floor AT OR ABOVE the degree the loop
/// actually reaches). REFUTED (`floor == acc_eval == obj_eval == incumbent's
/// neighbour` but `big_f > floor`, so `obj_eval < incumbent`). Mirrors
/// `negative_control_overcounted_floor_is_rejected` (optimum_check.rs:904): an
/// overcounted lower bound can NEVER yield a wrong OPTIMUM.
#[trust_vc::requires(acc_eval >= floor)]
#[trust_vc::ensures(
    (acc_eval == obj_eval && big_f >= floor && incumbent == big_f) ==> (obj_eval >= incumbent)
)]
pub fn optimum_terminal_overcount(
    acc_eval: int,
    floor: int,
    obj_eval: int,
    big_f: int,
    incumbent: int,
) -> bool {
    acc_eval == obj_eval && big_f >= floor && incumbent == big_f
}

/// NON-VACUITY CONTROL — DROP TIGHTNESS: promote to OPTIMUM regardless of
/// `incumbent == big_f`. Unsound when `incumbent > big_f` (the loop's floor is a
/// bound, not attained), so it would declare a non-optimal incumbent optimal.
/// REFUTED (`big_f <= obj_eval < incumbent`). Mirrors
/// `negative_control_floor_below_incumbent_is_not_optimum` (optimum_check.rs:935).
#[trust_vc::requires(acc_eval >= floor)]
#[trust_vc::ensures(
    (acc_eval == obj_eval && floor == big_f) ==> (obj_eval >= incumbent)
)]
pub fn optimum_terminal_drop_tightness(
    acc_eval: int,
    floor: int,
    obj_eval: int,
    big_f: int,
    incumbent: int,
) -> bool {
    acc_eval == obj_eval && floor == big_f
}

// ===========================================================================
// (iii) BOUNDED-N END-TO-END — the canonical Lean OPTIMUM example
// (`aggregation_certifies_lean_division_example`, optimum_check.rs:862) replayed
// at an ARBITRARY point `(x,y)` over ℤ. Input row `2x + 2y >= 3`; the floor
// derivation divides by 2 (ceil) to derive `x + y >= 2` (the floor `F = 2`).
// Incumbent `x=y=1` has objective value `2 == F` ⟹ OPTIMUM. Each derived fact is
// its own lemma, then composed into the LB==UB conclusion.
// ===========================================================================

/// The divide-by-2 ceil cut: from `2x + 2y >= 3` derive `x + y >= 2 = F` over ℤ
/// (`2S >= 3 ==> S >= 2`). This is the whole floor derivation for this instance.
/// PROVES `S >= 2`.
#[trust_vc::ensures((2 * x + 2 * y >= 3) ==> (result >= 2))]
pub fn division_example_derive_floor(x: int, y: int) -> int {
    x + y
}

/// NON-VACUITY CONTROL — overclaim the floor `S >= 3`. REFUTED (`x=1,y=1` gives
/// `2x+2y = 4 >= 3` but `x+y = 2 < 3`), pinning that the derived floor is exactly
/// `2`, not a vacuous over-claim.
#[trust_vc::ensures((2 * x + 2 * y >= 3) ==> (result >= 3))]
pub fn division_example_derive_floor_overclaim(x: int, y: int) -> int {
    x + y
}

/// END-TO-END OPTIMUM: the floor `F = 2` is a VALID lower bound on `obj = x + y`
/// over every feasible point (`2x+2y>=3`), and the VIG-verified incumbent attains
/// it (`incumbent == 2`). So `incumbent == 2 <= x + y` for every feasible `(x,y)`:
/// the incumbent is OPTIMAL (`LB == UB`). PROVES `x + y >= incumbent`.
#[trust_vc::ensures(
    (2 * x + 2 * y >= 3 && incumbent == 2) ==> (x + y >= incumbent)
)]
pub fn division_example_optimum(x: int, y: int, incumbent: int) -> bool {
    2 * x + 2 * y >= 3 && incumbent == 2
}

/// NON-VACUITY CONTROL — DROP THE INPUT ROW (no `2x+2y>=3`): the claim
/// "`x + y >= incumbent` for incumbent 2" is then FALSE (a feasible-of-nothing
/// point like `x=y=0` has `x+y = 0 < 2`), so it MUST be REFUTED — pinning that the
/// OPTIMUM above is GENUINELY carried by the derived floor, not vacuous.
#[trust_vc::ensures((incumbent == 2) ==> (x + y >= incumbent))]
pub fn division_example_optimum_drop_input(x: int, y: int, incumbent: int) -> bool {
    incumbent == 2
}
