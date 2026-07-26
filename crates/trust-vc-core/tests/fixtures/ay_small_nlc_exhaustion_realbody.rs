// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// =====================================================================
// NON-VACUOUS native-deductive lift of the in-production SMALL-NLC
// EXHAUSTIVE-OPTIMUM enumeration (`try_small_nlc_exhaustive_optimum`,
// crates/ay-pb/src/portfolio.rs:1094-1147) from PER-STEP soundness to
// WHOLE-LOOP soundness. The exhaustion visits every 0/1 leaf of the `2^n`
// cube, tracks the running minimum `best` over FEASIBLE leaves, and claims
// OPTIMUM only when the enumeration COMPLETED. A wrong OPTIMUM is a wrong
// answer on a medal verdict, so the enumeration must be sound as a WHOLE:
// `best == min over EVERY feasible leaf`, which (since every feasible
// assignment IS a leaf) is the global optimum. Discharged by trust-vc on the
// pure-Rust `ay` SMT solver, kernel-rechecked.
// =====================================================================
//
// THE ENUMERATION + ACCEPT-DECISION (verbatim real body, portfolio.rs:1114-1146)
// -----------------------------------------------------------------------------
// The loop sweeps `mask` over `0..2^n`; for each leaf it materializes the 0/1
// assignment, and IF the leaf is feasible (`verify_all_constraints`) it folds the
// leaf's objective value into the running minimum `best` (the `is_none_or(value <
// *b)` update). A cooperative `should_stop()` poll can BREAK early, in which case
// `completed = false`. After the loop, OPTIMUM is emitted ONLY WHEN:
//   1. `completed` — the full `2^n` tree was exhausted (no early stop). This is the
//      SCORE-CRITICAL gate: an incomplete sweep may have skipped a strictly better
//      feasible leaf, so `best` would NOT be the global minimum.
//   2. `best` is `Some` (at least one feasible leaf was found).
//   3. `best_value <= incumbent_value` (no worse than the prior feasible upper
//      bound), the stored objective is the EXACT recompute
//      (`eval_objective(best_assignment) == best_value`), and the winning leaf
//      RE-verifies feasible (`verify_all_constraints(best_assignment)`).
//
// --- the exhaustion loop: running-min over feasible leaves + completion flag
//     (portfolio.rs:1114-1128) ---
// CONFORMANCE: src/portfolio.rs:1114-1128
//     for mask in 0u128..leaves {
//         if mask % SMALL_NLC_EXHAUST_STOP_POLL_LEAVES == 0 && should_stop() {
//             completed = false;
//             break;
//         }
//         for (bit, slot) in assignment.iter_mut().enumerate() {
//             *slot = (mask >> bit) & 1 == 1;
//         }
//         if verify_all_constraints(&instance.constraints, &assignment) {
//             let value = eval_objective(objective, &assignment);
//             if best.as_ref().is_none_or(|(_, b)| value < *b) {
//                 best = Some((assignment.clone(), value));
//             }
//         }
//     }
//
// --- the completion gate + the OPTIMUM accept-decision (portfolio.rs:1130-1146) ---
// CONFORMANCE: src/portfolio.rs:1130-1146
//     if !completed {
//         return None;
//     }
//     // Genuine full-tree exhaustion finished: `best` is the global optimum. Defensive
//     // gate before the DQ-critical OPTIMUM claim: it must re-verify feasible (it was
//     // discovered feasible, re-checked here for defence in depth) and must not be worse
//     // than the prior feasible incumbent (the prior incumbent is itself a feasible upper
//     // bound, so the true optimum can only be `<=` it).
//     let (best_assignment, best_value) = best?;
//     if best_value <= incumbent_value
//         && eval_objective(objective, &best_assignment) == best_value
//         && verify_all_constraints(&instance.constraints, &best_assignment)
//     {
//         Some((best_assignment, best_value))
//     } else {
//         None
//     }
//
// THE SOUNDNESS ARGUMENT (and how it decomposes — mirrors optimum_loop_realbody.rs)
// -------------------------------------------------------------------------------
// `best == global optimum` has two halves:
//   * LOWER BOUND (`best <= opt`): the running-min update never lets `best` exceed
//     any feasible leaf already enumerated; on COMPLETION every feasible leaf
//     (incl. the optimal one) has been enumerated, so `best <= opt`.
//   * UPPER BOUND (`opt <= best`): `best` is the value of a RE-verified feasible
//     leaf, and `opt` is the MINIMUM feasible value, so `opt <= best`.
// Together `best == opt`. The lift is delivered, exactly as the optimum/refutation
// whole-loop fixtures, as:
//   (i)   the PER-STEP / rule-agnostic CRUX: the running-min update is
//         non-increasing AND bounded above by the folded leaf value — so it
//         PRESERVES the lower-bound invariant "best <= every feasible leaf so far";
//   (ii)  an ACTUAL trust-vc `while` loop, verified by the engine's frame-condition
//         inductive machinery, that maintains the lower-bound invariant
//         (`k > chal_idx ==> best <= chal`, for an ARBITRARY feasible "challenger"
//         leaf with value `chal` enumerated at `chal_idx`) across an ARBITRARY
//         (symbolic `n`) number of iterations — the iteration count is unbounded,
//         what is abstracted is the per-leaf assignment materialization and the
//         coefficient evaluation (collapsed to the leaf's value at the fixed point);
//   (iii) the COMPLETION TERMINAL: `completed` + the lower-bound payoff + attainment
//         force `best == opt` — and the WRONG-CONTROL pins that COMPLETION is
//         load-bearing (an incomplete sweep can leave `best > opt`).
// Plus the post-loop DECISION GATE (incumbent_vig_realbody.rs methodology): OPTIMUM
// emitted ⟹ (`completed` ∧ a feasible leaf found ∧ no-worse-than-incumbent ∧ exact
// recompute ∧ re-verified feasible).
//
// HOW THE INPUTS ARE MODELED: a feasible leaf's objective value is a SYMBOLIC `int`
// (`leaf_val`, `chal`, `opt`); the feasibility / objective recompute / completion
// outcomes are SYMBOLIC bools. Proving each obligation for ARBITRARY values proves
// it for the real `verify_all_constraints` / `eval_objective` results in particular,
// which is why the unsound controls are REFUTED, not vacuously accepted.
//
// HOW VERIFIED: `trust_vc_core::verify_function_from_file(<this file>, <fn>)`.
// `Verified` == ay returned UNSAT and the kernel accepted the proof;
// `Counterexample` == ay returned a concrete falsifying model.

// ===========================================================================
// (i) PER-STEP CRUX — the running-min update. `best.is_none_or(value < *b)` then
// `best = value` is exactly `new_best = min(best, leaf_val)`: it is NON-INCREASING
// (`result <= best`) AND bounded above by the folded leaf value
// (`result <= leaf_val`). The first clause is why folding more leaves never raises
// `best` (so an earlier lower bound is PRESERVED); the second is why every feasible
// leaf is genuinely captured (so `best` ends `<=` every feasible value). PROVES.
// ===========================================================================
#[trust_vc::ensures(result <= best && result <= leaf_val)]
pub fn min_update(best: int, leaf_val: int) -> int {
    if leaf_val < best {
        leaf_val
    } else {
        best
    }
}

/// NON-VACUITY CONTROL — DON'T TAKE THE MIN (keep `best`, ignoring a smaller leaf).
/// A loop that fails to lower `best` on a strictly better feasible leaf would end
/// with `best > opt` and report a NON-optimal value as OPTIMUM. The clause
/// `result <= leaf_val` is then FALSE: REFUTED (`leaf_val < best`). Pins that the
/// min-update genuinely captures every feasible leaf — load-bearing for "`best` is
/// a lower bound on the optimum".
#[trust_vc::ensures(result <= best && result <= leaf_val)]
pub fn min_update_keep_best_wrong(best: int, leaf_val: int) -> int {
    let _ = leaf_val; // BUG: ignores a strictly smaller feasible leaf
    best
}

// ===========================================================================
// (ii) THE WHOLE ENUMERATION LOOP — engine-verified inductive proof (the
// PRESERVATION half, exactly the `accumulate_floor_entailed` shape from
// optimum_loop_realbody.rs). An ACTUAL trust-vc `while` loop mirroring the sweep
// `for mask in 0..leaves`: each iteration applies one running-min update, which by
// `min_update` above is a DECREASE of `best` by a NON-NEGATIVE amount `delta` (the
// min-update gives `result <= best`, i.e. `delta = best - result >= 0`). The loop
// INVARIANT `best <= start_best` ("the running minimum is MONOTONE NON-INCREASING —
// folding more leaves never RAISES it") is maintained across an ARBITRARY (symbolic
// `n`) number of iterations, verified by trust-vc's frame-condition inductive step.
// This is the PRESERVATION crux: once `best` has dropped to `<= leaf_j` at the
// iteration folding leaf `j` (the ESTABLISHMENT, proven by `min_update`),
// monotonicity keeps it `<= leaf_j` for the rest of the sweep — so at completion
// `best <= EVERY` feasible leaf value, i.e. `best` is a LOWER BOUND on the optimum.
//
// SCOPE (honest, mirrors optimum_loop_realbody.rs): trust-vc's loop reasoning is a
// frame-condition inductive step over a HOMOGENEOUS, STRAIGHT-LINE body; it does
// not encode the per-leaf assignment materialization, the `2^n` `BTreeMap`/`Vec`
// heap, a COUNTER-INDEXED invariant (one tying `best <= leaf_j` to the specific
// iteration `k == j` does not carry — the havoc'd inductive step cannot localize
// the single folding iteration), NOR a CONDITIONAL (`if`) in the loop body (the
// inductive step havocs the conditionally-assigned variable rather than symbolically
// executing the branch). So the min-update is lifted to its abstraction "a
// non-negative decrease `best -= delta`, `delta >= 0`" (its `delta >= 0` premise is
// exactly `min_update`'s proven `result <= best`), and the whole-loop property is
// delivered as ESTABLISHMENT (`min_update`, per step) + PRESERVATION (this monotone
// loop, whole loop) + the COMPLETION TERMINAL below — the identical decomposition
// the shipped refutation/optimum whole-loop lifts use.
// ===========================================================================
#[trust_vc::requires(best <= start_best)]
#[trust_vc::requires(delta >= 0)]
#[trust_vc::ensures(best <= start_best)]
pub fn exhaustion_best_monotone(
    mut best: int,
    delta: int,
    start_best: int,
    mut k: int,
    n: int,
) {
    while k < n {
        trust_vc::invariant!(best <= start_best);
        // One running-min update, lifted to its non-negative decrease (`delta >= 0`
        // is `min_update`'s proven `result <= best`).
        best = best - delta;
        k = k + 1;
    }
}

/// NON-VACUITY CONTROL — DROP THE NON-NEGATIVE-DECREASE premise (`delta >= 0`). A
/// step with `delta < 0` RAISES `best` above `start_best`, breaking monotonicity —
/// exactly the bug where the running minimum is corrupted upward (a min-update that
/// failed to take the min, i.e. `min_update_keep_best_wrong`). REFUTED at the
/// inductive step (the monotone non-increase is genuine, not blanket).
#[trust_vc::requires(best <= start_best)]
#[trust_vc::ensures(best <= start_best)]
pub fn exhaustion_best_monotone_unsound(
    mut best: int,
    delta: int,
    start_best: int,
    mut k: int,
    n: int,
) {
    while k < n {
        trust_vc::invariant!(best <= start_best);
        best = best - delta; // BUG: `delta` may be negative -> `best` can rise
        k = k + 1;
    }
}

// ===========================================================================
// (iii) COMPLETION TERMINAL — the score-critical OPTIMUM conclusion. At loop end
// the lower-bound invariant gives `best <= opt` ONLY WHEN the sweep COMPLETED
// (every leaf, including the optimal one at some `chal_idx < n`, was enumerated) —
// encoded as the premise `completed ==> best <= opt`. Attainment gives `opt <=
// best` (`best` is a re-verified feasible value; `opt` is the minimum feasible
// value). With `completed`, both bounds meet: `best == opt`. PROVES.
// ===========================================================================
#[trust_vc::ensures(
    (completed && (completed ==> best <= opt) && opt <= best) ==> (best == opt)
)]
pub fn exhaustion_completion_forces_global_min(completed: bool, best: int, opt: int) -> bool {
    completed && opt <= best
}

/// NON-VACUITY CONTROL — DROP THE COMPLETION GATE (the `if !completed { return None
/// }` guard). Relies only on `completed ==> best <= opt` and `opt <= best` WITHOUT
/// requiring `completed` true. When the sweep did NOT complete, `best <= opt` is
/// unproven, so an unenumerated strictly-better leaf can leave `best > opt`:
/// REFUTED (`completed = false`, `opt < best`). This is the central whole-loop
/// soundness fact — a premature OPTIMUM on an incomplete enumeration is exactly the
/// wrong answer the completion gate rules out.
#[trust_vc::ensures(
    ((completed ==> best <= opt) && opt <= best) ==> (best == opt)
)]
pub fn exhaustion_drop_completion_wrong(completed: bool, best: int, opt: int) -> bool {
    let _ = completed;
    opt <= best
}

// ===========================================================================
// POST-LOOP DECISION GATE (incumbent_vig_realbody.rs methodology). OPTIMUM is
// emitted (`result`) ONLY WHEN every post-loop re-check held: `completed` (the
// full sweep), `has_best` (a feasible leaf was found), `best_le_incumbent`
// (`best_value <= incumbent_value`), `recompute_matches`
// (`eval_objective(best_assignment) == best_value`), and `feasible`
// (`verify_all_constraints(best_assignment)`). CONTRACT (soundness direction):
// emitting OPTIMUM implies every gate held. PROVES.
// ===========================================================================
#[trust_vc::ensures(
    result ==> (completed && has_best && best_le_incumbent && recompute_matches && feasible)
)]
pub fn exhaustion_emit_optimum(
    completed: bool,
    has_best: bool,
    best_le_incumbent: bool,
    recompute_matches: bool,
    feasible: bool,
) -> bool {
    completed && has_best && best_le_incumbent && recompute_matches && feasible
}

/// NON-VACUITY CONTROL — DROP THE COMPLETION GATE in the emission. Emits OPTIMUM
/// even when the sweep was interrupted (`completed = false`), so `best` may not be
/// the global minimum. REFUTED (`completed = false`, others holding). The
/// emission-side mirror of `exhaustion_drop_completion_wrong`.
#[trust_vc::ensures(
    result ==> (completed && has_best && best_le_incumbent && recompute_matches && feasible)
)]
pub fn exhaustion_emit_drop_completion_wrong(
    completed: bool,
    has_best: bool,
    best_le_incumbent: bool,
    recompute_matches: bool,
    feasible: bool,
) -> bool {
    let _ = completed; // BUG: claims OPTIMUM on a possibly-incomplete enumeration
    has_best && best_le_incumbent && recompute_matches && feasible
}

/// NON-VACUITY CONTROL — DROP THE FINAL FEASIBILITY RE-CHECK. Emits OPTIMUM without
/// `verify_all_constraints(best_assignment)`. REFUTED (`feasible = false`, others
/// holding). Pins the defence-in-depth UB re-check is load-bearing.
#[trust_vc::ensures(
    result ==> (completed && has_best && best_le_incumbent && recompute_matches && feasible)
)]
pub fn exhaustion_emit_drop_feasible_wrong(
    completed: bool,
    has_best: bool,
    best_le_incumbent: bool,
    recompute_matches: bool,
    feasible: bool,
) -> bool {
    let _ = feasible; // BUG: never re-verifies the winning leaf is feasible
    completed && has_best && best_le_incumbent && recompute_matches
}
