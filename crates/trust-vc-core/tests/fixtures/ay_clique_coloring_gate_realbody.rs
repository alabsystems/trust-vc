// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// =====================================================================
// NON-VACUOUS native-deductive proof that the in-production IHALAINEN
// PBO-CLIQUE-COLORING certified-optimum accept path
// (`crate::optimize::clique_coloring::try_solve`,
// crates/ay-pb/src/optimize/clique_coloring.rs:308-360) emits
// `OptimumFound { value }` ONLY WHEN (a) the EXACT structural recognizer
// matched the canonical family — the hypothesis under which the
// kernel-verified clique lower-bound theorem `opt >= n - t` applies (Clean:
// `ay_pb_clique_coloring_lb.lean`) — and (b) the constructed colouring is
// re-verified feasible with objective `== n - t`. Discharged by trust-vc on
// the pure-Rust `ay` SMT solver, kernel-rechecked.
// =====================================================================
//
// THE ACCEPT-DECISION (verbatim real body, clique_coloring.rs:308-359)
// -------------------------------------------------------------------
// `try_solve` constructs the `((b-1) mod t)+1` colouring assignment, then GATES
// the `OptimumFound` emission on three re-checks:
//
//   1. Recognizer match — `detect(instance, objective)?` returns `Some(shape)`
//      ONLY IF the instance's constraint multiset equals the canonical
//      clique-coloring family EXACTLY (every A/B/C/D/E row present, none missing,
//      none extra). This is the hypothesis of the kernel LB theorem, so under a
//      match `opt >= n - t` holds (and `opt >= 0` always).
//
//   2. UB re-check — the constructed `assignment` is re-verified feasible against
//      the ORIGINAL rows by `verify_all_constraints`: a feasible colouring is a
//      valid UPPER bound `opt <= eval_objective(assignment) = value`.
//
//   3. Tightness — `value == lower_bound` where `lower_bound = (n - t).max(0)`.
//
// `lower_bound <= opt <= value` together with `value == lower_bound` FORCES
// `opt == value`.
//
// --- the recognizer `?` (clique_coloring.rs:309) ---
// CONFORMANCE: src/optimize/clique_coloring.rs:309-309
//     let shape = detect(instance, objective)?;
//
// --- the UB re-check, the clamped lower bound, the tightness gate, and the
//     OPTIMUM emission (clique_coloring.rs:343-359) ---
// CONFORMANCE: src/optimize/clique_coloring.rs:343-359
//     if !verify_all_constraints(&instance.constraints, &assignment) {
//         return None;
//     }
//     // 1 + 3. The exact structural match in `detect` established the clique lower
//     // bound `opt >= n - t`; require the UB to meet it exactly.
//     let lower_bound = (n as i128) - (t as i128);
//     let lower_bound = lower_bound.max(0);
//     let value = eval_objective(objective, &assignment);
//     if value != lower_bound {
//         return None;
//     }
//
//     Some(PbSolution {
//         status: PbStatus::OptimumFound,
//         assignment,
//         objective: Some(value),
//     })
//
// HOW THE INPUTS ARE MODELED (identical methodology to incumbent_vig_realbody.rs
// and domset_gate_realbody.rs): the decision's inputs are free symbolic variables:
//   * `recognizer_matched : bool` = `detect(..).is_some()`.
//   * `ub_feasible : bool` = `verify_all_constraints(constraints, assignment)`.
//   * `value : int` = `eval_objective(objective, assignment)`.
//   * `lower_bound : int` = `(n - t).max(0)`.
// Proving the gate for ARBITRARY values proves it for the real re-check results in
// particular, which is why the unsound controls are REFUTED, not vacuously
// accepted.
//
// HOW VERIFIED: `trust_vc_core::verify_function_from_file(<this file>, <fn>)`.
// `Verified` == ay returned UNSAT and the kernel accepted the proof;
// `Counterexample` == ay returned a concrete falsifying model.

// ===========================================================================
// THE GATE — `OptimumFound` is emitted (`result`) ONLY WHEN all three re-checks
// held. Body is the conjunction the `?`/early-`return`/`if` guards compute: the
// `Some(OptimumFound)` tail is reached IFF `recognizer_matched` (the `detect` `?`
// did not bail) AND `ub_feasible` (the colouring passed the VIG) AND `value ==
// lower_bound` (the tightness gate). CONTRACT (soundness direction): emitting
// OPTIMUM implies every re-check held. PROVES.
// ===========================================================================
#[trust_vc::ensures(result ==> (recognizer_matched && ub_feasible && value == lower_bound))]
pub fn clique_coloring_emit_optimum(
    recognizer_matched: bool,
    ub_feasible: bool,
    value: int,
    lower_bound: int,
) -> bool {
    recognizer_matched && ub_feasible && value == lower_bound
}

/// NON-VACUITY CONTROL — DROP THE RECOGNIZER MATCH. Emits OPTIMUM without
/// requiring `detect` to have matched the canonical family. The kernel LB theorem
/// `opt >= n - t` then has no hypothesis, so the claimed bound is unfounded and the
/// reported value need not be optimal. REFUTED (`recognizer_matched = false`,
/// others holding). Pins that the EXACT structural match is LOAD-BEARING.
#[trust_vc::ensures(result ==> (recognizer_matched && ub_feasible && value == lower_bound))]
pub fn clique_coloring_emit_drop_recognizer_wrong(
    recognizer_matched: bool,
    ub_feasible: bool,
    value: int,
    lower_bound: int,
) -> bool {
    let _ = recognizer_matched; // BUG: claims optimum on an unrecognized instance
    ub_feasible && value == lower_bound
}

/// NON-VACUITY CONTROL — DROP THE UB FEASIBILITY RE-CHECK. Emits OPTIMUM without
/// re-verifying the constructed colouring against the ORIGINAL rows. Then `value`
/// is not a valid upper bound on `opt`. REFUTED (`ub_feasible = false`, others
/// holding). Pins that the `verify_all_constraints` UB re-check is LOAD-BEARING.
#[trust_vc::ensures(result ==> (recognizer_matched && ub_feasible && value == lower_bound))]
pub fn clique_coloring_emit_drop_feasible_wrong(
    recognizer_matched: bool,
    ub_feasible: bool,
    value: int,
    lower_bound: int,
) -> bool {
    let _ = ub_feasible; // BUG: never re-verifies the colouring is feasible
    recognizer_matched && value == lower_bound
}

/// NON-VACUITY CONTROL — DROP THE TIGHTNESS GATE. Emits OPTIMUM without requiring
/// `value == lower_bound`, so a feasible-but-suboptimal colouring (value above the
/// LB) would be reported as optimal. REFUTED (`value != lower_bound`, both other
/// re-checks holding). Pins that the LB==UB tightness gate is LOAD-BEARING.
#[trust_vc::ensures(result ==> (recognizer_matched && ub_feasible && value == lower_bound))]
pub fn clique_coloring_emit_drop_tightness_wrong(
    recognizer_matched: bool,
    ub_feasible: bool,
    value: int,
    lower_bound: int,
) -> bool {
    recognizer_matched && ub_feasible // BUG: drops `value == lower_bound`
}

// ===========================================================================
// THE CLAMP — `lower_bound = (n - t).max(0)` (clique_coloring.rs:348-349). The
// clamped value is a valid lower-bound FLOOR: it dominates BOTH the kernel clique
// bound `n - t` AND the trivial `0` bound, and it is exactly one of the two.
// PROVES (`result >= n - t && result >= 0 && (result == n - t || result == 0)`).
// ===========================================================================
#[trust_vc::ensures(result >= n - t && result >= 0 && (result == n - t || result == 0))]
pub fn clique_coloring_lower_bound(n: int, t: int) -> int {
    let lower_bound = n - t;
    if lower_bound >= 0 {
        lower_bound
    } else {
        0
    }
}

// ===========================================================================
// SOUNDNESS COROLLARY — the bracket forces optimality. The recognizer match gives
// the kernel LOWER bound `opt >= n - t`; the objective is a sum of 0/1 indicators
// so `opt >= 0`; the clamp `lb = (n-t).max(0)` (`lb == n - t || lb == 0`) is thus
// `<= opt`. The feasible colouring gives the UPPER bound `opt <= value`; the
// tightness gate gives `value == lb`. Together these FORCE `opt == value`: the
// emitted value is the exact optimum. PROVES (pure ℤ arithmetic + the clamp
// disjunction).
// ===========================================================================
#[trust_vc::ensures(
    (opt >= n - t && opt >= 0 && opt <= value && value == lb && (lb == n - t || lb == 0))
        ==> (opt == value)
)]
pub fn clique_coloring_bracket_forces_optimum(
    opt: int,
    n: int,
    t: int,
    value: int,
    lb: int,
) -> bool {
    opt >= n - t && opt >= 0 && opt <= value && value == lb && (lb == n - t || lb == 0)
}

/// NON-VACUITY CONTROL for the bracket — DROP THE KERNEL LB premise
/// (`opt >= n - t`, i.e. no recognizer match). Then the clamp `lb` can exceed
/// `opt` (when `lb == n - t > opt >= 0`), so `value == lb` no longer pins `opt`:
/// REFUTED (e.g. `n - t = lb = value = 5`, `opt = 3`). Pins that the recognizer's
/// LB theorem is what closes the bracket from below.
#[trust_vc::ensures(
    (opt >= 0 && opt <= value && value == lb && (lb == n - t || lb == 0))
        ==> (opt == value)
)]
pub fn clique_coloring_bracket_drop_lb_wrong(
    opt: int,
    n: int,
    t: int,
    value: int,
    lb: int,
) -> bool {
    opt >= 0 && opt <= value && value == lb && (lb == n - t || lb == 0)
}
