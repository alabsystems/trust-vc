// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// =====================================================================
// NON-VACUOUS native-deductive proof that the in-production MINIMUM
// DOMINATING SET certified-optimum accept path
// (`crate::optimize::dominating_set::try_solve`,
// crates/ay-pb/src/optimize/dominating_set.rs:163-229) emits
// `OptimumFound { value }` ONLY WHEN three independently re-checkable facts
// hold, so the reported optimum is BRACKETED `|S| <= gamma(G) <= |D|` with
// equality. Discharged by trust-vc on the pure-Rust `ay` SMT solver,
// kernel-rechecked.
// =====================================================================
//
// THE ACCEPT-DECISION (verbatim real body, dominating_set.rs:188-228)
// ------------------------------------------------------------------
// `try_solve` greedily proposes a 2-packing `S` and a dominating-set candidate
// `D`, then GATES the `OptimumFound` emission on three re-checks (none of which
// trusts the greedy producer):
//
//   1. LB re-check — `certified_two_packing_size(&packing, nbhd, n)?` returns
//      `Some(|S|)` ONLY IF `packing` is a GENUINE 2-packing (closed
//      neighbourhoods pairwise disjoint, each containing its centre). A genuine
//      2-packing is a valid LOWER bound: `gamma(G) >= |S|`.
//
//   2. UB re-check — the chosen `assignment` (the packing centres, else the
//      projected incumbent) is re-verified feasible against the ORIGINAL rows by
//      `verify_all_constraints`. A feasible dominating set is a valid UPPER
//      bound: `gamma(G) <= eval_objective(D) = value`.
//
//   3. Tightness — `value == packing_size` (`|D| == |S|`).
//
// `|S| <= gamma(G) <= |D|` together with `|D| == |S|` FORCES `gamma(G) == value`.
//
// --- the LB re-check (dominating_set.rs:190): the 2-packing certificate `?` ---
// CONFORMANCE: src/optimize/dominating_set.rs:190-190
//     let packing_size = certified_two_packing_size(&packing, nbhd, n)?;
//
// --- the UB re-check (dominating_set.rs:200-214): whichever candidate is chosen
//     is re-verified feasible by `verify_all_constraints`; the only non-`return`
//     paths leave `assignment` VIG-feasible (centres branch, else projected) ---
// CONFORMANCE: src/optimize/dominating_set.rs:200-214
//     let assignment = if verify_all_constraints(&instance.constraints, &centers) {
//         centers
//     } else {
//         // Candidate B: AY's incumbent (only certifies if its value matches the
//         // LB; a strictly larger incumbent means packing < domination -> decline).
//         let inc = incumbent?;
//         let mut projected = vec![false; n];
//         for (v, slot) in projected.iter_mut().enumerate() {
//             *slot = inc.get(v).copied().unwrap_or(false);
//         }
//         if !verify_all_constraints(&instance.constraints, &projected) {
//             return None;
//         }
//         projected
//     };
//
// --- the tightness gate + the OPTIMUM emission (dominating_set.rs:219-228) ---
// CONFORMANCE: src/optimize/dominating_set.rs:219-228
//     let value = eval_objective(objective, &assignment);
//     if value != packing_size {
//         return None;
//     }
//
//     Some(PbSolution {
//         status: PbStatus::OptimumFound,
//         assignment,
//         objective: Some(value),
//     })
//
// HOW THE THREE RE-CHECKS ARE MODELED (the established per-decision methodology,
// identical to `incumbent_vig_realbody.rs`)
// ----------------------------------------------------------------------------
// Exactly as `incumbent_vig_realbody` models the VIG decision by a SYMBOLIC bool
// `feasible` and the objective recompute by a SYMBOLIC `actual`, this fixture
// models the accept-decision's three inputs as free variables:
//   * `packing_ok : bool` = `certified_two_packing_size(..).is_some()` — whether
//     the 2-packing certificate re-check passed.
//   * `domset_feasible : bool` = `verify_all_constraints(constraints, assignment)`
//     for whichever candidate is chosen — the UB feasibility re-check.
//   * `value : int` = `eval_objective(objective, assignment)` = `|D|` (the UB).
//   * `packing_size : int` = the certified `|S|` (the LB).
// Proving the gate for ARBITRARY values proves it for the real re-check results
// in particular — which is exactly why the unsound controls below are REFUTED
// rather than vacuously accepted. (That `certified_two_packing_size` faithfully
// validates a 2-packing, and `verify_all_constraints` faithfully computes the AND
// over the constraints, are SEPARATE re-checks; the latter is already discharged
// in `verify_all_constraints_realbody.rs`.)
//
// HOW VERIFIED: `trust_vc_core::verify_function_from_file(<this file>, <fn>)`.
// `Verified` == ay returned UNSAT and the kernel accepted the proof;
// `Counterexample` == ay returned a concrete falsifying model.

// ===========================================================================
// THE GATE — `OptimumFound` is emitted (`result`) ONLY WHEN all three re-checks
// held. Body is the conjunction the three `?`/early-`return`/`if` guards compute:
// the `Some(OptimumFound)` tail is reached IFF `packing_ok` (the LB `?` did not
// bail) AND `domset_feasible` (the chosen assignment passed the VIG) AND
// `value == packing_size` (the tightness gate). CONTRACT (soundness direction):
// emitting OPTIMUM implies every re-check held. PROVES.
// ===========================================================================
#[trust_vc::ensures(result ==> (packing_ok && domset_feasible && value == packing_size))]
pub fn domset_emit_optimum(
    packing_ok: bool,
    domset_feasible: bool,
    value: int,
    packing_size: int,
) -> bool {
    packing_ok && domset_feasible && value == packing_size
}

/// NON-VACUITY CONTROL — DROP THE LB RE-CHECK. Emits OPTIMUM without requiring
/// the 2-packing certificate (`packing_ok`). Then `|S|` is unverified, so the
/// claimed lower bound could exceed `gamma(G)` and the emitted `value` need not be
/// the true optimum. The contract `result ==> packing_ok && ..` is FALSE:
/// REFUTED (`packing_ok = false`, `domset_feasible = true`,
/// `value == packing_size`). Pins that the 2-packing re-check is LOAD-BEARING.
#[trust_vc::ensures(result ==> (packing_ok && domset_feasible && value == packing_size))]
pub fn domset_emit_drop_packing_check_wrong(
    packing_ok: bool,
    domset_feasible: bool,
    value: int,
    packing_size: int,
) -> bool {
    let _ = packing_ok; // BUG: never re-checks the 2-packing lower-bound certificate
    domset_feasible && value == packing_size
}

/// NON-VACUITY CONTROL — DROP THE UB FEASIBILITY RE-CHECK. Emits OPTIMUM without
/// re-verifying the chosen dominating set against the ORIGINAL rows
/// (`domset_feasible`). Then `value` is not a valid upper bound on `gamma(G)` and
/// could be below it. REFUTED (`domset_feasible = false`, others holding). Pins
/// that the `verify_all_constraints` UB re-check is LOAD-BEARING.
#[trust_vc::ensures(result ==> (packing_ok && domset_feasible && value == packing_size))]
pub fn domset_emit_drop_feasible_check_wrong(
    packing_ok: bool,
    domset_feasible: bool,
    value: int,
    packing_size: int,
) -> bool {
    let _ = domset_feasible; // BUG: never re-verifies the dominating set is feasible
    packing_ok && value == packing_size
}

/// NON-VACUITY CONTROL — DROP THE TIGHTNESS GATE. Emits OPTIMUM without requiring
/// `value == packing_size` (`|D| == |S|`). A non-tight packing (`|S| < |D|`)
/// would then be reported as optimal even though only `|S| <= gamma <= |D|` is
/// known. REFUTED (`value != packing_size`, both re-checks holding). Pins that the
/// LB==UB tightness gate is LOAD-BEARING.
#[trust_vc::ensures(result ==> (packing_ok && domset_feasible && value == packing_size))]
pub fn domset_emit_drop_tightness_wrong(
    packing_ok: bool,
    domset_feasible: bool,
    value: int,
    packing_size: int,
) -> bool {
    packing_ok && domset_feasible // BUG: drops `value == packing_size`
}

// ===========================================================================
// SOUNDNESS COROLLARY — the bracket forces optimality. The genuine 2-packing
// gives the LOWER bound `packing_size <= gamma`; the feasible dominating set gives
// the UPPER bound `gamma <= value`; the tightness gate gives `value ==
// packing_size`. Together these FORCE `gamma == value`: the emitted value is the
// exact domination number. PROVES (pure ℤ arithmetic).
// ===========================================================================
#[trust_vc::ensures(
    (packing_size <= gamma && gamma <= value && value == packing_size) ==> (gamma == value)
)]
pub fn domset_bracket_forces_optimum(gamma: int, packing_size: int, value: int) -> bool {
    packing_size <= gamma && gamma <= value && value == packing_size
}

/// NON-VACUITY CONTROL for the bracket — DROP THE LOWER-BOUND fact (no genuine
/// 2-packing, so `packing_size <= gamma` is not established). Then `value ==
/// packing_size` no longer pins `gamma`: REFUTED (`gamma > value`, e.g. a
/// too-small unverified packing). Pins that the LB witness is what closes the
/// bracket from below.
#[trust_vc::ensures(
    (gamma <= value && value == packing_size) ==> (gamma == value)
)]
pub fn domset_bracket_drop_lower_wrong(gamma: int, packing_size: int, value: int) -> bool {
    let _ = packing_size;
    gamma <= value
}
