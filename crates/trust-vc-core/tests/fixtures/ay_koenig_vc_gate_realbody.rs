// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// =====================================================================
// NON-VACUOUS native-deductive proof that the in-production KÖNIG
// BIPARTITE MINIMUM-VERTEX-COVER certified-optimum accept path
// (`crate::optimize::bipartite_vertex_cover::try_solve`,
// crates/ay-pb/src/optimize/bipartite_vertex_cover.rs:134-229) emits
// `OptimumFound { value }` ONLY WHEN three independently re-checkable facts
// hold, so the reported optimum is BRACKETED `|M| <= tau <= |C|` with
// equality (tau = the minimum vertex cover number). This is the ORIGINAL
// structural OPTIMUM certificate the score levers (dominating set,
// clique-coloring) mirror. Discharged by trust-vc on the pure-Rust `ay` SMT
// solver, kernel-rechecked.
// =====================================================================
//
// THE ACCEPT-DECISION (verbatim real body, bipartite_vertex_cover.rs:211-228)
// --------------------------------------------------------------------------
// König's theorem: in a bipartite graph `|min vertex cover| = |max matching|`.
// `try_solve` computes a maximum matching `M` (Hopcroft-Karp) and the König
// cover `C` from heuristic code, then GATES the `OptimumFound` emission on three
// re-checks (NONE of which trusts the matching/König producer):
//
//   1. UB re-check — the cover `assignment` is re-verified feasible against the
//      ORIGINAL constraints by `verify_all_constraints`. A feasible vertex cover
//      is a valid UPPER bound: `tau <= eval_objective(C) = value`.
//
//   2. LB re-check — `certified_matching_size(&matching, &adjacency, &color)?`
//      returns `Some(|M|)` ONLY IF `matching` is a GENUINE matching: each
//      partner is SYMMETRIC (`matching[matching[v]] == v`), a REAL edge
//      (`adjacency[v].contains(partner)`), and properly bipartite-ORIENTED
//      (`color[v] != color[partner]`); the disjoint matched pairs are counted
//      once. A genuine matching of pairwise-disjoint real edges forces every
//      vertex cover to take >= 1 endpoint per edge, so it is a valid LOWER
//      bound: `tau >= |M|`.
//
//   3. Tightness — `value == matching_size` (`|C| == |M|`).
//
// `|M| <= tau <= |C|` together with `|C| == |M|` FORCES `tau == value`. A bug in
// Hopcroft-Karp or the König cover construction simply fails one of the three
// re-checks and returns `None` (the general portfolio then runs) — never a wrong
// optimum. The emitted objective is literally `Some(value)`, so the reported
// `v == value`, and the tightness gate makes `v == matching_size`.
//
// --- the UB re-check (bipartite_vertex_cover.rs:213-215): the cover is
//     re-verified feasible against the ORIGINAL constraints ---
// CONFORMANCE: src/optimize/bipartite_vertex_cover.rs:213-215
//     if !verify_all_constraints(&instance.constraints, &assignment) {
//         return None;
//     }
//
// --- the LB re-check (bipartite_vertex_cover.rs:217): the matching certificate
//     `?` (genuine matching => |M| is a valid lower bound) ---
// CONFORMANCE: src/optimize/bipartite_vertex_cover.rs:217-217
//     let matching_size = certified_matching_size(&matching, &adjacency, &color)?;
//
// --- the tightness gate + the OPTIMUM emission (bipartite_vertex_cover.rs:219-228) ---
// CONFORMANCE: src/optimize/bipartite_vertex_cover.rs:219-228
//     let value = eval_objective(objective, &assignment);
//     if value != matching_size {
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
// identical to `domset_gate_realbody.rs` / `incumbent_vig_realbody.rs`)
// ----------------------------------------------------------------------------
// The accept-decision's three inputs are modeled as free variables:
//   * `cover_feasible : bool` = `verify_all_constraints(constraints, assignment)`
//     — the UB feasibility re-check (the `if !.. { return None }` did not fire).
//   * `matching_certified : bool` = `certified_matching_size(..).is_some()` —
//     whether the matching certificate `?` re-check passed.
//   * `value : int` = `eval_objective(objective, assignment)` = `|C|` (the UB,
//     and the literal emitted objective `v`).
//   * `matching_size : int` = the certified `|M|` (the LB).
// Proving the gate for ARBITRARY values proves it for the real re-check results
// in particular — which is exactly why the unsound controls below are REFUTED
// rather than vacuously accepted. (That `certified_matching_size` faithfully
// validates a matching, and `verify_all_constraints` faithfully computes the AND
// over the constraints, are SEPARATE re-checks; the latter is already discharged
// in `verify_all_constraints_realbody.rs`.)
//
// HOW VERIFIED: `trust_vc_core::verify_function_from_file(<this file>, <fn>)`.
// `Verified` == ay returned UNSAT and the kernel accepted the proof;
// `Counterexample` == ay returned a concrete falsifying model.

// ===========================================================================
// THE GATE — `OptimumFound` is emitted (`result`) ONLY WHEN all three re-checks
// held. Body is the conjunction the three guards compute: the `Some(OptimumFound)`
// tail is reached IFF `cover_feasible` (the UB `if !.. return None` did not fire)
// AND `matching_certified` (the LB `?` did not bail) AND `value == matching_size`
// (the tightness gate). CONTRACT (soundness direction): emitting OPTIMUM implies
// every re-check held — and since the emitted objective is `Some(value)`, this is
// exactly `Some(OptimumFound v) ==> (cover_feasible && matching_certified && v ==
// matching_size)`. PROVES.
// ===========================================================================
#[trust_vc::ensures(result ==> (cover_feasible && matching_certified && value == matching_size))]
pub fn koenig_emit_optimum(
    cover_feasible: bool,
    matching_certified: bool,
    value: int,
    matching_size: int,
) -> bool {
    cover_feasible && matching_certified && value == matching_size
}

/// NON-VACUITY CONTROL — DROP THE UB FEASIBILITY RE-CHECK. Emits OPTIMUM without
/// re-verifying the cover against the ORIGINAL rows (`cover_feasible`). Then
/// `value` is not a valid upper bound on `tau` and could be below it (an infeasible
/// "cover" can be cheaper than any real cover). REFUTED (`cover_feasible = false`,
/// `matching_certified = true`, `value == matching_size`). Pins that the
/// `verify_all_constraints` UB re-check is LOAD-BEARING.
#[trust_vc::ensures(result ==> (cover_feasible && matching_certified && value == matching_size))]
pub fn koenig_emit_drop_feasible_check_wrong(
    cover_feasible: bool,
    matching_certified: bool,
    value: int,
    matching_size: int,
) -> bool {
    let _ = cover_feasible; // BUG: never re-verifies the cover is feasible
    matching_certified && value == matching_size
}

/// NON-VACUITY CONTROL — DROP THE LB MATCHING RE-CHECK. Emits OPTIMUM without the
/// `certified_matching_size` certificate (`matching_certified`). Then `|M|` is
/// unverified: a fabricated matching with overlapping / non-edge / wrongly-oriented
/// pairs could report a `matching_size` exceeding `tau`, so `value == matching_size`
/// no longer pins the optimum. REFUTED (`matching_certified = false`,
/// `cover_feasible = true`, `value == matching_size`). Pins that the matching
/// certificate `?` is LOAD-BEARING for the lower bound.
#[trust_vc::ensures(result ==> (cover_feasible && matching_certified && value == matching_size))]
pub fn koenig_emit_drop_matching_check_wrong(
    cover_feasible: bool,
    matching_certified: bool,
    value: int,
    matching_size: int,
) -> bool {
    let _ = matching_certified; // BUG: never re-certifies the matching lower bound
    cover_feasible && value == matching_size
}

/// NON-VACUITY CONTROL — DROP THE TIGHTNESS GATE. Emits OPTIMUM without requiring
/// `value == matching_size` (`|C| == |M|`). A non-tight pair (`|M| < |C|`) would
/// then be reported as optimal even though only `|M| <= tau <= |C|` is known.
/// REFUTED (`value != matching_size`, both re-checks holding). Pins that the
/// LB==UB tightness gate is LOAD-BEARING.
#[trust_vc::ensures(result ==> (cover_feasible && matching_certified && value == matching_size))]
pub fn koenig_emit_drop_tightness_wrong(
    cover_feasible: bool,
    matching_certified: bool,
    value: int,
    matching_size: int,
) -> bool {
    cover_feasible && matching_certified // BUG: drops `value == matching_size`
}

// ===========================================================================
// SOUNDNESS COROLLARY — König's bracket forces optimality. The genuine matching
// of disjoint real edges gives the LOWER bound `matching_size <= tau`; the feasible
// vertex cover gives the UPPER bound `tau <= value`; the tightness gate gives
// `value == matching_size`. Together these FORCE `tau == value`: the emitted value
// is the exact minimum vertex cover number. PROVES (pure ℤ arithmetic — this is the
// König max-matching == min-vertex-cover identity instantiated at the witnesses).
// ===========================================================================
#[trust_vc::ensures(
    (matching_size <= tau && tau <= value && value == matching_size) ==> (tau == value)
)]
pub fn koenig_bracket_forces_optimum(tau: int, matching_size: int, value: int) -> bool {
    matching_size <= tau && tau <= value && value == matching_size
}

/// NON-VACUITY CONTROL for the bracket — DROP THE LOWER-BOUND fact (no genuine
/// matching, so `matching_size <= tau` is not established). Then `value ==
/// matching_size` no longer pins `tau`: REFUTED (`tau > value`, e.g. a fabricated
/// matching larger than the true max matching). Pins that the matching LB witness
/// is what closes the bracket from below.
#[trust_vc::ensures(
    (tau <= value && value == matching_size) ==> (tau == value)
)]
pub fn koenig_bracket_drop_lower_wrong(tau: int, matching_size: int, value: int) -> bool {
    let _ = matching_size;
    tau <= value
}
