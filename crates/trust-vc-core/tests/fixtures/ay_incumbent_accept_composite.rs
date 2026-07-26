// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// =====================================================================
// NON-VACUOUS native-deductive proof of the in-production OPTIMIZATION
// INCUMBENT accept path stated as ONE contract over a COMPOSITE (struct)
// RETURN value — the decidable composite form. Companion to
// `ay_incumbent_vig_realbody.rs`, which proves the same accept-core soundness
// as the two scalar halves P1 (accept ⟹ feasible) and P2 (stored objective ==
// exact recompute). Here BOTH halves are discharged JOINTLY as a single
// `#[ensures]` over a struct return carrying (accept-bit, stored-objective).
// Discharged by trust-vc on the pure-Rust `ay` SMT solver, kernel-rechecked.
// =====================================================================
//
// WHY A *NEW* COMPOSITE FORM (and how it sidesteps the documented Unknown)
// ----------------------------------------------------------------------
// `ay_incumbent_vig_realbody.rs` notes that the naive composite statement
//   `result == if feasible { Accept(actual) } else { Reject }`
// over an `enum { Reject, Accept(i128) }` is BLOCKED by an `ay` datatype-theory
// incompleteness: an `Ite` whose branches are DIFFERENT constructors (or a
// constructor carrying an `Ite` payload) is returned as `Unknown` (fail-closed —
// never a false `Verified`). The form proven here AVOIDS that shape entirely:
//
//   * the return is a SINGLE-constructor struct `AcceptDecision { accepted,
//     value }` — there is no `Ite` over distinct constructors;
//   * both fields are bound STRAIGHT-LINE before the struct is built, so the one
//     constructor application carries only TRIVIAL (variable) payloads. The
//     objective's inner `claimed == actual` selection is a scalar `Int` `Ite`
//     (decidable), resolved into the `obj` binding before construction.
//
// So the composite obligation reduces to the struct's field selectors over
// trivial payloads — `result.accepted` and `result.value` — which the datatype
// UF layer decides. This is the durable pattern for stating multi-field
// accept-decision soundness as one composite contract.
//
// THE ACCEPT CORE (verbatim real body, crates/ay-pb/src/portfolio.rs:5344-5362)
// ----------------------------------------------------------------------------
//   fn sanitize_optimization_incumbent(
//       assignment: &[bool], claimed_objective: Option<i128>,
//       instance: &PbInstance, objective: &PbObjective,
//   ) -> Option<(Vec<bool>, i128)> {
//       let assignment = normalize_assignment_width(assignment, instance.num_vars);
//       if !verify_all_constraints(&instance.constraints, &assignment) {
//           return None;                                  // REJECT iff !feasible
//       }
//       let actual_objective = eval_objective(objective, &assignment);
//       let objective = match claimed_objective {
//           Some(claimed) if claimed == actual_objective => claimed,  // == actual
//           _ => actual_objective,                                     // == actual
//       };
//       Some((assignment, objective))                     // ACCEPT, stored == actual
//   }
//
// MODELING (same per-step symbolic methodology as ay_incumbent_vig_realbody):
//   * `feasible : bool` = value of `verify_all_constraints(..)` (the VIG decision)
//   * `actual : i128`   = value of `eval_objective(..)` (the exact recompute)
//   * `claimed`/`has_claim` = the producer's `Option<i128>` claim.
// `AcceptDecision.accepted` is the real `Some` vs `None`; `AcceptDecision.value`
// is the stored objective (meaningful only on the accept path).
//
// HOW VERIFIED: `trust_vc_core::verify_function_from_file(<this file>, <fn>)`.
// `Verified` == ay UNSAT + trust-vc-kernel accepted; `Counterexample` == ay
// returned a concrete falsifying model.

/// Composite accept decision: the accept bit and the stored objective, the two
/// observable outputs of `sanitize_optimization_incumbent`'s `Some`/`None`.
pub struct AcceptDecision {
    pub accepted: bool,
    pub value: i128,
}

// ===========================================================================
// COMBINED COMPOSITE CONTRACT — ACCEPT ⟹ (feasible ∧ stored == exact recompute),
// stated over the struct return in ONE `#[ensures]`:
//   * `result.accepted == feasible`         (P1: accept ⟺ the VIG decision)
//   * `result.accepted ==> result.value == actual`
//                                           (P2: on accept, stored == recompute)
// The objective is selected straight-line into `obj` (the `claimed == actual`
// guard, exactly as the real `match`), THEN the struct is built once with the
// trivial payloads `feasible` and `obj`. PROVES.
// ===========================================================================
#[trust_vc::ensures(
    result.accepted == feasible && (result.accepted ==> result.value == actual)
)]
pub fn incumbent_accept_composite(
    feasible: bool,
    actual: i128,
    claimed: i128,
    has_claim: bool,
) -> AcceptDecision {
    // Exact-recompute selection: store `claimed` ONLY in the arm guarded by
    // `claimed == actual`, else the recompute — so `obj == actual` either way.
    let obj = if has_claim && claimed == actual {
        claimed
    } else {
        actual
    };
    // Single constructor application, trivial (variable) payloads.
    AcceptDecision {
        accepted: feasible,
        value: obj,
    }
}

/// NON-VACUITY CONTROL — on the accept path stores the UNCHECKED `claimed`
/// objective (drops the `claimed == actual` guard, the exact gap a mismatched
/// producer value would exploit to fabricate a false `OptimumFound`). Then
/// `result.accepted ==> result.value == actual` is FALSE: REFUTED with a
/// concrete counterexample (`feasible = true`, `has_claim = true`,
/// `claimed != actual`). Pins that the `claimed == actual_objective` re-check is
/// LOAD-BEARING for the composite accept-decision soundness.
#[trust_vc::ensures(
    result.accepted == feasible && (result.accepted ==> result.value == actual)
)]
pub fn incumbent_accept_composite_wrong(
    feasible: bool,
    actual: i128,
    claimed: i128,
    has_claim: bool,
) -> AcceptDecision {
    let _ = has_claim;
    AcceptDecision {
        accepted: feasible,
        value: claimed, // BUG: stores the unchecked claim on the accept path
    }
}
