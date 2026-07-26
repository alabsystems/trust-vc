// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// =====================================================================
// NON-VACUOUS native-deductive proof that the in-production OPTIMIZATION
// INCUMBENT accept path (`sanitize_optimization_incumbent`,
// crates/ay-pb/src/portfolio.rs:5344-5362) ACCEPTS an incumbent ONLY WHEN
// (a) it re-verifies against the ORIGINAL constraints (the Verified
// Incumbent Gate, VIG) and (b) the stored objective is the EXACT recompute
// of that assignment — never a producer's unchecked claimed value. This is
// the VIG core the warmup flagged ("the OPTIMUM/incumbent accept path could
// store an objective without a feasibility check"). Discharged by trust-vc
// on the pure-Rust `ay` SMT solver, kernel-rechecked.
// =====================================================================
//
// THE ACCEPT CORE (verbatim real body, crates/ay-pb/src/portfolio.rs:5344-5362)
// ----------------------------------------------------------------------------
//   fn sanitize_optimization_incumbent(
//       assignment: &[bool],
//       claimed_objective: Option<i128>,
//       instance: &PbInstance,
//       objective: &PbObjective,
//   ) -> Option<(Vec<bool>, i128)> {
//       let assignment = normalize_assignment_width(assignment, instance.num_vars);
//       if !verify_all_constraints(&instance.constraints, &assignment) {
//           return None;
//       }
//
//       let actual_objective = eval_objective(objective, &assignment);
//       let objective = match claimed_objective {
//           Some(claimed) if claimed == actual_objective => claimed,
//           _ => actual_objective,
//       };
//
//       Some((assignment, objective))
//   }
//
// This is the single funnel every OPTIMUM/SATISFIABLE incumbent passes through:
// `finalize_optimum_verdict` (portfolio.rs:5409) and `sanitize_optimization_
// solution` (portfolio.rs:5445) both gate on it; `exact_optimization_incumbent`
// (bin/ay.rs:1808) likewise relies on the caller VIG, and the emission boundary
// re-checks `verify_all_constraints` again (bin/ay.rs:1891-1893). The accept
// DECISION is: return `Some` (ACCEPT) iff `verify_all_constraints` holds, and the
// stored objective is `actual_objective = eval_objective(objective, assignment)`
// regardless of the producer's `claimed_objective` — the `match` returns `claimed`
// ONLY in the arm GUARDED by `claimed == actual_objective`, so the stored value is
// the exact recompute in every arm.
//
// HOW THE TWO INPUTS ARE MODELED (the established per-step symbolic methodology)
// ----------------------------------------------------------------------------
// Exactly as `ay_refutation_step_realbody` models a constraint holding at a point
// by a SYMBOLIC relation `eval_a >= rhs_a` (not a call into the real fold), this
// fixture models:
//   * `feasible : bool` = the value of
//     `verify_all_constraints(&instance.constraints, &assignment)` — the VIG
//     decision. (That `verify_all_constraints` faithfully computes the AND over the
//     constraints is the SEPARATE, already-discharged proof
//     `ay_verify_all_constraints_realbody`.)
//   * `actual : i128` = the value of `eval_objective(objective, &assignment)`, the
//     exact recompute. On the i128-in-range path `eval_objective` (solver.rs:78)
//     returns EXACTLY `eval_objective_exact(objective, assignment)`: it first tries
//     `eval_objective_checked` = `checked_i128_to_i64(eval_objective_exact(..).ok()?)`
//     and `checked_i128_to_i64` is the identity `Some(value)` (solver.rs:207-209).
//     So `actual` IS `eval_objective_exact`'s value in the regime the incumbent
//     path operates in (the same checked/ℤ regime as the cutting-planes fixtures).
// Proving accept-soundness for ARBITRARY `feasible`/`actual` proves it for the real
// VIG result and real objective recompute in particular — and is exactly why the
// unsound controls below are REFUTED rather than vacuously accepted.
//
// THE SOUNDNESS PROPERTY (ACCEPT ⟹ feasible ∧ objective-exact)
// ------------------------------------------------------------
// Proven as its two halves, which JOINTLY are the accept-core soundness:
//   P1  ACCEPT ⟹ `feasible` (no incumbent accepted without the VIG re-check).
//   P2  on the accept path the stored objective == `actual` (the exact recompute;
//       never the unchecked claim).
// Each PROVES; each unsound control (drop the VIG check / trust the claim) is
// REFUTED with a concrete counterexample.
//
// (A single COMBINED statement over a composite return — e.g.
// `result == if feasible { Accept(actual) } else { Reject }` with
// `enum { Reject, Accept(i128) }`, or the struct/Option analogues — is currently
// blocked by an `ay` datatype-theory incompleteness: an `Ite` whose branch is a
// constructor carrying a NON-TRIVIAL (itself `Ite`) payload is not decided (it
// returns `Unknown`, NOT a false `Verified`, so this is fail-closed, never
// unsound). The two halves P1 ∧ P2 — each a decidable scalar/bool obligation —
// establish exactly the same property. See the deliverable note.)
//
// HOW VERIFIED: `trust_vc_core::verify_function_from_file(<this file>, <fn>)`.
// `Verified` == ay returned UNSAT and the kernel accepted the proof;
// `Counterexample` == ay returned a concrete falsifying model.

// ===========================================================================
// P1 — ACCEPT ⟹ FEASIBLE. Mirrors the early-return guard
// (portfolio.rs:5351-5353): `if !verify_all_constraints { return None }`.
// `result` is the ACCEPT bit (real: `Some` vs `None`); `feasible` is the VIG
// value. CONTRACT: an accepted incumbent satisfies the VIG. PROVES (the only
// value that yields `accept = true` is the one where `feasible` held).
// ===========================================================================
#[trust_vc::ensures(result ==> feasible)]
pub fn incumbent_accepted(feasible: bool) -> bool {
    if feasible {
        true // real: falls through to `Some((assignment, objective))`
    } else {
        false // real: `return None`
    }
}

/// NON-VACUITY CONTROL for P1 — accept WITHOUT the feasibility check (drops the
/// `if !verify_all_constraints { return None }` guard, the exact gap the warmup
/// flagged). `result` is unconditionally `true`, but `feasible` is arbitrary, so
/// `true ==> feasible` is FALSE: REFUTED (`feasible = false`). Pins that the
/// feasibility re-check is LOAD-BEARING for accept-soundness.
#[trust_vc::ensures(result ==> feasible)]
pub fn incumbent_accepted_no_check_wrong(feasible: bool) -> bool {
    let _ = feasible;
    true // BUG: accepts with no VIG re-check
}

// ===========================================================================
// P2 — STORED OBJECTIVE IS THE EXACT RECOMPUTE. Mirrors the objective
// selection (portfolio.rs:5355-5359):
//   actual = eval_objective(objective, assignment);
//   match claimed { Some(c) if c == actual => c, _ => actual }
// `result` is the stored objective; `actual` is the exact recompute; `claimed`
// (present iff `has_claim`) is the producer's value. CONTRACT: the stored value
// equals the exact recompute. PROVES — the `claimed` arm is GUARDED by
// `claimed == actual`, so both arms return `actual`; an unchecked claim is never
// stored.
// ===========================================================================
#[trust_vc::ensures(result == actual)]
pub fn incumbent_stored_objective(actual: i128, claimed: i128, has_claim: bool) -> i128 {
    if has_claim && claimed == actual {
        claimed
    } else {
        actual
    }
}

/// NON-VACUITY CONTROL for P2 — store the producer's `claimed` objective WITHOUT
/// the `claimed == actual` guard (trusts the claim blindly). The stored value can
/// then differ from the exact recompute: REFUTED (`has_claim = true`,
/// `claimed != actual`). Pins that the `claimed == actual_objective` re-check is
/// LOAD-BEARING — a mismatched objective (which could fabricate a false
/// `OptimumFound`) is never stored.
#[trust_vc::ensures(result == actual)]
pub fn incumbent_stored_objective_trust_claim_wrong(
    actual: i128,
    claimed: i128,
    has_claim: bool,
) -> i128 {
    if has_claim {
        claimed // BUG: stores the claim without `claimed == actual`
    } else {
        actual
    }
}

// ===========================================================================
// COMBINED (implication form) — ACCEPT ⟹ (feasible ∧ stored == exact recompute)
// as one decidable scalar statement. `result` is the stored objective; the
// `accept` event is `feasible` (P1: accept ⟺ feasible). On the accept path the
// stored value is the exact recompute. CONTRACT: `feasible ==> result == actual`.
// PROVES. Together with P1 this is the full "ACCEPT ⟹ feasible ∧ objective-exact".
// ===========================================================================
#[trust_vc::ensures(feasible ==> result == actual)]
pub fn incumbent_accept_objective_exact(
    feasible: bool,
    actual: i128,
    claimed: i128,
    has_claim: bool,
) -> i128 {
    if feasible {
        if has_claim && claimed == actual {
            claimed
        } else {
            actual
        }
    } else {
        actual // real: `return None` (no stored objective on the reject path)
    }
}

/// NON-VACUITY CONTROL for the COMBINED form — on the accept path stores the
/// unchecked `claimed` value. Then `feasible ==> result == actual` is FALSE:
/// REFUTED (`feasible = true`, `has_claim = true`, `claimed != actual`). Pins that
/// the accept path stores the exact recompute, not a producer's claim.
#[trust_vc::ensures(feasible ==> result == actual)]
pub fn incumbent_accept_objective_exact_wrong(
    feasible: bool,
    actual: i128,
    claimed: i128,
    has_claim: bool,
) -> i128 {
    let _ = has_claim;
    if feasible {
        claimed // BUG: stores the unchecked claim on the accept path
    } else {
        actual
    }
}
