// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// =====================================================================
// NON-VACUOUS native-deductive proof that the SUBMISSION binary's DECISION-SAT
// VERDICT-EMISSION is SELF-CHECKED: the MAIN `ay` CLI
// (`crates/ay/src/cmd_pb.rs`, built `-p ay --bin ay --features cli`) emits
// `s SATISFIABLE` for a decision (`objective.is_none()`) instance ONLY WHEN the
// returned model RE-VERIFIES against the ORIGINAL `instance.constraints` with the
// proven `ay_pb::verify_all_constraints` (the DECISION-SAT Verified-SAT-Gate,
// VSG). This is the decision-track analogue of the OPTIMIZATION incumbent VIG
// (`sanitize_optimization_incumbent`, proven in `incumbent_vig_realbody.rs`):
// where the incumbent path re-verifies before ACCEPTING an incumbent, the
// decision path here re-verifies before EMITTING `s SATISFIABLE`.
//
// WHY THIS FIXTURE EXISTS. The core CDCL solver's model reaches
// `pb_cdcl_result_to_solution` and is mapped DIRECTLY to `PbStatus::Satisfiable`
// with NO re-check; the emission funnel in `run_solve` otherwise TRUSTED that
// model. This gate makes decision-SAT 0-wrong BY CONSTRUCTION — independent of
// any core-solver model bug — and the two PRIME DIRECTIVES it must satisfy are
// BOTH proven here:
//   (1) SOUNDNESS   — emit `s SATISFIABLE` ⟹ the model re-verified (fail-closed:
//       a non-verifying model is downgraded to UNKNOWN, never a wrong SAT);
//   (2) 0-REGRESSION — a model that DOES re-verify is ALWAYS still emitted SAT
//       (no false UNKNOWN on a valid model).
//
// Discharged by trust-vc on the pure-Rust `ay` SMT solver, kernel-rechecked.
// `Verified` == ay returned UNSAT and the kernel accepted the proof;
// `Counterexample` == ay returned a concrete falsifying model.
// =====================================================================
//
// THE GATE (verbatim real body, crates/ay/src/cmd_pb.rs)
// ------------------------------------------------------
// The decision-SAT self-check funnel. `Satisfiable` is downgraded to `Unknown`
// (via `unknown_solution()`) IFF `verify_all_constraints` over the ORIGINAL
// constraints FAILS; any other status (and a verifying SAT model) passes through
// UNCHANGED.
// CONFORMANCE: ../ay/src/cmd_pb.rs len=8
// fn decision_sat_self_checked(solution: PbSolution, instance: &PbInstance) -> PbSolution {
//     if solution.status == PbStatus::Satisfiable
//         && !ay_pb::verify_all_constraints(&instance.constraints, &solution.assignment)
//     {
//         return unknown_solution();
//     }
//     solution
// }
//
// THE EMIT FUNNEL (verbatim real body, crates/ay/src/cmd_pb.rs `run_solve`)
// ------------------------------------------------------------------------
// Every decision (`objective.is_none()`) SAT path — native, portfolio,
// frontend-timeout, and proof — funnels through this call BEFORE
// `write_result_or_best_known` emits the verdict, so the gate is load-bearing on
// the ACTUAL emission route. Optimization instances are skipped (their incumbent
// is already re-verified by the incumbent VIG), so there is no double-gate.
// CONFORMANCE: ../ay/src/cmd_pb.rs len=5
//     if let ParsedPbInstance::Opb(pb) = &instance {
//         if pb.objective.is_none() {
//             result.solution = decision_sat_self_checked(result.solution, pb);
//         }
//     }
//
// HOW THE INPUTS ARE MODELED (the established per-gate methodology, mirrored from
// `incumbent_vig_realbody.rs`). Exactly as the incumbent fixture models the VIG
// decision by a SYMBOLIC `feasible : bool` = the value of
// `verify_all_constraints(&instance.constraints, &assignment)`, this fixture
// models:
//   * `feasible : bool` = the value of
//     `ay_pb::verify_all_constraints(&instance.constraints, &solution.assignment)`
//     — the VSG re-check. (That `verify_all_constraints` faithfully computes the
//     AND over the constraints is the SEPARATE, already-discharged proof
//     `verify_all_constraints_realbody.rs`.)
//   * `was_sat : bool` = whether the incoming solution's status is
//     `PbStatus::Satisfiable` (the core solver's would-be SAT verdict, before the
//     gate). It routes into the guarded `if` exactly as the live
//     `solution.status == PbStatus::Satisfiable` conjunct does.
// The gate's OBSERVABLE OUTPUT is "the emitted status is `Satisfiable`" — a bool.
// The live gate returns `Satisfiable` IFF the input was `Satisfiable` AND
// `verify_all_constraints` held; otherwise it returns `unknown_solution()` (on the
// downgrade) or the unchanged non-SAT status (neither of which is an emitted
// `s SATISFIABLE`). Proving the obligations for ARBITRARY `was_sat`/`feasible`
// proves them for the real status/verify result in particular — which is why the
// unsound controls below are REFUTED rather than vacuously accepted.
//
// THE SOUNDNESS PROPERTY (the two PRIME DIRECTIVES, and their conjunction)
// -----------------------------------------------------------------------
//   P1  SOUNDNESS  : emit `s SATISFIABLE` ⟹ `feasible` (the model re-verified).
//   P2  0-REGRESSION: (`was_sat` ∧ `feasible`) ⟹ emit `s SATISFIABLE` (a
//       verifying model is NEVER turned into a false UNKNOWN).
//   COMBINED (biconditional): emit `s SATISFIABLE` ⟺ (`was_sat` ∧ `feasible`) —
//       the EXACT gate decision, jointly establishing P1 ∧ P2.
// Each PROVES; each unsound control (drop the VSG re-check / over-eagerly downgrade
// a verifying model) is REFUTED with a concrete counterexample.
//
// HOW VERIFIED: `trust_vc_core::verify_function_from_file(<this file>, <fn>)`.
// `Verified` == the soundness contract holds for all symbolic inputs;
// `Counterexample` == ay returned a concrete falsifying model (an unsound control).

// ===========================================================================
// P1 — SOUNDNESS: EMIT `s SATISFIABLE` ⟹ FEASIBLE. Models the gate's guarded
// downgrade `if status == Satisfiable && !verify_all_constraints { return
// unknown_solution() }` by the equivalent decision `if was_sat { feasible } else
// { false }` (== `was_sat && feasible`; the if/else-expression form the extractor
// decides, as in `incumbent_vig_realbody.rs`). `result` is the EMIT-AS-SATISFIABLE
// bit (real: whether the surviving status is `Satisfiable`); `was_sat` is the
// incoming `status == Satisfiable`; `feasible` is the VSG re-check value. CONTRACT:
// an emitted `s SATISFIABLE` implies the model re-verified. PROVES (the only branch
// that yields `result = true` is `was_sat` with `feasible` true).
// ===========================================================================
#[trust_vc::ensures(result ==> feasible)]
pub fn decision_sat_emit_implies_feasible(was_sat: bool, feasible: bool) -> bool {
    if was_sat {
        feasible // real: keep `Satisfiable` iff `verify_all_constraints` held (else downgrade to Unknown)
    } else {
        false // real: a non-`Satisfiable` status is never emitted as `s SATISFIABLE` by this gate
    }
}

/// NON-VACUITY CONTROL for P1 — emit `s SATISFIABLE` WITHOUT the re-check (drops
/// the `if status == Satisfiable && !verify_all_constraints { return
/// unknown_solution() }` guard, the exact gap the audit-plan flagged: the verdict
/// would TRUST the core solver's model). `result` is `was_sat` unconditionally, but
/// `feasible` is arbitrary, so `result ==> feasible` is FALSE: REFUTED
/// (`was_sat = true`, `feasible = false` — a buggy core-solver model reported SAT).
/// Pins that the `verify_all_constraints` re-check is LOAD-BEARING for soundness.
#[trust_vc::ensures(result ==> feasible)]
pub fn decision_sat_emit_implies_feasible_no_check_wrong(was_sat: bool, feasible: bool) -> bool {
    let _ = feasible; // BUG: emits SAT with no verify_all_constraints re-check
    was_sat
}

// ===========================================================================
// P2 — 0-REGRESSION: A FEASIBLE MODEL STAYS SATISFIABLE. The dual soundness
// direction (prime directive #1's "must NEVER turn a genuine SAT into UNKNOWN for
// a model that DOES verify"): when the incoming status was `Satisfiable` AND the
// model re-verifies, the gate MUST fall through and keep `Satisfiable` — it must
// not manufacture a false UNKNOWN. CONTRACT: (`was_sat` ∧ `feasible`) ⟹ emit
// `s SATISFIABLE`. PROVES (that input misses the downgrade `if`, so it falls
// through to `was_sat` = true).
// ===========================================================================
#[trust_vc::ensures((was_sat && feasible) ==> result)]
pub fn decision_sat_feasible_stays_satisfiable(was_sat: bool, feasible: bool) -> bool {
    if was_sat {
        feasible // real: a `Satisfiable` input keeps its status iff it re-verifies (downgrade ONLY on failure)
    } else {
        false
    }
}

/// NON-VACUITY CONTROL for P2 — an OVER-EAGER gate that downgrades EVERY model to
/// UNKNOWN (never emits SAT), including models that re-verify. This is the false-
/// UNKNOWN regression prime directive #1 forbids. The contract
/// `(was_sat && feasible) ==> result` is FALSE: REFUTED (`was_sat = true`,
/// `feasible = true`, `result = false`). Pins that the gate downgrades ONLY on a
/// FAILED re-check — a verifying SAT model is never lost (0 regression).
#[trust_vc::ensures((was_sat && feasible) ==> result)]
pub fn decision_sat_feasible_stays_satisfiable_overeager_wrong(
    was_sat: bool,
    feasible: bool,
) -> bool {
    let _ = was_sat;
    let _ = feasible; // BUG: downgrades EVERY model, even a verifying one (false UNKNOWN)
    false
}

// ===========================================================================
// COMBINED (biconditional) — EMIT `s SATISFIABLE` ⟺ (was_sat ∧ feasible). The
// EXACT decision of the gate, as one decidable scalar statement, jointly
// establishing P1 (⟸ contrapositive: not-feasible ⟹ not-emitted) and P2 (⟹). Body
// mirrors the live gate end-to-end: the guarded downgrade, then the unchanged
// status. CONTRACT: `result == (was_sat && feasible)`. PROVES. Together this is
// the full "decision-SAT is emitted IFF the model genuinely re-verifies".
// ===========================================================================
#[trust_vc::ensures(result == (was_sat && feasible))]
pub fn decision_sat_gate_decision(was_sat: bool, feasible: bool) -> bool {
    if was_sat {
        feasible // real: `Satisfiable` survives (`solution`) iff re-verified, else `unknown_solution()`
    } else {
        false // real: a non-`Satisfiable` status is passed through unchanged (never emitted as SAT)
    }
}

/// NON-VACUITY CONTROL for the COMBINED form — drop the re-check, so the emitted
/// status is `Satisfiable` whenever the core solver said `Satisfiable`, regardless
/// of `feasible`. Then `result == (was_sat && feasible)` is FALSE: REFUTED
/// (`was_sat = true`, `feasible = false` — a wrong `s SATISFIABLE` on a model that
/// violates a constraint). Pins that the re-check is load-bearing end-to-end: the
/// gate decision is `was_sat ∧ feasible`, not `was_sat` alone.
#[trust_vc::ensures(result == (was_sat && feasible))]
pub fn decision_sat_gate_decision_no_check_wrong(was_sat: bool, feasible: bool) -> bool {
    let _ = feasible; // BUG: no verify_all_constraints re-check — trusts the core model
    was_sat
}
