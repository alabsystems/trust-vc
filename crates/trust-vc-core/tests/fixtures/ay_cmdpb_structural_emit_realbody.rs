// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// =====================================================================
// NON-VACUOUS native-deductive proof that the SUBMISSION binary's structural-
// UNSAT VERDICT-EMISSION DISPATCH is SOUND. This lifts the per-recognizer gate
// proofs (`pigeonhole_gate_realbody.rs`, `gf2_parity_gate_realbody.rs`,
// `koenig_vc_gate_realbody.rs`, ...) up to the ACTUAL dispatch in the MAIN `ay`
// CLI — `crates/ay/src/cmd_pb.rs` `solve_opb` — which is the binary built for the
// PB competition (`-p ay --bin ay --features cli`). It proves the OR-composition
// of the recognizers AND the load-bearing emit-guard that gates `s UNSATISFIABLE`.
//
// Discharged by trust-vc on the pure-Rust `ay` SMT solver, kernel-rechecked.
// `Verified` == ay returned UNSAT and the kernel accepted the proof;
// `Counterexample` == ay returned a concrete falsifying model.
// =====================================================================
//
// THE DISPATCH (verbatim real bodies from crates/ay/src/cmd_pb.rs)
// ---------------------------------------------------------------
// In `solve_opb`, BEFORE the full-timeout native decision solve, the dispatch
// emits `s UNSATISFIABLE` via the structural route IFF the EMIT GUARD holds:
//   `objective.is_none() && proof.is_none() && structural_unsat_self_checked(..)`.
// `structural_unsat_self_checked` is a SHORT-CIRCUIT OR of the four self-checked
// recognizers, and `structural_unsat_outcome()` is the `PbStatus::Unsatisfiable`
// verdict the route returns.
//
// --- the EMIT GUARD (cmd_pb.rs:520-528): `s UNSATISFIABLE` via the structural
//     route ONLY WHEN `structural_unsat_self_checked` is true ---
// CONFORMANCE: ../ay/src/cmd_pb.rs len=9
//     if instance.objective.is_none() && proof.is_none() && structural_unsat_self_checked(instance) {
//         if std::env::var_os("AY_CERT_DEBUG").is_some() {
//             eprintln!(
//                 "c refutation self-checked EARLY: structural 0>=1 (kernel-algebra), \
//                  emitting s UNSATISFIABLE"
//             );
//         }
//         return Ok(structural_unsat_outcome());
//     }
//
// --- the OR-COMPOSITION (cmd_pb.rs:1869-1874): true ONLY WHEN at least one
//     self-checked recognizer accepted ---
// CONFORMANCE: ../ay/src/cmd_pb.rs len=6
// fn structural_unsat_self_checked(instance: &PbInstance) -> bool {
//     gf2_parity_unsat_cp_checked(&instance.constraints, instance.num_vars)
//         || matching_cardinality_unsat_cp_checked(&instance.constraints)
//         || pigeonhole_unsat_cp_checked(&instance.constraints)
//         || gf2_parity_detects_unsat_with_recovery(&instance.constraints, instance.num_vars)
// }
//
// --- the structural verdict (cmd_pb.rs:1878-1883): the route returns
//     `PbStatus::Unsatisfiable` (so EMIT-via-this-route == emit `s UNSATISFIABLE`) ---
// CONFORMANCE: ../ay/src/cmd_pb.rs len=6
// fn structural_unsat_outcome() -> PbSolveOutcome {
//     PbSolveOutcome::without_native_helpers(PbSolution {
//         status: PbStatus::Unsatisfiable,
//         assignment: Vec::new(),
//         objective: None,
//     })
// }
//
// HOW THE INPUTS ARE MODELED (the established per-gate methodology, mirrored from
// `pigeonhole_gate_realbody.rs` / `gf2_parity_gate_realbody.rs`): each recognizer's
// run-time result is a SYMBOLIC bool — `rec_gf2_cp`, `rec_matching`,
// `rec_pigeonhole`, `rec_gf2_recovery` — whose TRUTH MEANS "a kernel-algebra-checked
// cutting-planes / GF(2) refutation for THIS instance exists". That meaning is
// EXACTLY what the separately-discharged per-recognizer gate proofs establish:
// each recognizer returns `true` ONLY after `refutation.check().ok()?` (the
// kernel-algebra checker, whose own whole-loop soundness is
// `refutation_loop_realbody.rs` / `refutation_step_realbody.rs`) accepts. Proving
// the dispatch obligation for ARBITRARY symbolic recognizer outputs proves it for
// the real recognizer outputs in particular. The emit-guard's dispatch conditions
// `objective.is_none()` / `proof.is_none()` are likewise SYMBOLIC bools
// `objective_is_none` / `proof_is_none` (they route to this emission path; they are
// not soundness gates — the soundness gate is `structural_unsat_self_checked`).
//
// HOW VERIFIED: `trust_vc_core::verify_function_from_file(<this file>, <fn>)`.
// `Verified` == the soundness contract holds for all symbolic inputs;
// `Counterexample` == ay returned a concrete falsifying model (an unsound control).

// ===========================================================================
// (P1) OR-COMPOSITION — `structural_unsat_self_checked` returns `true` (`result`)
// ONLY WHEN at least one self-checked recognizer accepted. Body mirrors the live
// short-circuit OR `gf2_parity_unsat_cp_checked(..) || matching_cardinality_..(..)
// || pigeonhole_..(..) || gf2_parity_detects_unsat_with_recovery(..)`, with each
// disjunct modeled as the symbolic recognizer result. CONTRACT: a structural-UNSAT
// self-check implies SOME recognizer accepted (== a kernel-algebra-checked
// refutation exists). PROVES.
// ===========================================================================
#[trust_vc::ensures(result ==> (rec_gf2_cp || rec_matching || rec_pigeonhole || rec_gf2_recovery))]
pub fn structural_unsat_self_checked_emit(
    rec_gf2_cp: bool,
    rec_matching: bool,
    rec_pigeonhole: bool,
    rec_gf2_recovery: bool,
) -> bool {
    rec_gf2_cp || rec_matching || rec_pigeonhole || rec_gf2_recovery
}

/// NON-VACUITY CONTROL — OR RETURNS TRUE WITH NO RECOGNIZER. Reports a structural
/// self-check WITHOUT any recognizer accepting (the disjunction replaced by an
/// unconditional `true`). Then the dispatch would emit `s UNSATISFIABLE` with NO
/// kernel-algebra-checked refutation behind it. The contract `result ==> (some
/// rec_i)` is FALSE: REFUTED (all four recognizers `false`, `result = true`). Pins
/// that the OR-of-self-checked-recognizers is LOAD-BEARING.
#[trust_vc::ensures(result ==> (rec_gf2_cp || rec_matching || rec_pigeonhole || rec_gf2_recovery))]
pub fn structural_unsat_self_checked_no_rec_wrong(
    rec_gf2_cp: bool,
    rec_matching: bool,
    rec_pigeonhole: bool,
    rec_gf2_recovery: bool,
) -> bool {
    let _ = rec_gf2_cp;
    let _ = rec_matching;
    let _ = rec_pigeonhole;
    let _ = rec_gf2_recovery; // BUG: structural self-check with NO recognizer accepting
    true
}

// ===========================================================================
// (P2) EMIT GUARD LOAD-BEARING — the structural route emits its verdict
// (`result`) ONLY WHEN `structural_unsat_self_checked` (modeled `structural`) is
// true. Body mirrors the live `if objective.is_none() && proof.is_none() &&
// structural_unsat_self_checked(instance) { return Ok(structural_unsat_outcome()) }`
// guard. CONTRACT: taking the structural emit route implies the structural gate
// held. PROVES.
// ===========================================================================
#[trust_vc::ensures(result ==> structural)]
pub fn emit_unsat_guard(objective_is_none: bool, proof_is_none: bool, structural: bool) -> bool {
    objective_is_none && proof_is_none && structural
}

/// NON-VACUITY CONTROL — DROP THE STRUCTURAL GATE. Takes the emit route on the
/// dispatch conditions ALONE (`objective.is_none() && proof.is_none()`), DROPPING
/// `structural_unsat_self_checked`. Then ANY objective-free, proof-free decision
/// instance — including a SAT one — would be flipped to `s UNSATISFIABLE`. The
/// contract `result ==> structural` is FALSE: REFUTED (`structural = false`,
/// dispatch conditions `true`, `result = true`). Pins that
/// `structural_unsat_self_checked` is the LOAD-BEARING soundness gate.
#[trust_vc::ensures(result ==> structural)]
pub fn emit_unsat_guard_no_gate_wrong(
    objective_is_none: bool,
    proof_is_none: bool,
    structural: bool,
) -> bool {
    let _ = structural; // BUG: drops the structural_unsat_self_checked gate
    objective_is_none && proof_is_none
}

// ===========================================================================
// (COMBINED) EMIT-UNSAT ==> A CHECKED REFUTATION EXISTS. Composes P1 and P2 over
// the ACTUAL dispatch: `structural` is the OR of the four recognizers (P1), and the
// emit route is taken only when the guard's structural conjunct holds (P2). Body
// mirrors the live dispatch end-to-end. CONTRACT: emitting `s UNSATISFIABLE` via
// the structural route implies SOME recognizer accepted == a kernel-algebra-checked
// refutation exists ==> the instance is UNSAT. PROVES.
// ===========================================================================
#[trust_vc::ensures(result ==> (rec_gf2_cp || rec_matching || rec_pigeonhole || rec_gf2_recovery))]
pub fn emit_unsat_implies_checked_refutation(
    objective_is_none: bool,
    proof_is_none: bool,
    rec_gf2_cp: bool,
    rec_matching: bool,
    rec_pigeonhole: bool,
    rec_gf2_recovery: bool,
) -> bool {
    // structural_unsat_self_checked == OR of the four self-checked recognizers (P1)
    let structural = rec_gf2_cp || rec_matching || rec_pigeonhole || rec_gf2_recovery;
    // the emit guard: structural is load-bearing (P2)
    objective_is_none && proof_is_none && structural
}

/// NON-VACUITY CONTROL — DROP THE GATE IN THE COMBINED DISPATCH. Emits via the
/// structural route on the dispatch conditions ALONE, discarding all four
/// recognizers. The contract `result ==> (some rec_i)` is FALSE: REFUTED (all
/// recognizers `false`, dispatch conditions `true`, `result = true`). Pins that
/// the WHOLE structural gate (the OR of self-checked recognizers, threaded through
/// the emit guard) is load-bearing end-to-end on the actual cmd_pb.rs dispatch.
#[trust_vc::ensures(result ==> (rec_gf2_cp || rec_matching || rec_pigeonhole || rec_gf2_recovery))]
pub fn emit_unsat_no_gate_wrong(
    objective_is_none: bool,
    proof_is_none: bool,
    rec_gf2_cp: bool,
    rec_matching: bool,
    rec_pigeonhole: bool,
    rec_gf2_recovery: bool,
) -> bool {
    let _ = rec_gf2_cp;
    let _ = rec_matching;
    let _ = rec_pigeonhole;
    let _ = rec_gf2_recovery; // BUG: emit route taken with NO recognizer accepting
    objective_is_none && proof_is_none
}
