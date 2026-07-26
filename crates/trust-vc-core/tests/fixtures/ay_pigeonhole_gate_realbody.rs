// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// =====================================================================
// NON-VACUOUS native-deductive proof that the in-production PIGEONHOLE /
// HALL UNSAT detector (`crate::optimize::pigeonhole::pigeonhole_unsat_cp_checked`,
// crates/ay-pb/src/optimize/pigeonhole.rs:858-860) returns `true` (=> the
// caller may emit `s UNSATISFIABLE`) ONLY WHEN a constructed cutting-planes
// `Refutation` was CERTIFIED by the kernel-verified checker
// (`Refutation::check`) — never on the heuristic detector's say-so. Discharged
// by trust-vc on the pure-Rust `ay` SMT solver, kernel-rechecked.
// =====================================================================
//
// THE ACCEPT-DECISION (verbatim real bodies)
// ------------------------------------------
// `pigeonhole_unsat_cp_checked` returns `true` IFF at least one of the two
// builders returned `Some(refutation)`. Each builder ASSEMBLES a candidate
// cutting-planes derivation over the ORIGINAL rows (+ the `x_v >= 0` axiom) from a
// HEURISTIC structural analysis, then GATES its `Some` on
// `refutation.check().ok()?` — the kernel-algebra checker independently replaying
// the derivation to `0 >= c` (`c >= 1`). A mis-detected structure yields a
// derivation the checker REJECTS, so it can never produce a wrong UNSAT; soundness
// is inherited from `Refutation::check` (the proven `impliedGe_add` / `var_geq_zero`
// / `pb_unsat_of_contradictory_bounds` algebra), NOT from the detector.
//
// --- the top-level gate (pigeonhole.rs:858-860): true IFF some builder Some ---
// CONFORMANCE: src/optimize/pigeonhole.rs:858-860
// pub fn pigeonhole_unsat_cp_checked(constraints: &[PbConstraint]) -> bool {
//     pigeonhole_cp_refutation(constraints).is_some() || hall_cp_refutation(constraints).is_some()
// }
//
// --- the PURE builder's soundness gate (pigeonhole.rs:300-305): `Some` only
//     after `check().ok()?` accepts ---
// CONFORMANCE: src/optimize/pigeonhole.rs:300-305
//     let refutation = Refutation { inputs, steps };
//     // SOUNDNESS GATE: only return a refutation the kernel-algebra checker accepts
//     // as actually replaying to `0 >= c`, `c >= 1`. A mis-built candidate is
//     // rejected here and yields `None` (the normal engine then runs).
//     refutation.check().ok()?;
//     Some(refutation)
//
// --- the HALL builder's soundness gate (pigeonhole.rs:798-803): same `?` gate ---
// CONFORMANCE: src/optimize/pigeonhole.rs:798-803
//     let refutation = Refutation { inputs, steps };
//     // SOUNDNESS GATE: the kernel-algebra checker must independently certify that
//     // this derivation replays to `0 >= c` (c >= 1). A mis-proposed subset / wrong
//     // coupling is rejected here and yields `None` (the normal engine then runs).
//     refutation.check().ok()?;
//     Some(refutation)
//
// HOW THE INPUTS ARE MODELED (the established per-decision methodology): the
// `Refutation::check()` outcome is a SYMBOLIC bool — `check_accepted` for a single
// builder, `pure_check_accepted` / `hall_check_accepted` for the two-builder
// disjunction. `refutation.check().ok()?` returns `None` (does NOT reach
// `Some(refutation)`) exactly when `check()` is `Err` (i.e. `!check_accepted`).
// Proving the gate for an ARBITRARY checker outcome proves it for the real
// `Refutation::check` in particular — whose own whole-loop soundness (the
// `replay_derivation` accumulate loop reaching `0 >= c`) is the separately
// discharged `refutation_loop_realbody.rs` / `refutation_step_realbody.rs`.
//
// HOW VERIFIED: `trust_vc_core::verify_function_from_file(<this file>, <fn>)`.
// `Verified` == ay returned UNSAT and the kernel accepted the proof;
// `Counterexample` == ay returned a concrete falsifying model.

// ===========================================================================
// PER-BUILDER GATE — a builder returns `Some(refutation)` (`result`) ONLY WHEN
// `refutation.check()` accepted. Body mirrors `refutation.check().ok()?;
// Some(refutation)`: the `?` on `.ok()` short-circuits to `None` when `check()` is
// `Err` (`!check_accepted`); otherwise control reaches `Some(refutation)`. So the
// "emitted Some" bit equals `check_accepted`. CONTRACT: emitting the refutation
// implies the checker accepted it. PROVES.
// ===========================================================================
#[trust_vc::ensures(result ==> check_accepted)]
pub fn refutation_emit_some(check_accepted: bool) -> bool {
    check_accepted
}

/// NON-VACUITY CONTROL — DROP THE CHECKER GATE. Returns `Some(refutation)` without
/// the `check().ok()?` self-check (the exact soundness anchor). A mis-built
/// derivation would then be emitted as a (false) UNSAT certificate. The contract
/// `result ==> check_accepted` is FALSE: REFUTED (`check_accepted = false`,
/// `result = true`). Pins that `Refutation::check` is LOAD-BEARING for every
/// pigeonhole/Hall UNSAT.
#[trust_vc::ensures(result ==> check_accepted)]
pub fn refutation_emit_some_no_check_wrong(check_accepted: bool) -> bool {
    let _ = check_accepted; // BUG: skips `refutation.check().ok()?`
    true
}

// ===========================================================================
// TOP-LEVEL GATE — `pigeonhole_unsat_cp_checked` returns `true` (`result`) ONLY
// WHEN at least one builder's checker accepted. Body mirrors `pure.is_some() ||
// hall.is_some()` where (by the per-builder gate above) `pure.is_some() ==
// pure_check_accepted` and `hall.is_some() == hall_check_accepted`. CONTRACT:
// reporting UNSAT implies SOME constructed refutation was kernel-checked. PROVES.
// ===========================================================================
#[trust_vc::ensures(result ==> (pure_check_accepted || hall_check_accepted))]
pub fn pigeonhole_unsat_emitted(pure_check_accepted: bool, hall_check_accepted: bool) -> bool {
    pure_check_accepted || hall_check_accepted
}

/// NON-VACUITY CONTROL — the PURE builder returns `Some` WITHOUT its checker gate,
/// so the disjunction `pure.is_some() || hall.is_some()` is `true` even when
/// NEITHER refutation was certified. The contract `result ==> (pure_check_accepted
/// || hall_check_accepted)` is FALSE: REFUTED (both checks `false`, `result =
/// true`). Pins that EACH builder's `check().ok()?` is load-bearing — dropping
/// either one fabricates UNSAT.
#[trust_vc::ensures(result ==> (pure_check_accepted || hall_check_accepted))]
pub fn pigeonhole_unsat_emitted_pure_no_check_wrong(
    pure_check_accepted: bool,
    hall_check_accepted: bool,
) -> bool {
    let _ = pure_check_accepted; // BUG: pure builder emits Some with no check().ok()?
    true || hall_check_accepted
}
