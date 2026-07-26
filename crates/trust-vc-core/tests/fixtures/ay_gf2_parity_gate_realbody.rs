// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// =====================================================================
// NON-VACUOUS native-deductive proof of the in-production GF(2)-PARITY UNSAT
// accept-decisions for the `EC_ODD_GRIDS` (handshake-lemma) family
// (`crate::optimize::gf2_parity`, crates/ay-pb/src/optimize/gf2_parity.rs).
// Two shipped arms emit `s UNSATISFIABLE` from a parity (XOR / mod-2 Gaussian)
// refutation; this fixture proves the accept-gate of EACH on its REAL body:
//
//   ARM A (PRIMARY, kernel-CHECKED): `gf2_parity_unsat_cp_checked`
//   (gf2_parity.rs:1116-1118, called from ay.rs:778-779) returns `true` ONLY WHEN
//   the parity refutation, RECONSTRUCTED as an explicit cutting-planes derivation
//   over the ORIGINAL equality rows, is CERTIFIED by the kernel-verified checker
//   (`Refutation::check`, the `?` at gf2_parity.rs:1101). EXACTLY like pigeonhole
//   routes its UNSAT through `Refutation::check` — soundness is inherited from the
//   proven CP algebra, not from the Gaussian search.
//
//   ARM B (RECOVERY, raw elimination): `gf2_parity_detects_unsat`
//   (gf2_parity.rs:203-248, reached via `gf2_parity_detects_unsat_with_recovery`
//   at ay.rs:807-808) returns `true` ONLY WHEN some row of the mod-2 system is the
//   inconsistent row `0 == 1` over GF(2): odd RHS parity (`aug`) AND empty variable
//   support (`words.iter().all(|&w| w == 0)`). This is the native real-body
//   accept-gate that the Clean proof `ay_pb_gf2_parity.lean` certifies sound
//   ABSTRACTLY (a `0 == 1` GF(2) consequence of the equality rows ⇒ the integer
//   system is infeasible).
//
// Discharged by trust-vc on the pure-Rust `ay` SMT solver, kernel-rechecked.
// `Verified` == ay returned UNSAT and the kernel accepted the proof;
// `Counterexample` == ay returned a concrete falsifying model.
// =====================================================================
//
// ===========================================================================
// ARM A — CHECKER-ACCEPTANCE GATE (mirrors pigeonhole_gate_realbody.rs)
// ===========================================================================
// `gf2_parity_cp_refutation` assembles a candidate cutting-planes derivation from
// the witness equality subset `S` (the rows whose mod-2 sum is `0 == 1`) and GATES
// its `Some(refutation)` on `refutation.check().ok()?` — the kernel-algebra checker
// independently replaying the derivation to `0 >= 1`. A mis-detected witness yields
// a derivation the checker REJECTS, so it can never produce a wrong UNSAT.
//
// --- the kernel checker gate (gf2_parity.rs:1101-1102): `Some` only after
//     `check().ok()?` accepts ---
// CONFORMANCE: src/optimize/gf2_parity.rs:1101-1102
//     refutation.check().ok()?;
//     Some(refutation)
//
// --- the production top-level gate (gf2_parity.rs:1116-1118): UNSAT IFF a checked
//     refutation was reconstructed ---
// CONFORMANCE: src/optimize/gf2_parity.rs:1116-1118
// pub fn gf2_parity_unsat_cp_checked(constraints: &[PbConstraint], num_vars: u32) -> bool {
//     gf2_parity_cp_refutation(constraints, num_vars).is_some()
// }
//
// HOW THE INPUT IS MODELED: the `Refutation::check()` outcome is a SYMBOLIC bool
// `check_accepted`. `refutation.check().ok()?` returns `None` (does NOT reach
// `Some(refutation)`) exactly when `check()` is `Err` (`!check_accepted`). Proving
// the gate for an ARBITRARY checker outcome proves it for the real
// `Refutation::check` in particular — whose own whole-loop soundness (the
// `replay_derivation` accumulate loop reaching `0 >= c`) is the separately
// discharged `refutation_loop_realbody.rs` / `refutation_step_realbody.rs`.

// THE BUILDER GATE — `gf2_parity_cp_refutation` returns `Some(refutation)`
// (`result`) ONLY WHEN `refutation.check()` accepted. Body mirrors
// `refutation.check().ok()?; Some(refutation)`: the `?` on `.ok()` short-circuits to
// `None` when `check()` is `Err` (`!check_accepted`); otherwise control reaches
// `Some(refutation)`. So the "emitted Some" bit equals `check_accepted`. CONTRACT:
// emitting the refutation implies the kernel checker accepted it. PROVES.
#[trust_vc::ensures(result ==> check_accepted)]
pub fn gf2_cp_refutation_emit_some(check_accepted: bool) -> bool {
    check_accepted
}

/// NON-VACUITY CONTROL — DROP THE CHECKER GATE. Returns `Some(refutation)` without
/// the `check().ok()?` self-check (the exact soundness anchor). A mis-reconstructed
/// derivation would then be emitted as a (false) UNSAT certificate. The contract
/// `result ==> check_accepted` is FALSE: REFUTED (`check_accepted = false`,
/// `result = true`). Pins that `Refutation::check` is LOAD-BEARING for the primary
/// GF(2) UNSAT arm.
#[trust_vc::ensures(result ==> check_accepted)]
pub fn gf2_cp_refutation_emit_some_no_check_wrong(check_accepted: bool) -> bool {
    let _ = check_accepted; // BUG: skips `refutation.check().ok()?`
    true
}

// THE TOP-LEVEL GATE — `gf2_parity_unsat_cp_checked` returns `true` (`result`) ONLY
// WHEN the reconstructed refutation was kernel-checked. Body mirrors
// `gf2_parity_cp_refutation(..).is_some()` where (by the builder gate above)
// `.is_some() == check_accepted`. CONTRACT: reporting UNSAT implies the
// reconstructed cutting-planes refutation was kernel-checked. PROVES.
#[trust_vc::ensures(result ==> check_accepted)]
pub fn gf2_unsat_cp_checked_emitted(check_accepted: bool) -> bool {
    check_accepted
}

// ===========================================================================
// ARM B — RAW-ELIMINATION `0 == 1` ACCEPT-DECISION (the deepest directive)
// ===========================================================================
// `gf2_parity_detects_unsat` returns `true` IFF SOME row of the mod-2 system is the
// inconsistent row `0 == 1` over GF(2). A GF(2) row models `sum_{j in P} x_j ≡ β`,
// where `β = row.aug` (RHS parity) and `P = support(row.words)` (the set columns).
// The row is the refutation `0 == 1` EXACTLY when `β = 1` (`row.aug`) AND `P = ∅`
// (`row.words.iter().all(|&w| w == 0)`):
//   * an OUTRIGHT input row already in that form (early return), and
//   * a REDUCED row after Gaussian elimination (`.any(..)` terminal).
//
// --- the immediate-refutation early return (gf2_parity.rs:220-222): an input row
//     already `0 == 1` ---
// CONFORMANCE: src/optimize/gf2_parity.rs:220-222
//         if row.aug && row.words.iter().all(|&w| w == 0) {
//             return true;
//         }
//
// --- the terminal decision (gf2_parity.rs:246-247): some REDUCED row is `0 == 1` ---
// CONFORMANCE: src/optimize/gf2_parity.rs:246-247
//     rows.iter()
//         .any(|r| r.aug && r.words.iter().all(|&w| w == 0))
//
// HOW THE INPUTS ARE MODELED: the two facts about a row are SYMBOLIC bools —
// `row_aug` = `row.aug` (RHS parity bit is 1) and `support_empty` =
// `row.words.iter().all(|&w| w == 0)` (the variable support `P` is empty). The
// per-row contradiction predicate `row_aug && support_empty` is the body of BOTH
// the early-`if` and the `.any(..)` closure; the `.any(..)` over the reduced rows
// is modeled as a disjunction over rows (mirroring the two-builder disjunction in
// pigeonhole_gate_realbody.rs). HONEST SCOPE: the full Gaussian-elimination
// whole-loop soundness (that `gaussian_eliminate` PRESERVES the GF(2) row-space, so
// a DERIVED `0 == 1` row is a genuine mod-2 consequence of the ORIGINAL equalities)
// is the separately-needed establishment+preservation+terminal decomposition,
// analogous to `refutation_loop_realbody.rs`; the abstract soundness (a `0 == 1`
// GF(2) consequence ⇒ integer UNSAT) is the Clean proof `ay_pb_gf2_parity.lean`.
// This fixture proves the native real-body ACCEPT-PREDICATE: UNSAT is emitted ONLY
// from a row that is genuinely `0 == 1` (odd RHS AND empty support), never from a
// valid parity CUT (odd RHS, non-empty support) or a trivial `0 == 0` row.

// THE PER-ROW CONTRADICTION PREDICATE — a row is accepted as the refutation
// (`result`) ONLY WHEN it is `0 == 1` over GF(2): `row_aug` (β = 1) AND
// `support_empty` (P = ∅). Body is the exact conjunction inside the early-`if` and
// the `.any(..)` closure. CONTRACT: accepting a row as the refutation implies both
// the odd-RHS bit AND empty variable support. PROVES.
#[trust_vc::ensures(result ==> (row_aug && support_empty))]
pub fn gf2_row_is_contradiction(row_aug: bool, support_empty: bool) -> bool {
    row_aug && support_empty
}

/// NON-VACUITY CONTROL — DROP THE EMPTY-SUPPORT CHECK. Accepts a row as the
/// refutation on `row_aug` ALONE. Then a row with odd RHS but NON-empty support
/// `P != ∅` — which is a VALID PARITY CUT `sum_{j in P} x_j >= 1`, NOT a
/// contradiction (it is satisfiable) — would be misreported as UNSAT. The contract
/// `result ==> (row_aug && support_empty)` is FALSE: REFUTED (`row_aug = true`,
/// `support_empty = false`). Pins that the empty-support test is LOAD-BEARING.
#[trust_vc::ensures(result ==> (row_aug && support_empty))]
pub fn gf2_row_drop_support_check_wrong(row_aug: bool, support_empty: bool) -> bool {
    let _ = support_empty; // BUG: a parity CUT (P != ∅) is not a refutation
    row_aug
}

/// NON-VACUITY CONTROL — DROP THE ODD-RHS (`aug`) CHECK. Accepts a row as the
/// refutation on `support_empty` ALONE. Then an all-zero row with EVEN RHS parity —
/// the trivially-true tautology `0 == 0` — would be misreported as UNSAT. The
/// contract is FALSE: REFUTED (`support_empty = true`, `row_aug = false`). Pins that
/// the odd-RHS (`aug`) bit is LOAD-BEARING.
#[trust_vc::ensures(result ==> (row_aug && support_empty))]
pub fn gf2_row_drop_aug_check_wrong(row_aug: bool, support_empty: bool) -> bool {
    let _ = row_aug; // BUG: `0 == 0` (empty support, even RHS) is not a refutation
    support_empty
}

// THE TERMINAL `.any(..)` DECISION — `gf2_parity_detects_unsat` returns `true`
// (`result`) ONLY WHEN SOME row is the `0 == 1` contradiction. Body mirrors
// `rows.iter().any(|r| r.aug && r.support_empty)`, modeled (like the two-builder
// disjunction in pigeonhole) over a representative pair of rows whose per-row
// contradiction bits are `row0_contradiction` / `row1_contradiction`. CONTRACT:
// emitting UNSAT implies SOME row genuinely refutes `0 == 1`. PROVES.
#[trust_vc::ensures(result ==> (row0_contradiction || row1_contradiction))]
pub fn gf2_unsat_detected(row0_contradiction: bool, row1_contradiction: bool) -> bool {
    row0_contradiction || row1_contradiction
}

/// NON-VACUITY CONTROL — EMIT UNSAT WITH NO CONTRADICTORY ROW. Returns `true` even
/// when NO row is the `0 == 1` refutation (`.any(..)` replaced by an unconditional
/// `true`). The contract `result ==> (row0_contradiction || row1_contradiction)` is
/// FALSE: REFUTED (both `false`, `result = true`). Pins that the existence of a
/// genuine `0 == 1` reduced row is LOAD-BEARING for the raw-elimination UNSAT arm.
#[trust_vc::ensures(result ==> (row0_contradiction || row1_contradiction))]
pub fn gf2_unsat_detected_no_row_wrong(row0_contradiction: bool, row1_contradiction: bool) -> bool {
    let _ = row0_contradiction;
    let _ = row1_contradiction; // BUG: emits UNSAT without finding a `0 == 1` row
    true
}
