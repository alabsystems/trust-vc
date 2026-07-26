// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// =====================================================================
// NON-VACUOUS native-deductive proof that the in-production cutting-planes
// SATURATION step (`impliedGe_saturate`, refutation_check.rs:167-179) is
// ENTAILMENT-PRESERVING over 0/1 points — the rule the checker-proof
// `wo0h78ivd` explicitly left uncovered. Matches the kernel arrow
// `ay_certcut_saturation_sound` in proofs/clean-pb/PBCertificateAlgebra.lean.
// Discharged by trust-vc on the pure-Rust `ay` SMT solver, kernel-rechecked.
// =====================================================================
//
// THE RULE (verbatim real body, crates/ay-pb/src/proof/refutation_check.rs)
// -----------------------------------------------------------------------
// --- impliedGe_saturate (refutation_check.rs:167-179) ---
//   /// `impliedGe_saturate` (degree capping): for a constraint with every
//   /// coefficient `>= 0` and degree `rhs = b >= 0`, replacing each coefficient
//   /// `a_i` by `min(a_i, b)` preserves entailment over `0/1` variables (the
//   /// kernel's `cut_saturate_sound`). Returns `None` (fail-closed) on any other
//   /// shape — a negative coefficient or a negative degree — because the cap is
//   /// only sound under the kernel's `0 <= a_i`, `0 <= b` side conditions.
//   fn saturate(&self) -> Option<Self> {
//       if self.rhs < 0 {
//           return None;
//       }
//       let mut out = Self::constant(self.rhs);
//       for (&var, &c) in &self.coeff {
//           if c < 0 {
//               return None;
//           }
//           out.add_coeff(var, c.min(self.rhs))?;
//       }
//       Some(out)
//   }
//
// SOUNDNESS PROPERTY (what "entailment-preserving over 0/1" means here)
// --------------------------------------------------------------------
// Original constraint: `A := sum_i a_i x_i >= b`, with side conditions `a_i >= 0`
// (the `if c < 0 { return None }` guard, refutation_check.rs:173) and `b >= 0`
// (the `if self.rhs < 0 { return None }` guard, refutation_check.rs:168). The
// degree `b` is UNCHANGED (`Self::constant(self.rhs)`, refutation_check.rs:171).
// Saturated constraint: `S := sum_i min(a_i, b) x_i >= b`. The rule is sound iff
// at EVERY 0/1 point, `A >= b` implies `S >= b`.
//
// WHY THE PROOF IS DECOMPOSED THE WAY IT IS (the loop invariant)
// --------------------------------------------------------------
// The per-coefficient `c.min(self.rhs)` loop (refutation_check.rs:172-177) builds
// `S` one term at a time. Its soundness is the LOOP INVARIANT
//     INV(A_p, S_p) := (S_p >= b) OR (S_p == A_p)
// over the running prefix sums (A_p original, S_p saturated). This fixture proves
// the invariant's THREE decidable pieces — exactly the per-step arithmetic content
// the kernel `cut_saturate_sound` rests on, in the same per-step style as the
// add/scale/divide arrows in `ay_refutation_step_realbody`:
//   (1) `saturate_cap` — the per-coefficient `c.min(b)` op produces a value that is
//       `<= a`, `<= b`, and equal to one of `a`/`b` (the cap characterization).
//   (2) `saturate_invariant_step` — the INDUCTIVE STEP: appending one capped term
//       to a prefix satisfying INV keeps INV (the crux disjunction reasoning).
//   (3) `saturate_invariant_implies_sound` — INV(A,S) and `A >= b` give `S >= b`.
// Plus `saturate_single_term_sound`, the fully-concrete single-coefficient witness
// (the `S` from one term), and `saturate_term_contrib`, the per-term loop body
// (capped contribution at a 0/1 point) feeding piece (2).
//
// The reasoning is over `int` (Verus mathematical ℤ) for the same reason as
// `ay_refutation_step_realbody`: the i128 checker uses `checked_*`/`?`, so any
// overflowing step returns `None` (REJECTED); every ACCEPTED step's arithmetic is
// exact ℤ arithmetic. The `min` op is the VERBATIM `c.min(self.rhs)` method,
// lowered by the new `.min()`/`.max()`-on-integer capability built for this proof
// (an SMT `Int`-sort `Ite`: `a.min(b) = if a <= b { a } else { b }`).
//
// HOW VERIFIED: `trust_vc_core::verify_function_from_file(<this file>, <fn>)`.
// `Verified` == ay returned UNSAT and the trust-vc-kernel accepted the proof;
// `Counterexample` == ay returned a concrete falsifying model. The `*_wrong`
// controls (over-capping below the degree; dropping the per-term cap relation;
// over-claiming a stronger bound) are each REFUTED — the proofs are non-vacuous.

// ===========================================================================
// PIECE 1 — the per-coefficient cap `c.min(self.rhs)` (refutation_check.rs:176),
// VERBATIM via the new `.min()`-on-`int` capability (the SMT `Int`-sort `Ite`
// lowering `a.min(b) = if a <= b { a } else { b }` built for this proof). Under
// the rule's side conditions a >= 0, b >= 0, the capped coefficient is `<= a`
// (never increases a coefficient), `<= b` (the degree cap — coefficients above the
// degree carry no extra 0/1 propagation power), and equals exactly one of `a`/`b`.
// PROVES.
// ===========================================================================
#[trust_vc::requires(a >= 0 && b >= 0)]
#[trust_vc::ensures(result <= a && result <= b && (result == a || result == b))]
pub fn saturate_cap(a: int, b: int) -> int {
    a.min(b) // c.min(self.rhs)
}

/// NON-VACUITY CONTROL for PIECE 1 (over-cap) — caps at `b - 1`, one BELOW the
/// degree (`a.min(b - 1)`). The real rule caps at exactly `b` (`c.min(self.rhs)`).
/// Over-capping violates `result == a || result == b`: REFUTED (e.g. `a = b`,
/// where the result is `b - 1`, equal to neither `a` nor `b`). Over-capping a
/// coefficient below the degree can therefore never masquerade as `min(a, b)`.
#[trust_vc::requires(a >= 0 && b >= 0)]
#[trust_vc::ensures(result <= a && result <= b && (result == a || result == b))]
pub fn saturate_cap_overcap_wrong(a: int, b: int) -> int {
    a.min(b - 1) // BUG: caps at b-1, one below the degree b
}

// ===========================================================================
// PIECE 1b — the per-term loop body at a 0/1 point (refutation_check.rs:172-177
// fused with evaluation). A term with raw coefficient `a` contributes `min(a, b)`
// to the saturated sum when its variable is selected (x = 1) and `0` otherwise;
// its original contribution is `a` (selected) or `0`. The capped contribution is
// `>= 0`, `<= b`, and equals the term's ORIGINAL contribution OR `b` — exactly the
// per-term fact the inductive step (PIECE 2) consumes. PROVES.
// ===========================================================================
#[trust_vc::requires(a >= 0 && b >= 0)]
#[trust_vc::ensures(
    result >= 0
    && result <= b
    && (result == (if selected { a } else { 0 }) || result == b)
)]
pub fn saturate_term_contrib(a: int, b: int, selected: bool) -> int {
    let cap = a.min(b); // c.min(self.rhs)
    if selected {
        cap
    } else {
        0
    }
}

/// NON-VACUITY CONTROL for PIECE 1b (over-cap) — the per-term body that caps at
/// `b - 1`. The capped contribution of a selected term with `a >= b` becomes
/// `b - 1`, which is neither the original contribution `a` nor `b`: REFUTED
/// (`selected = true`, `a = b`). The dropped/over-aggressive cap is rejected.
#[trust_vc::requires(a >= 0 && b >= 0)]
#[trust_vc::ensures(
    result >= 0
    && result <= b
    && (result == (if selected { a } else { 0 }) || result == b)
)]
pub fn saturate_term_contrib_overcap_wrong(a: int, b: int, selected: bool) -> int {
    let cap = a.min(b - 1); // BUG: caps at b-1
    if selected {
        cap
    } else {
        0
    }
}

// ===========================================================================
// PIECE 2 — THE CRUX. Inductive step of the saturation loop invariant
//     INV(A, S) := (S >= b) OR (S == A).
// Appending one capped term to a prefix sum keeps INV. Operands: `a_sum`/`s_sum`
// are the running original/saturated prefix sums (INV holds), `o`/`s_term` the new
// term's original/capped contribution satisfying the PIECE-1b facts
// (`o >= 0`, `0 <= s_term <= b`, `s_term == o || s_term == b`). The new saturated
// sum `result = s_sum + s_term` and new original sum `a_sum + o` still satisfy INV.
// This is the entire soundness argument for the `c.min(self.rhs)` loop, decided by
// linear case analysis. PROVES.
// ===========================================================================
#[trust_vc::requires(
    b >= 0
    && s_sum >= 0
    && o >= 0
    && s_term >= 0
    && s_term <= b
    && (s_term == o || s_term == b)
    && ((s_sum >= b) || (s_sum == a_sum))
)]
#[trust_vc::ensures((result >= b) || (result == a_sum + o))]
pub fn saturate_invariant_step(a_sum: int, s_sum: int, o: int, s_term: int, b: int) -> int {
    s_sum + s_term
}

/// NON-VACUITY CONTROL for PIECE 2 — the SAME step body and contract but WITHOUT
/// the per-term cap relation `(s_term == o || s_term == b)` in the precondition
/// (it allows an arbitrary `0 <= s_term <= b`). This is the unsound regime where a
/// term may be over-capped (e.g. `s_term = 0` while `o` is large): the invariant
/// is NOT preserved, so it is REFUTED (`s_sum == a_sum == 0`, `o = b`, `s_term = 0`
/// gives `result = 0`, neither `>= b` (for `b >= 1`) nor `== a_sum + o = b`).
/// Shows the `s_term == o || s_term == b` cap relation is LOAD-BEARING.
#[trust_vc::requires(
    b >= 0
    && s_sum >= 0
    && o >= 0
    && s_term >= 0
    && s_term <= b
    && ((s_sum >= b) || (s_sum == a_sum))
)]
#[trust_vc::ensures((result >= b) || (result == a_sum + o))]
pub fn saturate_invariant_step_no_relation_wrong(
    a_sum: int,
    s_sum: int,
    o: int,
    s_term: int,
    b: int,
) -> int {
    s_sum + s_term
}

// ===========================================================================
// PIECE 3 — extracting soundness from the final invariant. After the loop,
// INV(A, S) holds for the FULL sums. If the original constraint holds (`A >= b`),
// then the saturated constraint holds (`S >= b`): if `S >= b` directly, done;
// otherwise `S == A >= b`. PROVES.
// ===========================================================================
#[trust_vc::requires(((s_sum >= b) || (s_sum == a_sum)) && a_sum >= b)]
#[trust_vc::ensures(result >= b)]
pub fn saturate_invariant_implies_sound(a_sum: int, s_sum: int, b: int) -> int {
    s_sum
}

/// NON-VACUITY CONTROL for PIECE 3 — claims the saturated sum meets a degree ONE
/// HIGHER than the rule preserves (`S >= b + 1`). Saturation preserves exactly the
/// degree `b` (the degree is UNCHANGED, refutation_check.rs:171), so a `b + 1`
/// claim is an over-strong (unsound) bound: REFUTED (`s_sum == a_sum == b`).
#[trust_vc::requires(((s_sum >= b) || (s_sum == a_sum)) && a_sum >= b)]
#[trust_vc::ensures(result >= b + 1)]
pub fn saturate_invariant_overclaim_wrong(a_sum: int, s_sum: int, b: int) -> int {
    s_sum
}

// ===========================================================================
// CONCRETE WITNESS — single-coefficient saturation soundness end-to-end. For a
// constraint with one term `a * x >= b` (`a >= 0`, `b >= 0`), the saturated
// `min(a, b) * x >= b` is implied at every 0/1 point: original contribution
// `o = if selected { a } else { 0 } >= b` implies saturated contribution
// `min(a, b) (selected) / 0 >= b`. The fully-decidable concrete instance of the
// rule (the analogue of `scale_step_by2_sound`). PROVES.
// ===========================================================================
#[trust_vc::requires(a >= 0 && b >= 0)]
#[trust_vc::ensures((if selected { a } else { 0 }) >= b ==> result >= b)]
pub fn saturate_single_term_sound(a: int, b: int, selected: bool) -> int {
    let cap = a.min(b); // c.min(self.rhs)
    if selected {
        cap
    } else {
        0
    }
}

/// NON-VACUITY CONTROL for the concrete witness (over-cap) — the single-term body
/// that caps at `b - 1`. Over-capping is UNSOUND end-to-end: a selected term with
/// `a = b` has original contribution `b >= b` (the constraint holds) but saturated
/// contribution `b - 1 < b` (the saturated constraint fails). REFUTED
/// (`selected = true`, `a = b = 1`: original `1 >= 1`, saturated `0 >= 1` false).
#[trust_vc::requires(a >= 0 && b >= 0)]
#[trust_vc::ensures((if selected { a } else { 0 }) >= b ==> result >= b)]
pub fn saturate_single_term_overcap_wrong(a: int, b: int, selected: bool) -> int {
    let cap = a.min(b - 1); // BUG: caps at b-1, below the degree
    if selected {
        cap
    } else {
        0
    }
}
