// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// =====================================================================
// NON-VACUOUS native-deductive verification of the C3-1 SYMMETRY-
// CONVENTION-CONSISTENCY invariant — the bug fixed in symmetry.rs:468
// (`permutation_lex_leader_constraint`) — discharged by trust-vc on the
// pure-Rust `ay` SMT solver (i128 => BV128).
// =====================================================================
//
// THE C3-1 BUG (symmetry.rs): the always-on single-variable interchangeability
// chain `lex_ge_constraint(hi, lo)` emits the KEEP-MAX row `+1 x_hi - 1 x_lo >=
// 0` (smaller-index variable kept maximal: x_hi >= x_lo), while the scalable
// `permutation_lex_leader_constraint` originally emitted the opposite KEEP-MIN
// convention `binval(sigma(x)) >= binval(x)`. On a shared interchangeable pair
// the two opposite rows force `x_hi == x_lo`, deleting the whole orbit and
// turning a SAT instance into a FALSE UNSAT the model-only Verified Incumbent
// Gate cannot catch. The fix flipped the scalable emitter to KEEP-MAX so both
// agree.
//
// WHAT THESE LEMMAS PROVE (the focused coefficient-pattern invariant the two
// emitters produce for a transposition `(hi, lo)`, hi < lo). For the scalable
// emitter over the 2-element support `[hi, lo]` (k = 2, weights `w_hi = 2^(k-1)`,
// `w_lo = 2^(k-2)`, strictly decreasing powers of two so `w_hi > w_lo >= 1`):
//   * KEEP-MAX (the fix): coeff[hi] = w_hi - w_lo (> 0), coeff[lo] = w_lo - w_hi
//     (< 0) — same SIGN pattern as the chain's (+1, -1).
//   * KEEP-MIN (the bug): the signs are flipped.
// The orbit representative `(x_hi = 1, x_lo = 0)` is the lex-leader the rows must
// KEEP. The lemmas assert it satisfies BOTH rows under keep-max, and the
// convention-agreement form asserts the scalable coeff on the smaller index is
// positive (matches the chain). The KEEP-MIN controls flip the sign and MUST be
// refuted — the i128/BV128 counterexample is the exact orbit-deleting witness.
//
// NON-VACUOUS only because trust-vc encodes i128 as BV128: the `requires`
// `w_hi > w_lo >= 1` constrains the (symbolic) power-of-two weights, and the
// keep-min control's `w_lo - w_hi` is genuinely negative there — a real BV128
// fact, not a type-erased-Int tautology.

// CORRECT (keep-max): the orbit representative (x_hi = 1, x_lo = 0) satisfies
// BOTH the single-variable chain row AND the scalable transposition row, so the
// orbit keeps a representative (no false UNSAT). PROVES.
#[trust_vc::requires(w_hi > w_lo)]
#[trust_vc::requires(w_lo >= 1)]
#[trust_vc::ensures(result == true)]
pub fn c3_1_keepmax_keeps_orbit_representative(w_hi: i128, w_lo: i128) -> bool {
    // single-variable chain `lex_ge_constraint(hi, lo)`: +1 x_hi -1 x_lo >= 0.
    let chain_hi: i128 = 1;
    let chain_lo: i128 = -1;
    // scalable transposition lex row (KEEP-MAX): coeff[hi] = w_hi - w_lo,
    // coeff[lo] = w_lo - w_hi.
    let scal_hi: i128 = w_hi - w_lo;
    let scal_lo: i128 = w_lo - w_hi;
    // Evaluate each row's LHS at the lex-leader representative (x_hi = 1, x_lo = 0).
    let chain_lhs: i128 = chain_hi * 1 + chain_lo * 0;
    let scal_lhs: i128 = scal_hi * 1 + scal_lo * 0;
    chain_lhs >= 0 && scal_lhs >= 0
}

// WRONG (keep-min, the pre-fix C3-1 bug): the scalable row sign is flipped, so
// the representative (1, 0) VIOLATES it; combined with the chain forbidding
// (0, 1) the orbit is deleted. The `result == true` claim is therefore FALSE —
// MUST be refuted with a concrete (w_hi, w_lo) counterexample.
#[trust_vc::requires(w_hi > w_lo)]
#[trust_vc::requires(w_lo >= 1)]
#[trust_vc::ensures(result == true)]
pub fn c3_1_keepmin_keeps_orbit_representative(w_hi: i128, w_lo: i128) -> bool {
    let chain_hi: i128 = 1;
    let chain_lo: i128 = -1;
    // BUG (KEEP-MIN): signs flipped relative to the chain.
    let scal_hi: i128 = w_lo - w_hi;
    let scal_lo: i128 = w_hi - w_lo;
    let chain_lhs: i128 = chain_hi * 1 + chain_lo * 0;
    let scal_lhs: i128 = scal_hi * 1 + scal_lo * 0;
    chain_lhs >= 0 && scal_lhs >= 0
}

// CORRECT (convention agreement): the scalable transposition coefficient on the
// SMALLER-index variable is POSITIVE — the same sign as the chain's `+1`, so the
// two emitters impose the SAME keep-max ordering on the shared pair. PROVES.
#[trust_vc::requires(w_hi > w_lo)]
#[trust_vc::requires(w_lo >= 1)]
#[trust_vc::ensures(result == true)]
pub fn c3_1_keepmax_conventions_agree(w_hi: i128, w_lo: i128) -> bool {
    let scal_hi: i128 = w_hi - w_lo;
    scal_hi > 0
}

// WRONG (keep-min convention): the scalable coeff on the smaller index is
// NEGATIVE (keep-min), the OPPOSITE of the chain's `+1` — the exact C3-1 clash.
// The `result == true` claim is FALSE — MUST be refuted.
#[trust_vc::requires(w_hi > w_lo)]
#[trust_vc::requires(w_lo >= 1)]
#[trust_vc::ensures(result == true)]
pub fn c3_1_keepmin_conventions_agree(w_hi: i128, w_lo: i128) -> bool {
    let scal_hi: i128 = w_lo - w_hi;
    scal_hi > 0
}
