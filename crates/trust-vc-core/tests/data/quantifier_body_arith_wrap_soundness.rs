// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// FV-B regression fixture: QUANTIFIER-BODY ARITHMETIC WRAPPED *AND* SUPPRESSED
// ITS OVERFLOW OBLIGATION.
//
// THE HOLE THIS GUARDS. A quantifier body is SPEC code, and Verus types spec
// arithmetic on `uN`/`iN` as unbounded `int` — `u64 + u64 : int`, no modulus,
// no overflow. trust-vc instead wrapped the body mod 2^width
// (`encode_int_arith` / `encode_neg` took their wrap context from the
// expression's Rust type) while EVERY overflow obligation in those same
// functions is gated on `quantifier_depth == 0`, because a predicate emitted
// under a binder references the bound variable, which becomes free at the outer
// assertion scope (#2557). So the body got neither faithful semantics nor a
// check, in both directions at once:
//
//   * FALSE claims VERIFIED, because the wrap pulled an out-of-range result
//     back into range (`fv_*` below);
//   * TRUE claims were REFUTED, because the wrap manufactured a fake witness
//     (`pin_true_*` below).
//
// Both directions are load-bearing: a fix that only stopped wrapping the value
// but kept a modulus anywhere in the chain fails the `pin_true_*` cases, and a
// fix that declined ALL quantifier-body work fails `pin_wrapping_*`.
//
// Measured against the production CLI at the defective HEAD (06a22d96, cache
// off): every `fv_*` reported `verified` and every `pin_true_*` reported
// `counterexample`.

// ---------------------------------------------------------------------------
// FALSE (must NOT verify) — the wrap pulled an overflowing result back in range.

// `i == u64::MAX` gives `i + 1 == 2^64`, which is NOT `<= u64::MAX`.
#[trust_vc::ensures(forall(|i: u64| i + 1 <= 18446744073709551615u64))]
pub fn fv_u64_add_stays_under_max() {}

// `i == 0` gives `i - 1 == -1`, which is NOT `>= 0`. This one also pins the
// `simplify_unsigned_zero_compare` fold: "unsigned expr >= 0" was folded to
// `true` on the premise that the body was reduced mod 2^w, and that premise
// died with the wrap.
#[trust_vc::ensures(forall(|i: u64| i - 1 >= 0u64))]
pub fn fv_u64_sub_is_nonnegative() {}

// The same fold in its OTHER polarity: `unsigned expr < 0` was folded to
// `false`, so negating it verified. `i == 0` refutes.
#[trust_vc::ensures(forall(|i: u64| !(i - 1 < 0u64)))]
pub fn fv_u64_sub_negated_zero_compare() {}

// The `0 <= expr` spelling of the same fold.
#[trust_vc::ensures(forall(|i: u64| 0u64 <= i - 1))]
pub fn fv_u64_zero_le_sub() {}

// `i == i32::MIN` gives `i + 1`... no — `i == i32::MAX` gives `2147483648`,
// which is NOT `<= i32::MAX`. Signed width, same hole.
#[trust_vc::ensures(forall(|i: i32| i + 1 <= 2147483647i32))]
pub fn fv_i32_add_stays_under_max() {}

// NEGATION, not subtraction: `x == i8::MIN` gives `-x == 128`, and `-(-128)`
// wrapped back to `-128`. Guards `encode_neg`, a separate site from the
// `Add`/`Sub`/`Mul` arms.
#[trust_vc::ensures(forall(|x: i8| 0i8 - x <= 127i8))]
pub fn fv_i8_neg_stays_under_max() {}

// EXISTENTIAL direction: the wrap manufactured a witness. `x + 1 == -128`
// needs `x == 127` wrapping to `i8::MIN`; mathematically `x + 1` ranges over
// `-127 ..= 128`, so `-128` is unreachable.
#[trust_vc::ensures(exists(|x: i8| x + 1i8 == -128i8))]
pub fn fv_i8_exists_wrapped_witness() {}

// ---------------------------------------------------------------------------
// TRUE (must verify) — the SAME one-site change is the capability win. Each of
// these was WRONGLY REFUTED while the body wrapped.

// The canonical case: mathematically `i + 1 > i` for every `i`.
#[trust_vc::ensures(forall(|i: u64| i + 1 > i))]
pub fn pin_true_u64_increment_is_greater() {}

// Signed width, same shape.
#[trust_vc::ensures(forall(|i: i32| i + 1 > i))]
pub fn pin_true_i32_increment_is_greater() {}

// The honest bound the modulus was hiding: `u8::MAX + u8::MAX == 510`.
#[trust_vc::ensures(forall(|a: u8, b: u8| a + b <= 510))]
pub fn pin_true_u8_add_honest_bound() {}

// ---------------------------------------------------------------------------
// NARROWNESS PINS — the fix must not degenerate into "a quantifier body proves
// nothing" or "a quantifier body never wraps at all".

// An EXPLICIT `wrapping_*` op is DEFINED as finite-width truncation and must
// keep truncating under a binder. TRUE only under wrapping.
#[trust_vc::ensures(forall(|a: u64, b: u64| a.wrapping_add(b) <= 18446744073709551615u64))]
pub fn pin_wrapping_add_still_truncates() {}

// The other half of that pin: a claim that is FALSE under truncation must still
// be refuted, so the pin above cannot be satisfied by "wrapping_add is opaque".
// `a == u64::MAX, b == 1` truncates to `0`, which is not `>= 1`.
#[trust_vc::ensures(forall(|a: u64, b: u64| !(b >= 1u64) || a.wrapping_add(b) >= 1u64))]
pub fn fv_wrapping_add_not_treated_as_math() {}

// The `simplify_unsigned_zero_compare` fold must SURVIVE for subtraction-free
// operands — declining it everywhere would be the capability disaster.
// TRUE and must keep verifying.
#[trust_vc::ensures(forall(|j: u32| j + 1 >= 0u32))]
pub fn pin_zero_compare_fold_survives_for_add() {}

// A genuinely FALSE quantified claim over fixed-width arithmetic must STILL be
// refuted — the fix must not make everything provable. `i == 0` refutes.
#[trust_vc::ensures(forall(|i: u64| i * 2 > i))]
pub fn fv_control_false_claim_still_refuted() {}

// Reflexivity: the plainest true body must keep verifying.
#[trust_vc::ensures(forall(|i: u64| i == i))]
pub fn pin_reflexive_still_verifies() {}

// ---------------------------------------------------------------------------
// OUTSIDE a quantifier, machine semantics and its obligation are UNCHANGED.

// The overflow obligation must still fire: `a == 191` gives `291`, not a `u8`.
#[trust_vc::requires(a <= 200u8)]
#[trust_vc::ensures(true)]
pub fn fv_exec_add_overflow_still_caught(a: u8) -> u8 {
    a + 100u8
}

// ...and an in-range exec addition must still verify.
#[trust_vc::requires(a <= 100u8)]
#[trust_vc::ensures(true)]
pub fn pin_exec_add_in_range_still_verifies(a: u8) -> u8 {
    a + 100u8
}
