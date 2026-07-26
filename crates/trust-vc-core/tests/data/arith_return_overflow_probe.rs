// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Adversarial (overflow/arithmetic): exec u64 MULTIPLICATION OVERFLOW in a
//! `return` expression is never checked.
//!
//! The value-position arithmetic-safety collector
//! `collect_value_position_arith_exprs` (body_extract.rs:14309) enumerates every
//! straight-line checked-arith site of a `let`/expr-statement and pins a reflexive
//! `(v) == (v)` obligation so the encoder fires the overflow precheck. It does NOT
//! have an arm for `Expr::Return` — that expression falls through to the final
//! `_ => {}` (body_extract.rs:14413). The return value is separately bound to
//! `result` only as an ASSUMPTION (`result == a * b`), and an assumption never
//! turns into an overflow GOAL — that is exactly why the `let b = a + 1; b`
//! regression (silent_drop_regressions.rs::test_returned_let_binding_overflow) had
//! to be caught by the let-INIT walker, not by the result binding. A bare
//! `return a * b;` has neither a let-init to instrument nor a walker arm, so the
//! multiplication-overflow obligation is dropped.

// TARGET (correct verdict: NOT Verified / Counterexample).
// `a * b` overflows u64 at the witness a = b = 4294967296 (2^32):
// 2^32 * 2^32 = 2^64, which is unrepresentable in u64 (wraps to 0). Rust panics in
// debug and Verus requires proving no overflow; there is no bound, so this is a
// genuine overflow. The return-position drop makes the engine accept it.
#[trust_vc::ensures(true)]
fn overflow_in_return(a: u64, b: u64) -> u64 {
    return a * b;
}

// POSITIVE CONTROL (correct verdict: Verified).
// The SAME multiplication in TAIL position — which the walker DOES instrument as a
// value-position site — bounded so it provably cannot overflow; the postcondition
// is genuinely true. Proves the arithmetic + contract machinery parses and a safe
// multiplication verifies (so the target's non-verify is not a parse failure).
#[trust_vc::requires(a < 1000u64)]
#[trust_vc::requires(b < 1000u64)]
#[trust_vc::ensures(result == a * b)]
fn bounded_mul_tail(a: u64, b: u64) -> u64 {
    a * b
}
