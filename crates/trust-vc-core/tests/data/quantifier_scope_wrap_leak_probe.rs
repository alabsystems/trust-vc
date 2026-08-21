// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// FV-C regression fixture: the SCOPE-WIDE quantifier wrap context must not
// reduce `int`/`nat` arithmetic modulo the BINDER's bit width.
//
// THE HOLE THIS GUARDS: `arith_semantics::resolve_expr_wrap` resolved an
// operation's modulus as `expr_type.bit_width().or_else(|| scope_wrap)`.
// `TrustVcType::bit_width()` returns `None` for exactly `MathInt` and `Nat` —
// the two sorts that must NEVER wrap — so the `or_else` adopted the
// quantifier binder's width instead of declining. Because
// `QuantifierScope::wrap_semantics()` is scope-WIDE, every `+`/`-`/`*` in a
// quantifier body was silently reduced mod 2^(binder width), including
// arithmetic on `int` values and arithmetic that never mentions the binder.
//
// The direction of the lie is a proof hole, not over-rejection: a sum that
// genuinely exceeds the binder's range wraps back into it, so a FALSE bound
// reports `verified` — and it does so through `ensures`, which crosses module
// boundaries.

// ---------------------------------------------------------------------------
// FALSE (must NOT verify). a == b == 200 gives 400 > 255. The values are
// `int`, so no wrapping exists in the source at all.
#[trust_vc::ensures(forall(|a: u8, b: u8| (a as int) + (b as int) <= 255))]
pub fn fv_int_cast_sum_bound() {}

// FALSE (must NOT verify). No cast anywhere: the spec function's declared
// return type is already `int`, so the `+` is `int` arithmetic. 200+200 = 400.
#[trust_vc::spec]
pub fn two_hundred(_i: u8) -> int {
    200
}

#[trust_vc::ensures(forall(|i: u8| two_hundred(i) + two_hundred(i) < 256))]
pub fn fv_spec_fn_int_sum() {}

// FALSE (must NOT verify). The binder `i` is NEVER MENTIONED in the arithmetic
// — the multiplication is over the caller's `y`. Only a scope-wide modulus can
// make `400 < 256` true.
#[trust_vc::requires(y == 200)]
#[trust_vc::ensures(forall(|i: u8| (y as int) * 2 < 256))]
pub fn fv_binder_unused(y: u8) {
    let _ = y;
}

// FALSE (must NOT verify). Subtraction under an unsigned binder: 0 - 1 is -1
// as `int`, never 255.
#[trust_vc::ensures(forall(|a: u8, b: u8| (a as int) - (b as int) >= 0))]
pub fn fv_int_cast_diff_nonneg() {}

// CONTROL (must NOT verify, and already did not): a `nat` BINDER contributes
// no wrap, because `QuantifierScope::from_bound_vars` gates on the same
// `bit_width()`. This is the neighbour that proves the expression-side
// fall-through was the defect and not a design choice.
#[trust_vc::ensures(forall(|a: nat, b: nat| a + b <= 255))]
pub fn control_nat_binder_never_wrapped() {}

// ---------------------------------------------------------------------------
// NARROWNESS PINS — genuine FIXED-WIDTH arithmetic under a binder must STILL
// wrap, because that is correct Rust machine semantics. Each of these is TRUE
// and must keep verifying; a blanket "never wrap inside a quantifier" fix
// would break the first two.

// TRUE ONLY UNDER WRAPPING: `a + b` on `u8` operands is a `u8`, so the result
// is reduced mod 256 and can never exceed 255.
#[trust_vc::ensures(forall(|a: u8, b: u8| a + b <= 255))]
pub fn pin_u8_add_wraps_into_range() {}

// TRUE ONLY UNDER WRAPPING: same for `*`.
#[trust_vc::ensures(forall(|a: u8, b: u8| a * b <= 255))]
pub fn pin_u8_mul_wraps_into_range() {}

// TRUE MATHEMATICALLY: 255 + 255 == 510. This is the bound the defect's
// modulus was hiding, and it must verify once `int` arithmetic is faithful.
#[trust_vc::ensures(forall(|a: u8, b: u8| (a as int) + (b as int) <= 510))]
pub fn pin_int_cast_sum_true_bound() {}

// TRUE MATHEMATICALLY: both operands are non-negative.
#[trust_vc::ensures(forall(|a: u8, b: u8| (a as int) + (b as int) >= 0))]
pub fn pin_int_cast_sum_nonneg() {}

// TRUE MATHEMATICALLY: 255 * 255 == 65025.
#[trust_vc::ensures(forall(|a: u8, b: u8| (a as int) * (b as int) <= 65025))]
pub fn pin_int_cast_mul_true_bound() {}
