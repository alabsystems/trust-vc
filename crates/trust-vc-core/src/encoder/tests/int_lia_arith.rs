//! `int` unbounded signed-integer arithmetic in spec/proof contexts — pure LIA
//! over the backend `Int` sort with NO bit-width overflow obligation (#2778).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! ## What this locks
//!
//! Verus models `int` as the unbounded *signed* mathematical integers. Spec-mode
//! arithmetic over `int` (`+`, `-`, `*`) is therefore pure linear integer
//! arithmetic (LIA over the backend `Int` sort) carrying **no** fixed-width
//! overflow/underflow obligation — unlike exec-mode `iN`/`uN` `+`, which emits a
//! `bvadd_no_overflow`-style check. trust-vc encodes `int` on the backend `Int`
//! sort (`TrustVcType::MathInt`); because `MathInt::bit_width()` is `None`,
//! `resolve_expr_wrap` returns `None`, so `encode_int_arith` performs no modular
//! wrapping and collects no overflow predicate (see
//! `encoder/ir_encoder/arith/int_arith.rs` and `arith_semantics::resolve_expr_wrap`).
//!
//! `int` is the signed companion of the `nat` coverage in `nat_lia_arith.rs`:
//! whereas `nat` carries a per-variable `>= 0` assumption, `int` ranges over all
//! integers, so the *signed* / negative-witness directions below are only
//! expressible here. These pin that the resulting queries are decided soundly in
//! **both** directions by the ay solver — no MBQI, no fixed-width wrapping, and
//! crucially never a false `Verified` for a refutable spec assertion.
//!
//! ## Soundness invariant
//!
//! Every "verify" case is a true LIA validity; every "counterexample" case is a
//! true LIA refutation with a concrete (possibly negative) integer witness. None
//! depend on fixed-width wrapping, so they can never be confused with exec-mode
//! BV `+`/`-`/`*` semantics, and an overflow-free spec `+` can never be refuted
//! by a phantom overflow obligation.

use super::*;

fn int_ty() -> crate::ir::TrustVcType {
    crate::ir::TrustVcType::MathInt
}

/// `a: int ⊢ a + 1 > a`. Unbounded successor strictly increases for *every*
/// `int` (including the values where a fixed-width `iN` would overflow at MAX).
/// If a phantom overflow obligation leaked onto the spec `+`, this could fail;
/// it must verify.
#[test]
fn int_successor_strictly_increases_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("a", int_ty());
    ctx.push_obligation(ProofObligation::assert("succ", "a + 1 > a"));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 int LIA: a + 1 > a holds for all int (no fixed-width wrap, no overflow obligation)",
    );
}

/// `a: int ⊢ a - 1 < a`. Unbounded predecessor strictly decreases — there is no
/// lower wrap (unlike `uN` underflow at 0).
#[test]
fn int_predecessor_strictly_decreases_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("a", int_ty());
    ctx.push_obligation(ProofObligation::assert("pred", "a - 1 < a"));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 int LIA: a - 1 < a holds for all int (no fixed-width underflow obligation)",
    );
}

/// `a, b: int ⊢ a + b == b + a`. Commutativity of unbounded signed addition —
/// pure LIA, holds for all signed values including mixed-sign operands.
#[test]
fn int_addition_commutes_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("a", int_ty());
    ctx.declare_var_typed("b", int_ty());
    ctx.push_obligation(ProofObligation::assert("comm", "a + b == b + a"));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 int LIA: signed addition commutes for all int",
    );
}

/// `a, b: int ⊢ (a - b) + b == a`. Round-trip of unbounded signed subtraction;
/// holds unconditionally (no `a >= b` guard) because `int` subtraction is the
/// genuine signed difference, never a saturating/clamped operation.
#[test]
fn int_subtraction_roundtrip_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("a", int_ty());
    ctx.declare_var_typed("b", int_ty());
    ctx.push_obligation(ProofObligation::assert("roundtrip", "a - b + b == a"));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 int LIA: (a - b) + b == a for all signed int with no guard",
    );
}

/// `a, b: int, a < b ⊢ a < b + 1`. Distributing a strict bound across an
/// unbounded `+ 1` — a true LIA validity exercising the `+` lowering inside a
/// comparison. (`b + 1` carries no overflow obligation, so this never spuriously
/// fails.)
#[test]
fn int_strict_bound_plus_one_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("a", int_ty());
    ctx.declare_var_typed("b", int_ty());
    ctx.push_obligation(ProofObligation::assume("lt", "a < b"));
    ctx.push_obligation(ProofObligation::assert("succ_bound", "a < b + 1"));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 int LIA: a < b implies a < b + 1 (unbounded successor)",
    );
}

/// `a: int ⊢ a * 2 == a + a`. Multiplication by a constant against repeated
/// addition — linear, decided in pure LIA, and holds for negative `a` too.
#[test]
fn int_mul_by_const_equals_repeated_add_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("a", int_ty());
    ctx.push_obligation(ProofObligation::assert("double", "a * 2 == a + a"));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 int LIA: a * 2 == a + a for all signed int (no fixed-width mul-overflow obligation)",
    );
}

// ---------------------------------------------------------------------------
// Counterexample direction: signed witnesses that fixed-width `uN` cannot reach.
// ---------------------------------------------------------------------------

/// `a: int ⊢ a + 1 > 0` is **false**: the unbounded signed witness `a = -1`
/// refutes it (`a + 1 == 0`, not `> 0`), and `a = -5` makes it negative. A
/// `nat`/`uN` encoding could never expose this; only a genuine signed `int`
/// lowering produces the negative counterexample.
#[test]
fn int_successor_positivity_negative_witness_counterexample() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("a", int_ty());
    ctx.push_obligation(ProofObligation::assert("pos", "a + 1 > 0"));
    expect_counterexample(
        &AYEncoder::verify(&ctx),
        "#2778 int LIA: a + 1 > 0 is refuted by the signed witness a = -1 (a + 1 == 0)",
    );
}

/// `a: int ⊢ a * a >= a` **holds** for every integer: `a*a - a == a*(a-1)` is a
/// product of two consecutive integers, hence non-negative. The only place it
/// could fail is the open interval `0 < a < 1`, which contains no integer, so
/// there is no refuting witness over `int`. This pins that the spec `*` lowering
/// decides a (mildly nonlinear-shaped but ultimately constant-free) validity
/// correctly rather than spuriously refuting it.
#[test]
fn int_square_at_least_self_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("a", int_ty());
    ctx.push_obligation(ProofObligation::assert("sq", "a * a >= a"));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 int LIA: a*a >= a holds for all int (no integer strictly between 0 and 1)",
    );
}

/// `a, b: int, a == b + 2 ⊢ a == b + 4` is **false** — the unbounded equality
/// `a == b + 2` is incompatible with `a == b + 4`. This is the pure-`int`,
/// signed analogue of the overflow-distinguishing `test_overflow_spec_fails_*`
/// shape: because spec `+` is unbounded (no wrap), the only models are the true
/// ones, so ay refutes the wrong equality with a concrete witness rather than
/// returning `Unknown`.
#[test]
fn int_unbounded_add_wrong_equality_counterexample() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("a", int_ty());
    ctx.declare_var_typed("b", int_ty());
    ctx.push_obligation(ProofObligation::assume("def", "a == b + 2"));
    ctx.push_obligation(ProofObligation::assert("wrong", "a == b + 4"));
    expect_counterexample(
        &AYEncoder::verify(&ctx),
        "#2778 int LIA: a == b + 2 is incompatible with a == b + 4 (unbounded add, no wrap)",
    );
}

/// `a, b: int ⊢ a - b > 0` is **false**: the signed difference can be negative
/// or zero (witness `a = 0, b = 1` gives `-1`). Distinguishes genuine signed
/// subtraction from a clamped/saturating one.
#[test]
fn int_subtraction_can_be_nonpositive_counterexample() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("a", int_ty());
    ctx.declare_var_typed("b", int_ty());
    ctx.push_obligation(ProofObligation::assert("pos_diff", "a - b > 0"));
    expect_counterexample(
        &AYEncoder::verify(&ctx),
        "#2778 int LIA: a - b is signed and can be <= 0 (a = 0, b = 1 gives -1)",
    );
}

// ---------------------------------------------------------------------------
// Soundness anchor: spec `int` `+` must carry NO overflow obligation even with
// overflow checks globally enabled. A sum past i64::MAX is a *valid* unbounded
// `int` value; if a phantom `bvadd_no_overflow` obligation leaked it would be
// refuted and produce a FALSE counterexample for this valid assertion. It must
// verify, proving the LIA path suppresses the fixed-width obligation.
// ---------------------------------------------------------------------------

/// `a: int, a == 9223372036854775807 ⊢ a + 1 == 9223372036854775808`.
/// `9223372036854775807` is `i64::MAX`; over unbounded `int` the successor is
/// the representable value `2^63`. With `with_overflow_checks()` on, a leaked
/// fixed-width obligation would refute this; the spec LIA lowering must verify.
#[test]
fn int_add_past_i64_max_has_no_overflow_obligation_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("a", int_ty());
    ctx.push_obligation(ProofObligation::assume(
        "at_max",
        "a == 9223372036854775807",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "succ_past_max",
        "a + 1 == 9223372036854775808",
    ));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 int LIA: spec int `+` past i64::MAX carries no overflow obligation and verifies",
    );
}

// ---------------------------------------------------------------------------
// Cross-mode bridge: an exec signed source `as int` flows through the signed
// BV->Int coercion (`coerce_bv_term_to_int_for_type` -> `bv2int_signed`) into
// the LIA path. This is the broadly-reusable bit shared with calc.rs/arithmetic
// spec proofs that mix exec integers with ghost `int` arithmetic.
// ---------------------------------------------------------------------------

/// `s: i64 ⊢ (s as int) + 1 > s as int`. The signed source's `as int` image is
/// the genuine signed integer; unbounded `+ 1` strictly increases it for *every*
/// `i64` (including `i64::MAX`, where an exec `i64 + 1` would overflow). The
/// signed-direction companion of `nat_lia_arith::as_nat_unbounded_add_strictly_increases`.
#[test]
fn as_int_signed_source_unbounded_add_strictly_increases_verifies() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::Int { width: 64 });
    ctx.push_obligation(ProofObligation::assert("succ", "(s as int) + 1 > s as int"));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 int LIA: (s as int) + 1 > s as int for s: i64 — signed bv2int bridge, unbounded successor",
    );
}

/// `s: i64 ⊢ (s as int) >= 0` is **false** (witness `s = -1`), but refuting it
/// requires constructing a concrete model *through* the `bv2int_signed` bridge —
/// exactly the BV/Int model-construction limitation documented in
/// `nat_lia_arith::as_nat_unsigned_upper_bound_verifies` and
/// `overflow_spec_add::test_overflow_spec_fails_1`. The ay solver currently
/// returns `Unknown(incomplete)` here. That is the *sound* outcome: fail-closed,
/// never a false `Verified`. We pin the fail-closed boundary (not a
/// counterexample) so a future regression that flipped this to `Verified` —
/// which would unsoundly accept `(s as int) >= 0` for a signed source — fails.
/// The pure-`int` negative-witness direction *is* decided exactly; see
/// `int_subtraction_can_be_nonpositive_counterexample` above. The distinction is
/// the BV-source bridge, not the `int` LIA lowering.
#[test]
fn as_int_signed_source_nonneg_is_fail_closed() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_typed("s", crate::ir::TrustVcType::Int { width: 64 });
    ctx.push_obligation(ProofObligation::assert("nonneg", "(s as int) >= 0"));
    expect_fail_closed(
        &AYEncoder::verify(&ctx),
        "#2778 int LIA: (s as int) >= 0 for s: i64 must not verify — refutation via the signed \
         bv2int bridge is an ay model-construction limit, so fail-closed (Unknown) is the sound result",
    );
}
