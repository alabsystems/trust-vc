//! Verus builtin truncating `add`/`sub`/`mul` in Int-mode queries + type-range
//! invariants for `by(nonlinear_arith)` query variables (#2778, upstream
//! `nonlinear.rs` test5 / test6 / test4_fails / test_new_vars).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! ## What this locks
//!
//! Verus's `builtin::add/sub/mul` over a fixed-width operand type `uN`/`iN` is
//! the *truncating* operation: `mul(x, z) == (x * z) mod 2^N` (two's-complement
//! re-centered for `iN`), with **no** overflow obligation. Over `int`/`nat` the
//! same builtins are the exact mathematical operations. trust-vc lowers an
//! unregistered `add`/`sub`/`mul` call to `WrappingArith { mode: Wrapping }`
//! (fixed-width) or plain `Arith` (`int`/`nat`), and the Int-arithmetic
//! encoder applies the type-derived modular wrap even in `use_int_arithmetic`
//! mode (`by(nonlinear_arith)` / measure queries), where ordinary spec `+`/`*`
//! is unbounded math.
//!
//! Additionally, `by(nonlinear_arith)` queries re-sort every scalar variable as
//! `Int`; Verus injects each query variable's *type range invariant* as a query
//! hypothesis (`0 <= x < 2^N` for `uN`, two's-complement range for `iN`,
//! `0 <= x` for `nat`). Without the upper bounds, bounded-product goals
//! (upstream test5/test6) are unprovable over unconstrained Int variables.
//!
//! ## Soundness invariant
//!
//! Every "verifies" case is a true statement of the truncating semantics /
//! range invariants; every "must not verify" case is the exact unsound
//! strengthening that a NON-truncating (unbounded) encoding of the builtins
//! would wrongly prove (upstream `test4_fails` is Verus's own witness). If a
//! regression ever drops the wrap, the `*_must_not_verify` cases flip to
//! Verified and fail the suite. The bounded-product cases are decided
//! VERIFIED by the ay NIA stack (2026-07-01): the `#nia-zero-bound` family-4
//! box product upper cut (`0 <= x <= c1 ∧ 0 <= z <= c2 ⊢ x*z <= c1*c2`,
//! justified LRA bound reasons), reason-carrying McCormick envelopes, and
//! the QF_NIA check-sat-assuming split fallback; `test6`'s nested wrap
//! chains additionally need the trust-vc encoder's modular-congruence
//! pushdown (`wrapping.rs`).

use super::*;

fn nl() -> crate::vc::SolverMode {
    crate::vc::SolverMode::NonlinearArith
}

fn nat_ty() -> crate::ir::TrustVcType {
    crate::ir::TrustVcType::Nat
}

fn int_ty() -> crate::ir::TrustVcType {
    crate::ir::TrustVcType::MathInt
}

// ---------------------------------------------------------------------------
// Truncating semantics of the builtins themselves (concrete, decidable).
// ---------------------------------------------------------------------------

/// `mul(65536u32, 65536u32) == 0u32` — 2^16 * 2^16 = 2^32 ≡ 0 (mod 2^32).
/// The truncating builtin wraps; must verify in a nonlinear-arith query.
#[test]
fn nl_mul_u32_concrete_wraps_to_zero_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(
        ProofObligation::assert("wrap_mul", "mul(65536u32, 65536u32) == 0u32")
            .with_solver_mode(nl()),
    );
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 nonlinear.rs builtin mul: 2^16 * 2^16 truncates to 0 in u32",
    );
}

/// SOUNDNESS (should-FAIL direction): the *unbounded* reading of
/// `mul(65536u32, 65536u32)` (= 2^32) would prove `mul(...) >= 1u32`; the
/// truncating builtin yields 0, so this must NOT verify. A non-wrapping
/// encoding of the builtin would wrongly prove it (the bug upstream
/// `test4_fails` exists to catch).
#[test]
fn nl_mul_u32_concrete_unbounded_reading_must_not_verify() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(
        ProofObligation::assert("no_wrap_mul", "mul(65536u32, 65536u32) >= 1u32")
            .with_solver_mode(nl()),
    );
    expect_fail_closed(
        &AYEncoder::verify(&ctx),
        "#2778 nonlinear.rs builtin mul: unbounded 2^32 reading of the truncating mul",
    );
}

/// `add(4294967295u32, 1u32) == 0u32` — u32::MAX + 1 wraps to 0.
#[test]
fn nl_add_u32_concrete_wraps_at_max_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(
        ProofObligation::assert("wrap_add", "add(4294967295u32, 1u32) == 0u32")
            .with_solver_mode(nl()),
    );
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 nonlinear.rs builtin add: u32::MAX + 1 truncates to 0",
    );
}

/// SOUNDNESS (should-FAIL direction): the *unbounded* reading of
/// `add(4294967295u32, 1u32)` (= 2^32) would prove `add(...) >= 1u32`; the
/// truncating builtin yields 0, so this must NOT verify.
#[test]
fn nl_add_u32_concrete_unbounded_reading_must_not_verify() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(
        ProofObligation::assert("no_wrap_add", "add(4294967295u32, 1u32) >= 1u32")
            .with_solver_mode(nl()),
    );
    expect_fail_closed(
        &AYEncoder::verify(&ctx),
        "#2778 nonlinear.rs builtin add: unbounded reading of the truncating add",
    );
}

/// `sub(0u32, 1u32) == 4294967295u32` — unsigned underflow wraps to u32::MAX.
#[test]
fn nl_sub_u32_concrete_wraps_below_zero_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(
        ProofObligation::assert("wrap_sub", "sub(0u32, 1u32) == 4294967295u32")
            .with_solver_mode(nl()),
    );
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 nonlinear.rs builtin sub: 0 - 1 truncates to u32::MAX",
    );
}

/// Signed wrap: `add(2147483647i32, 1i32) == -2147483648i32` (i32::MAX + 1
/// re-centers to i32::MIN under two's-complement truncation).
#[test]
fn nl_add_i32_concrete_wraps_at_max_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(
        ProofObligation::assert("wrap_add_i32", "add(2147483647i32, 1i32) == -2147483648i32")
            .with_solver_mode(nl()),
    );
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 nonlinear.rs builtin add: i32::MAX + 1 truncates to i32::MIN",
    );
}

/// SOUNDNESS (should-FAIL direction): `add(2147483647i32, 1i32) > 0i32` must
/// NOT verify — the truncated result is negative. The unbounded reading
/// (2147483648 > 0) would wrongly prove it.
#[test]
fn nl_add_i32_concrete_positive_reading_must_not_verify() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(
        ProofObligation::assert("no_wrap_add_i32", "add(2147483647i32, 1i32) > 0i32")
            .with_solver_mode(nl()),
    );
    expect_fail_closed(
        &AYEncoder::verify(&ctx),
        "#2778 nonlinear.rs builtin add: signed truncation must keep i32::MAX + 1 negative",
    );
}

/// `int`/`nat` operands: the builtins are the exact mathematical operations
/// (no truncation — there is no width). Upstream `test_new_vars` inner block:
/// `let y: nat = mul(x as nat, 2); assert(y == 10)` with `x == 5`.
#[test]
fn nl_test_new_vars_nat_mul_exact_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", int_ty());
    // Function-level `requires x == 5` — discharges the scoped requires.
    ctx.push_obligation(ProofObligation::assume("fn_requires", "x == 5"));
    ctx.add_assert_by_with_solver_mode(
        "nl_query",
        "mul(x as nat, 2) == 10",
        vec![ProofObligation::requires("nl_query_requires_0", "x == 5")],
        Some(nl()),
    );
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 nonlinear.rs test_new_vars: mul over nat is exact math (5 * 2 == 10)",
    );
}

/// SOUNDNESS (should-FAIL direction) for the math-`mul` recognition: with
/// `x == 5` the goal `mul(x as nat, 2) == 11` is false and must not verify.
#[test]
fn nl_nat_mul_wrong_value_must_not_verify() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", int_ty());
    // Function-level `requires x == 5` — the scoped requires discharges, so
    // the failure is the goal itself (10 != 11), not the requires check.
    ctx.push_obligation(ProofObligation::assume("fn_requires", "x == 5"));
    ctx.add_assert_by_with_solver_mode(
        "nl_query",
        "mul(x as nat, 2) == 11",
        vec![ProofObligation::requires("nl_query_requires_0", "x == 5")],
        Some(nl()),
    );
    expect_fail_closed(
        &AYEncoder::verify(&ctx),
        "#2778 nonlinear.rs: exact nat mul must refute 5 * 2 == 11",
    );
}

// ---------------------------------------------------------------------------
// Upstream test5 / test4_fails: bounded vs unbounded `x * z == mul(x, z)`.
// ---------------------------------------------------------------------------

/// Upstream `test5` first query:
/// ```ignore
/// assert(x * z == mul(x, z)) by(nonlinear_arith)
///     requires x <= 0xffff, z <= 0xffff
/// { assert(0 <= x * z); assert(x * z <= 0xffff * 0xffff); }
/// ```
/// With the u32 range invariants (`0 <= x, z`) and the scoped requires, the
/// product stays below 2^32, so the truncating `mul` agrees with the
/// mathematical `x * z`. (The upstream block-body steps are pinned separately
/// by `nl_test5_block_product_nonneg_verifies` /
/// `nl_test5_block_product_upper_bound_verifies` below.)
///
/// Decided VERIFIED by the ay NIA stack: the `#nia-zero-bound` family-4 box
/// product upper cut bounds `x*z` by the constant box (justified LRA bound
/// reasons), the wrap purification then forces the mod quotient to 0, and the
/// QF_NIA check-sat-assuming split fallback lets the pipeline pursue the
/// integer splits the direct assumption route cannot. The unsound direction
/// stays pinned by `nl_test4_fails_unbounded_mul_must_not_verify`.
#[test]
fn nl_test5_bounded_mul_matches_builtin_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.declare_var_typed("z", u32_ty());
    // Function-level `requires x <= 0xffff, z <= 0xffff` (upstream test5) —
    // discharges the scoped requires of the nonlinear query.
    ctx.push_obligation(ProofObligation::assume("fn_requires_x", "x <= 0xffffu32"));
    ctx.push_obligation(ProofObligation::assume("fn_requires_z", "z <= 0xffffu32"));
    ctx.add_assert_by_with_solver_mode(
        "nl_query",
        "x * z == mul(x, z)",
        vec![
            ProofObligation::requires("nl_query_requires_0", "x <= 0xffffu32"),
            ProofObligation::requires("nl_query_requires_1", "z <= 0xffffu32"),
        ],
        Some(nl()),
    );
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 nonlinear.rs test5: bounded x * z equals the truncating mul(x, z)",
    );
}

/// Upstream `test4_fails` (SOUNDNESS, should-FAIL direction):
/// ```ignore
/// assert(x * z == (mul(x, z) as int)) by(nonlinear_arith); // FAILS
/// ```
/// With NO bounds the mathematical `x * z` exceeds 2^32 (e.g. x = z = 2^16)
/// while the truncating `mul` wraps — the equality is refutable and must
/// never verify. A non-truncating builtin encoding would wrongly prove it.
#[test]
fn nl_test4_fails_unbounded_mul_must_not_verify() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.declare_var_typed("z", u32_ty());
    ctx.add_assert_by_with_solver_mode("nl_query", "x * z == mul(x, z)", vec![], Some(nl()));
    expect_fail_closed(
        &AYEncoder::verify(&ctx),
        "#2778 nonlinear.rs test4_fails: unbounded x * z vs truncating mul(x, z)",
    );
}

// ---------------------------------------------------------------------------
// Upstream test6: polynomial identity + commutativity through the builtins.
// ---------------------------------------------------------------------------

/// Upstream `test6` first query:
/// `assert(add(mul(x, x), x) == mul(x, add(x, 1))) by(nonlinear_arith) requires x < 0xfff`.
///
/// Decided VERIFIED via the trust-vc modular-congruence pushdown
/// (`wrapping.rs`): the nested same-width truncating operands contribute only
/// their residue mod 2^32, so the goal reduces to ONE wrap over the plain
/// ring identity, which polynomial normalization decides — see
/// `nl_bounded_ring_identity_without_builtins_verifies` for the mod-free
/// contrast.
#[test]
fn nl_test6_builtin_poly_identity_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    // Function-level `requires x < 0xfff` (upstream test6).
    ctx.push_obligation(ProofObligation::assume("fn_requires", "x < 0xfffu32"));
    ctx.add_assert_by_with_solver_mode(
        "nl_query",
        "add(mul(x, x), x) == mul(x, add(x, 1u32))",
        vec![ProofObligation::requires(
            "nl_query_requires_0",
            "x < 0xfffu32",
        )],
        Some(nl()),
    );
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 nonlinear.rs test6: add(mul(x, x), x) == mul(x, add(x, 1)) for x < 0xfff",
    );
}

/// Upstream `test6` second query: `assert(mul(x, y) == mul(y, x)) by(nonlinear_arith)`
/// with NO requires — truncating mul commutes because the underlying product does.
#[test]
fn nl_test6_builtin_mul_commutes_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.declare_var_typed("y", u32_ty());
    ctx.add_assert_by_with_solver_mode("nl_query", "mul(x, y) == mul(y, x)", vec![], Some(nl()));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 nonlinear.rs test6: truncating mul commutes unconditionally",
    );
}

/// SOUNDNESS (should-FAIL direction) for test6's shape: dropping the bound
/// makes the identity refutable (wrap point differs between the two sides),
/// mirroring upstream `test_requires` (same goal, missing requires ⇒ FAILS).
#[test]
fn nl_test6_poly_identity_without_bound_must_not_verify() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", nat_ty());
    ctx.add_assert_by_with_solver_mode(
        "nl_query",
        "x * x + x == x * (x + 1) && x < 0xfff",
        vec![],
        Some(nl()),
    );
    expect_fail_closed(
        &AYEncoder::verify(&ctx),
        "#2778 nonlinear.rs test_requires: goal with dropped requires must not verify",
    );
}

// ---------------------------------------------------------------------------
// Type-range invariants for by-block query variables.
// ---------------------------------------------------------------------------

/// A `u32` query variable carries `x <= u32::MAX` in a nonlinear-arith query.
#[test]
fn nl_u32_range_upper_bound_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(
        ProofObligation::assert("u32_upper", "x <= 4294967295u32").with_solver_mode(nl()),
    );
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 by-block query var range: u32 variable is bounded by u32::MAX",
    );
}

/// SOUNDNESS (should-FAIL direction): the range invariant must be EXACT —
/// `x <= u32::MAX - 1` is refutable at `x == u32::MAX` and must not verify.
#[test]
fn nl_u32_range_tighter_bound_must_not_verify() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(
        ProofObligation::assert("u32_tight", "x <= 4294967294u32").with_solver_mode(nl()),
    );
    expect_fail_closed(
        &AYEncoder::verify(&ctx),
        "#2778 by-block query var range: u32 range must not be over-tightened",
    );
}

/// An `i32` query variable carries the two's-complement range invariant.
#[test]
fn nl_i32_range_bounds_verify() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(
        ProofObligation::assert("i32_range", "x >= -2147483648i32 && x <= 2147483647i32")
            .with_solver_mode(nl()),
    );
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 by-block query var range: i32 variable is in [i32::MIN, i32::MAX]",
    );
}

/// SOUNDNESS (should-FAIL direction): `x >= i32::MIN + 1` must not verify —
/// `x == i32::MIN` inhabits the type.
#[test]
fn nl_i32_range_tighter_lower_bound_must_not_verify() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", i32_ty());
    ctx.push_obligation(
        ProofObligation::assert("i32_tight", "x >= -2147483647i32").with_solver_mode(nl()),
    );
    expect_fail_closed(
        &AYEncoder::verify(&ctx),
        "#2778 by-block query var range: i32 range must not be over-tightened",
    );
}

/// A `nat` query variable carries `x >= 0` in a nonlinear-arith query.
#[test]
fn nl_nat_nonneg_invariant_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", nat_ty());
    ctx.push_obligation(ProofObligation::assert("nat_nonneg", "x >= 0").with_solver_mode(nl()));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 by-block query var range: nat variable is non-negative",
    );
}

/// SOUNDNESS (should-FAIL direction): `x >= 1` must not verify for `nat`
/// (zero inhabits the type).
#[test]
fn nl_nat_positive_must_not_verify() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", nat_ty());
    ctx.push_obligation(ProofObligation::assert("nat_pos", "x >= 1").with_solver_mode(nl()));
    expect_fail_closed(
        &AYEncoder::verify(&ctx),
        "#2778 by-block query var range: nat range must not be over-tightened",
    );
}

/// Upstream `test5` block body first step: `assert(0 <= x * z)` inside the
/// nonlinear query — needs the `u32` non-negativity range invariants on both
/// factors (product-sign reasoning over Int-sorted query variables).
#[test]
fn nl_test5_block_product_nonneg_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.declare_var_typed("z", u32_ty());
    ctx.push_obligation(
        ProofObligation::assert("prod_nonneg", "0u32 <= x * z").with_solver_mode(nl()),
    );
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 nonlinear.rs test5 block: 0 <= x * z from u32 range invariants",
    );
}

/// Contrast pin for the ay-gap cases below: the SAME `x < 0xfff` bound with
/// the plain ring identity (no builtins, hence no wrap `mod` terms) IS decided
/// — polynomial normalization proves `x*x + x == x*(x + 1)` outright. This
/// localizes the remaining test5/test6 incompleteness to the constant-box
/// product upper bound (`0 <= x <= c1 ∧ 0 <= z <= c2 ⊢ x*z <= c1*c2`) that the
/// wrap terms' range guards need, NOT to the truncating-builtin encoding.
#[test]
fn nl_bounded_ring_identity_without_builtins_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_bound", "x < 0xfffu32"));
    ctx.push_obligation(
        ProofObligation::assert("ring_identity", "x * x + x == x * (x + 1u32)")
            .with_solver_mode(nl()),
    );
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 nonlinear.rs: plain bounded ring identity decided by polynomial normalization",
    );
}

/// Upstream `test5` block body second step: `assert(x * z <= 0xffff * 0xffff)`
/// under the scoped requires — constant-box product upper bound.
///
/// Decided VERIFIED by the ay `#nia-zero-bound` family-4 box product upper
/// cut: every factor carries justified LRA bounds `0 <= x, z <= 0xffff`, so
/// the constant cut `x*z <= 0xffff*0xffff` joins the LIA constraint set with
/// the bounds' reason atoms as justification.
#[test]
fn nl_test5_block_product_upper_bound_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", u32_ty());
    ctx.declare_var_typed("z", u32_ty());
    ctx.push_obligation(ProofObligation::assume("x_bound", "x <= 0xffffu32"));
    ctx.push_obligation(ProofObligation::assume("z_bound", "z <= 0xffffu32"));
    ctx.push_obligation(
        ProofObligation::assert("prod_upper", "x * z <= 0xffffu32 * 0xffffu32")
            .with_solver_mode(nl()),
    );
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 nonlinear.rs test5 block: x * z <= 0xffff * 0xffff",
    );
}
