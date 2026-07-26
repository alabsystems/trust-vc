//! `nat` / `as nat` unbounded non-negative integer arithmetic in spec/proof
//! contexts — pure LIA over Int with a `>= 0` side-condition (#2778).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! ## What this locks
//!
//! Verus models `nat` as the unbounded non-negative mathematical integers, and
//! `x as nat` (for an unsigned source `x: u_`) as the non-negative integer image
//! of `x`. Arithmetic over `nat` is therefore *pure linear integer arithmetic*
//! (LIA over `Int`) with a single `>= 0` side-condition per `nat`-typed term —
//! crucially **not** fixed-width modular arithmetic. This is the exact pivot of
//! upstream `overflow.rs::test_overflow_spec_fails_1/2`: an unbounded `a as nat
//! + 2` must be distinguished from a wrapping fixed-width `add(a, 2)`.
//!
//! trust-vc encodes `nat` on the backend `Int` sort (`TrustVcType::Nat`,
//! `SortMeta::MathInt`) and emits the non-negativity assumption `x >= 0` for
//! every `nat`-typed variable (`static_extraction.rs`). These tests pin that the
//! resulting queries are decided *soundly in both directions* by the ay solver
//! with no MBQI and no fixed-width wrapping:
//!
//! * unbounded successor / monotonicity / transitivity **verify**;
//! * the `nat` non-negativity side-condition **verifies** `n >= 0`;
//! * `nat` subtraction is `int`-typed (Verus `SpecSub` output type is `int`),
//!   so an unguarded `n - m >= 0` is **refuted** (counterexample), and the
//!   round-trip `(m - n) + n == m` **verifies** with no `m >= n` guard;
//! * a wrong unbounded equality (`j == a + 2` but asserting `j == a + 4`) is
//!   **refuted** — the same overflow-distinguishing shape as `_fails_1/2` but in
//!   pure `nat` LIA, where ay decides it exactly.
//!
//! ## Soundness invariant
//!
//! Every "verify" case below is a true LIA validity; every "counterexample" case
//! is a true LIA refutation with a concrete witness. None rely on fixed-width
//! wrapping, so they can never be confused with the BV `add` semantics. The
//! distinct (currently fail-closed) BV-source `as nat` query lives in
//! `overflow_spec_add.rs`; see that module's notes for why the mixed BV/Int
//! refutation stays `Unknown` rather than producing a counterexample.

use super::*;

fn nat_ty() -> crate::ir::TrustVcType {
    crate::ir::TrustVcType::Nat
}

/// `n: nat ⊢ n + 1 > n`. Unbounded successor strictly increases — there is no
/// upper wrap, so this holds for *every* `nat` (unlike a fixed-width `u_`).
#[test]
fn nat_successor_strictly_increases_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", nat_ty());
    ctx.push_obligation(ProofObligation::assert("succ", "n + 1 > n"));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 nat LIA: n + 1 > n holds for all nat (no fixed-width wrap)",
    );
}

/// `n: nat ⊢ n >= 0`. The `nat` non-negativity side-condition is discharged by
/// the encoder's per-variable `>= 0` assumption.
#[test]
fn nat_nonnegativity_side_condition_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", nat_ty());
    ctx.push_obligation(ProofObligation::assert("nonneg", "n >= 0"));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 nat LIA: the nat >= 0 side-condition is assumed",
    );
}

/// `a < b, b < c ⊢ a < c` over `nat`. Pure LIA transitivity.
#[test]
fn nat_strict_order_transitivity_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", nat_ty());
    ctx.declare_var_typed("b", nat_ty());
    ctx.declare_var_typed("c", nat_ty());
    ctx.push_obligation(ProofObligation::assume("ab", "a < b"));
    ctx.push_obligation(ProofObligation::assume("bc", "b < c"));
    ctx.push_obligation(ProofObligation::assert("ac", "a < c"));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 nat LIA: strict order is transitive",
    );
}

/// `n: nat ⊢ (n / 2) * 2 <= n`. Floor (Euclidean) division over `nat` — decided
/// in pure LIA without nonlinear reasoning because the divisor is a constant.
#[test]
fn nat_floor_division_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", nat_ty());
    ctx.push_obligation(ProofObligation::assert("floor", "(n / 2) * 2 <= n"));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 nat LIA: floor division satisfies (n / 2) * 2 <= n",
    );
}

/// `m, n: nat ⊢ (m - n) + n == m` with **no** `m >= n` guard. In Verus the
/// output type of `SpecSub` on `nat` is `int`, so `m - n` is a genuine
/// (possibly negative) integer and the round-trip holds unconditionally — it is
/// *not* a saturating `nat` subtraction clamped at 0.
#[test]
fn nat_subtraction_is_int_typed_roundtrip_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("m", nat_ty());
    ctx.declare_var_typed("n", nat_ty());
    ctx.push_obligation(ProofObligation::assert("roundtrip", "m - n + n == m"));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 nat LIA: nat subtraction is int-typed, so (m - n) + n == m for all m, n",
    );
}

/// `n, m: nat ⊢ n - m >= 0` is **false**: because `n - m` is `int`-typed it can
/// be negative (witness `n = 0, m = 1`). A correct `nat`-arithmetic encoding
/// must refute this rather than silently treat subtraction as saturating.
#[test]
fn nat_subtraction_can_be_negative_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", nat_ty());
    ctx.declare_var_typed("m", nat_ty());
    ctx.push_obligation(ProofObligation::assert("nonneg_diff", "n - m >= 0"));
    expect_counterexample(
        &AYEncoder::verify(&ctx),
        "#2778 nat LIA: n - m is int-typed and can be negative (n = 0, m = 1)",
    );
}

/// Overflow-distinguishing shape of `test_overflow_spec_fails_1/2`, but in pure
/// `nat` LIA where ay decides it exactly: `j == a + 2` cannot also satisfy
/// `j == a + 4`, so the wrong equality is refuted with a concrete witness.
/// Because `nat` add is unbounded (no wrap), the only models are the true ones.
#[test]
fn nat_unbounded_add_wrong_equality_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", nat_ty());
    ctx.declare_var_typed("j", nat_ty());
    ctx.push_obligation(ProofObligation::assume("j_def", "j == a + 2"));
    ctx.push_obligation(ProofObligation::assert("wrong", "j == a + 4"));
    expect_counterexample(
        &AYEncoder::verify(&ctx),
        "#2778 nat LIA: unbounded add makes j == a + 2 incompatible with j == a + 4",
    );
}

/// `a: u64 ⊢ (a as nat) + 2 > a as nat`. The `as nat` cast of an unsigned source
/// yields the non-negative integer image; unbounded `+ 2` strictly increases it.
/// This is the verify-direction of the upstream `as nat + 2` pivot.
#[test]
fn as_nat_unbounded_add_strictly_increases_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u64_ty());
    ctx.push_obligation(ProofObligation::assert("succ", "(a as nat) + 2 > a as nat"));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 nat LIA: (a as nat) + 2 > a as nat — unbounded, no fixed-width wrap",
    );
}

/// `a: u64 ⊢ a as nat <= u64::MAX`. The unsigned `as nat` image is bounded above
/// by `2^64 - 1`; the cast carries this range so the bound verifies. (The strict
/// counterexample direction — constructing the `a = u64::MAX` witness through a
/// `bv2int` bridge — remains an ay BV/Int model-construction limitation; see the
/// module notes and `overflow_spec_add.rs`.)
#[test]
fn as_nat_unsigned_upper_bound_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", u64_ty());
    ctx.declare_var_typed("b", nat_ty());
    ctx.push_obligation(ProofObligation::assume("b_def", "b == a as nat"));
    ctx.push_obligation(ProofObligation::assert("ub", "b <= 18446744073709551615"));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 nat LIA: (a as nat) for a: u64 is bounded above by u64::MAX",
    );
}
