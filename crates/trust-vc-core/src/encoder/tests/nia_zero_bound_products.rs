//! Symbolic nonlinear product sign / monotonicity over unbounded `int`
//! (#2778, upstream `nonlinear.rs` test2 / test3 shapes).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! ## What this locks
//!
//! ay's NIA solver extends incremental linearization with *exact*
//! zero-lower-bound product lemmas (`#nia-zero-bound` in ay,
//! `ay-theories/nia/src/zero_bound_lemmas.rs`): the tangent plane of
//! `m = x*y` at the asserted bound `0` is a valid ordered-ring theorem, not a
//! model-point approximation, so these obligations are decided UNSAT-genuine
//! for **unbounded** symbolic integers:
//!
//! - product sign: `x >= 0 && y >= 0  ==>  x*y >= 0`
//!   (upstream `test2`, `lemma_mul_stay_positive`);
//! - multiplication monotonicity: `x <= y && z >= 0  ==>  x*z <= y*z`
//!   (upstream `test3`, `lemma_inequality_after_mul`).
//!
//! Previously both stalled at solver `Unknown` (McCormick needs finite
//! bounds; tangent hyperplanes are approximations whose UNSAT is rechecked
//! away; bounded enumeration needs a finite box).
//!
//! ## Soundness invariant
//!
//! Every "verifies" case is a true ordered-ring validity over the integers.
//! Every "counterexample" case is the corresponding *strict* strengthening
//! refuted by a zero witness (`x = 0` / `z = 0`) — exactly upstream
//! `test1_fails` (`wrong_lemma_1`). The lemmas must stay WEAK (`>= 0`,
//! `<=`): if ay ever over-strengthened them, the counterexample cases here
//! would flip to Verified and fail the suite.

use super::*;

fn int_ty() -> crate::ir::TrustVcType {
    crate::ir::TrustVcType::MathInt
}

fn int_ctx(vars: &[&str]) -> VerificationContext {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    for v in vars {
        ctx.declare_var_typed(v, int_ty());
    }
    ctx
}

// ---------------------------------------------------------------------------
// Product sign at the zero bound (upstream test2: lemma_mul_stay_positive)
// ---------------------------------------------------------------------------

/// `x >= 0, y >= 0 ⊢ x * y >= 0` — the upstream `test2` proof obligation for
/// fully symbolic, unbounded `int`. Must verify via the ay zero-bound sign
/// lemma (no concrete witnesses, no finite bounds).
#[test]
fn nia_mul_stay_positive_symbolic_verifies() {
    let mut ctx = int_ctx(&["x", "y"]);
    ctx.push_obligation(ProofObligation::assume("x_nonneg", "x >= 0"));
    ctx.push_obligation(ProofObligation::assume("y_nonneg", "y >= 0"));
    ctx.push_obligation(ProofObligation::assert("prod_nonneg", "x * y >= 0"));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 nonlinear.rs test2: x>=0 && y>=0 ==> x*y>=0 must verify symbolically \
         (ay #nia-zero-bound product sign lemma)",
    );
}

/// SOUNDNESS: `x >= 0, y >= 0 ⊢ x * y > 0` is **false** (witness `x = 0`).
/// The zero-bound lemma must stay the weak `x*y >= 0`; a strict
/// over-strengthening would wrongly verify this.
#[test]
fn nia_mul_stay_positive_strict_counterexample() {
    let mut ctx = int_ctx(&["x", "y"]);
    ctx.push_obligation(ProofObligation::assume("x_nonneg", "x >= 0"));
    ctx.push_obligation(ProofObligation::assume("y_nonneg", "y >= 0"));
    ctx.push_obligation(ProofObligation::assert("prod_pos", "x * y > 0"));
    expect_counterexample(
        &AYEncoder::verify(&ctx),
        "#2778 nonlinear.rs: x>=0 && y>=0 does NOT imply x*y>0 (x=0 refutes); \
         the zero-bound sign lemma must not be over-strengthened",
    );
}

/// Mixed weak signs: `x >= 0, y <= 0 ⊢ x * y <= 0` (odd parity of
/// non-positive factors flips the product's weak sign).
#[test]
fn nia_mul_mixed_signs_nonpos_product_verifies() {
    let mut ctx = int_ctx(&["x", "y"]);
    ctx.push_obligation(ProofObligation::assume("x_nonneg", "x >= 0"));
    ctx.push_obligation(ProofObligation::assume("y_nonpos", "y <= 0"));
    ctx.push_obligation(ProofObligation::assert("prod_nonpos", "x * y <= 0"));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 nonlinear arithmetic: x>=0 && y<=0 ==> x*y<=0 must verify symbolically \
         (ay #nia-zero-bound mixed-sign product lemma)",
    );
}

// ---------------------------------------------------------------------------
// Multiplication monotonicity (upstream test3: lemma_inequality_after_mul)
// ---------------------------------------------------------------------------

/// `x <= y, z >= 0 ⊢ x * z <= y * z` — the upstream `test3` proof obligation
/// for fully symbolic, unbounded `int`. Must verify via the ay zero-bound
/// monotonicity lemma (`(y - x) * z >= 0`).
#[test]
fn nia_mul_monotonicity_symbolic_verifies() {
    let mut ctx = int_ctx(&["x", "y", "z"]);
    ctx.push_obligation(ProofObligation::assume("x_le_y", "x <= y"));
    ctx.push_obligation(ProofObligation::assume("z_nonneg", "z >= 0"));
    ctx.push_obligation(ProofObligation::assert("mono", "x * z <= y * z"));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 nonlinear.rs test3: x<=y && z>=0 ==> x*z<=y*z must verify symbolically \
         (ay #nia-zero-bound multiplication monotonicity lemma)",
    );
}

/// SOUNDNESS (upstream `test1_fails`, `wrong_lemma_1`): `x <= y, z >= 0 ⊢
/// x * z < y * z` is **false** (witness `z = 0` makes both sides equal).
/// This is the exact upstream negative case guarding the monotonicity lemma:
/// it must be refuted, never verified.
#[test]
fn nia_mul_monotonicity_strict_counterexample() {
    let mut ctx = int_ctx(&["x", "y", "z"]);
    ctx.push_obligation(ProofObligation::assume("x_le_y", "x <= y"));
    ctx.push_obligation(ProofObligation::assume("z_nonneg", "z >= 0"));
    ctx.push_obligation(ProofObligation::assert("strict_mono", "x * z < y * z"));
    expect_counterexample(
        &AYEncoder::verify(&ctx),
        "#2778 nonlinear.rs test1_fails: x<=y && z>=0 does NOT imply x*z<y*z \
         (z=0 refutes); the zero-bound monotonicity lemma must stay weak",
    );
}

/// Non-positive multiplier flips the order: `x <= y, z <= 0 ⊢ y * z <= x * z`.
#[test]
fn nia_mul_monotonicity_nonpos_multiplier_verifies() {
    let mut ctx = int_ctx(&["x", "y", "z"]);
    ctx.push_obligation(ProofObligation::assume("x_le_y", "x <= y"));
    ctx.push_obligation(ProofObligation::assume("z_nonpos", "z <= 0"));
    ctx.push_obligation(ProofObligation::assert("anti_mono", "y * z <= x * z"));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 nonlinear arithmetic: x<=y && z<=0 ==> y*z<=x*z must verify symbolically \
         (ay #nia-zero-bound monotonicity, non-positive multiplier)",
    );
}

/// SOUNDNESS: without the sign premise on `z`, monotonicity is **false**
/// (witness `z = -1, x = 0, y = 1` gives `x*z = 0 > -1 = y*z`). Guards
/// against the lemma firing without its sign justification.
#[test]
fn nia_mul_monotonicity_without_sign_premise_counterexample() {
    let mut ctx = int_ctx(&["x", "y", "z"]);
    ctx.push_obligation(ProofObligation::assume("x_le_y", "x <= y"));
    ctx.push_obligation(ProofObligation::assert("mono", "x * z <= y * z"));
    expect_counterexample(
        &AYEncoder::verify(&ctx),
        "#2778 nonlinear arithmetic: x<=y alone does NOT imply x*z<=y*z \
         (z=-1,x=0,y=1 refutes); the monotonicity lemma requires the sign premise",
    );
}
