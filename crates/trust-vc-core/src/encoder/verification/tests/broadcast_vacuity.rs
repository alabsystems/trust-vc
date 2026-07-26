//! Soundness tests: a bogus #[broadcast] lemma must never prove a false goal.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! A `#[broadcast]` proof fn publishes its `ensures!` as a GLOBAL forall axiom
//! WITHOUT verifying the body establishes it. A bogus lemma such as
//! `#[broadcast] #[trigger(x * x)] fn evil_sq(x: i32) { ensures!(x * x < 0); }`
//! therefore injects a contradictory premise: any goal containing the trigger
//! term `x * x` becomes vacuously provable (the negated goal is UNSAT under the
//! contradictory broadcast axiom). These tests pin that NO goal chokepoint —
//! regular `assert!`, postcondition, `assert_by!` (with and without a let-bound
//! local), loop invariant, loop ensures — lets such a bogus broadcast prove a
//! false goal, while CORRECT broadcasts still verify and remain usable.

use crate::encoder::types::VerifyResult;
use crate::encoder::{AYEncoder, UnknownCategory};
use crate::vc::{ProofObligation, VerificationContext};

/// Asserts the goal was downgraded by the broadcast-vacuity probe specifically
/// (i.e. `Unknown(VacuousTruth)`), proving the probe — not an unrelated failure
/// path — is what closed the hole. Anything other than Verified is acceptable
/// for soundness, but VacuousTruth is the discriminating signal we expect.
fn assert_vacuous(result: &VerifyResult, ctx_label: &str) {
    assert!(
        matches!(
            result,
            VerifyResult::Unknown {
                category: UnknownCategory::VacuousTruth,
                ..
            }
        ),
        "{ctx_label}: expected Unknown(VacuousTruth) from the broadcast-vacuity \
         probe, got {result:?}"
    );
}

/// The bogus `evil_sq` broadcast axiom: `forall x: i32 :: x * x < 0`, triggered
/// on `x * x`. Published globally without verifying the (empty) body.
fn push_evil_sq(ctx: &mut VerificationContext) {
    ctx.push_obligation(
        ProofObligation::broadcast_assume("broadcast_evil_sq", "x * x < 0")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["x * x".to_string()]]),
    );
}

/// A second bogus shape: `forall x :: false` triggered on `x * x`.
fn push_evil_false(ctx: &mut VerificationContext) {
    ctx.push_obligation(
        ProofObligation::broadcast_assume("broadcast_evil_false", "x * x < 0 && x * x >= 0")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["x * x".to_string()]]),
    );
}

/// A third bogus shape: `forall x :: x + 1 == x` triggered on `x + 1`.
fn push_evil_succ(ctx: &mut VerificationContext) {
    ctx.push_obligation(
        ProofObligation::broadcast_assume("broadcast_evil_succ", "x + 1 == x")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["x + 1".to_string()]]),
    );
}

fn base_ctx() -> VerificationContext {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");
    ctx.declare_var_parsed("v", "i32");
    ctx
}

// ───────────────────────── REPRODUCTION / ADVERSARIAL ─────────────────────────

#[test]
fn evil_sq_regular_assert_false_goal_not_verified() {
    let mut ctx = base_ctx();
    push_evil_sq(&mut ctx);
    ctx.push_assume("v_is_5", "v == 5");
    ctx.push_assert("false_goal", "v * v == 99");
    let result = AYEncoder::verify(&ctx);
    assert_vacuous(&result, "regular assert! v*v==99 under bogus evil_sq");
}

#[test]
fn evil_sq_postcondition_false_goal_not_verified() {
    let mut ctx = base_ctx();
    push_evil_sq(&mut ctx);
    ctx.push_assume("v_is_5", "v == 5");
    ctx.push_obligation(ProofObligation::ensures("postcondition", "v * v == 99"));
    let result = AYEncoder::verify(&ctx);
    assert_vacuous(&result, "postcondition v*v==99 under bogus evil_sq");
}

#[test]
fn evil_sq_assert_by_false_goal_not_verified() {
    let mut ctx = base_ctx();
    push_evil_sq(&mut ctx);
    ctx.push_assume("v_is_5", "v == 5");
    ctx.add_assert_by("evil_assert_by", "v * v == 99", vec![]);
    let result = AYEncoder::verify(&ctx);
    assert_vacuous(&result, "assert_by! v*v==99 under bogus evil_sq");
}

#[test]
fn evil_sq_assert_by_with_let_false_goal_not_verified() {
    // assert_by! { let v: i32 = 5; v * v == 99 } — the surviving hole.
    let mut ctx = base_ctx();
    push_evil_sq(&mut ctx);
    ctx.add_assert_by(
        "evil_assert_by_let",
        "v * v == 99",
        vec![ProofObligation::assume("let_v", "v == 5")],
    );
    let result = AYEncoder::verify(&ctx);
    assert_vacuous(
        &result,
        "assert_by!{ let v=5; v*v==99 } under bogus evil_sq (the surviving hole)",
    );
}

#[test]
fn evil_sq_loop_invariant_false_goal_not_verified() {
    let mut ctx = base_ctx();
    push_evil_sq(&mut ctx);
    ctx.push_assume("v_is_5", "v == 5");
    ctx.push_obligation(ProofObligation::loop_invariant("evil_inv", "v * v == 99"));
    let result = AYEncoder::verify(&ctx);
    assert_vacuous(&result, "loop invariant v*v==99 under bogus evil_sq");
}

#[test]
fn evil_sq_loop_ensures_false_goal_not_verified() {
    let mut ctx = base_ctx();
    push_evil_sq(&mut ctx);
    ctx.push_assume("v_is_5", "v == 5");
    ctx.push_obligation(ProofObligation::loop_ensures("evil_ens", "v * v == 99"));
    let result = AYEncoder::verify(&ctx);
    assert_vacuous(&result, "loop ensures v*v==99 under bogus evil_sq");
}

#[test]
fn evil_false_assert_by_false_goal_not_verified() {
    let mut ctx = base_ctx();
    push_evil_false(&mut ctx);
    ctx.add_assert_by(
        "evil_false_assert_by",
        "v * v == 99",
        vec![ProofObligation::assume("let_v", "v == 5")],
    );
    let result = AYEncoder::verify(&ctx);
    assert_vacuous(&result, "assert_by! under ensures!(false)-shaped broadcast");
}

#[test]
fn evil_succ_assert_by_false_goal_not_verified() {
    let mut ctx = base_ctx();
    push_evil_succ(&mut ctx);
    ctx.add_assert_by(
        "evil_succ_assert_by",
        "v == 99",
        vec![ProofObligation::assume("let_v", "v == 5")],
    );
    let result = AYEncoder::verify(&ctx);
    assert_vacuous(&result, "assert_by! under ensures!(x+1==x) broadcast");
}

// ───────────────────────────── CONTROLS (a) ─────────────────────────────
// No-broadcast versions: the same false goal must be a Counterexample.

#[test]
fn no_broadcast_regular_assert_false_goal_counterexample() {
    let mut ctx = base_ctx();
    ctx.push_assume("v_is_5", "v == 5");
    ctx.push_assert("false_goal", "v * v == 99");
    let result = AYEncoder::verify(&ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "without a broadcast, v*v==99 must be a counterexample, got {result:?}"
    );
}

#[test]
fn no_broadcast_assert_by_false_goal_counterexample() {
    let mut ctx = base_ctx();
    ctx.add_assert_by(
        "plain_assert_by",
        "v * v == 99",
        vec![ProofObligation::assume("let_v", "v == 5")],
    );
    let result = AYEncoder::verify(&ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "without a broadcast, assert_by! v*v==99 must be a counterexample, got {result:?}"
    );
}

// ───────────────────────────── CONTROLS (b) ─────────────────────────────
// CORRECT broadcast: the square lemma `gx * gx >= 0` over `gx: i8`, guarded to
// |gx| <= 11. Consistent-broadcast control for the vacuity gate.
//
// Two deliberate choices make this broadcast HONESTLY consistent AND
// solver-certifiable, so the control tests below demand SAT only on genuinely
// satisfiable formulas:
//
// 1. GUARD (honesty): under wrapping two's-complement semantics an unguarded
//    square lemma is FALSE — for i32, `forall x :: x * x >= 0` is falsified at
//    x = 46341 (46341^2 = 2_147_488_281 wraps to -2_147_479_015 < 0), so the
//    original i32 version of this control was itself a contradictory premise
//    and the "consistent-broadcast" tests demanded SAT on an UNSAT formula
//    (they only ever passed via a removed unsound solver authority). For i8,
//    12^2 = 144 wraps to -112 < 0; with |gx| <= 11, gx^2 <= 121 <= i8::MAX
//    never overflows, so the guarded lemma is genuinely valid.
//
// 2. i8 BINDER (certifiability): a Counterexample/consistency-witness result
//    requires ay to certify SAT of a formula CONTAINING the broadcast forall,
//    i.e. genuinely prove the forall holds in the model. ay's BV-MBQI proves
//    foralls by exhaustive instantiation only for binder widths <= 8
//    (BV_EXHAUSTIVE_MAX_WIDTH); a BV32 binder can never be SAT-certified, so
//    an i32 version of even the honestly-guarded lemma leaves these controls
//    Unknown. The i8 binder keeps the lemma a real guarded square lemma while
//    making its consistency machine-checkable (256-value enumeration).
//
// The goals below stay over `v: i32` with `v == 5` assumed, so they are
// ground-decidable; what these controls exercise is the vacuity gate's
// behavior when a CONSISTENT broadcast is in scope (no over-rejection, and
// real counterexamples must survive).

fn push_good_sq(ctx: &mut VerificationContext) {
    ctx.declare_var_parsed("gx", "i8");
    let mut broadcast = ProofObligation::broadcast_assume("broadcast_good_sq", "gx * gx >= 0")
        .with_bound_vars(vec!["gx".to_string()])
        .with_trigger_patterns(vec![vec!["gx * gx".to_string()]]);
    broadcast.broadcast_guard = Some(vec![
        crate::vc::BroadcastGuardClause {
            condition: "gx >= -11".to_string(),
        },
        crate::vc::BroadcastGuardClause {
            condition: "gx <= 11".to_string(),
        },
    ]);
    ctx.push_obligation(broadcast);
}

#[test]
fn good_sq_regular_assert_true_goal_verifies() {
    let mut ctx = base_ctx();
    push_good_sq(&mut ctx);
    ctx.push_assume("v_is_5", "v == 5");
    ctx.push_assert("true_goal", "v * v >= 0");
    let result = AYEncoder::verify(&ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "correct broadcast x*x>=0 must verify v*v>=0 via assert!, got {result:?}"
    );
}

#[test]
fn good_sq_assert_by_true_goal_verifies() {
    let mut ctx = base_ctx();
    push_good_sq(&mut ctx);
    ctx.add_assert_by(
        "good_assert_by",
        "v * v >= 0",
        vec![ProofObligation::assume("let_v", "v == 5")],
    );
    let result = AYEncoder::verify(&ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "correct broadcast x*x>=0 must verify v*v>=0 via assert_by!, got {result:?}"
    );
}

#[test]
fn good_sq_regular_assert_false_goal_counterexample() {
    // A genuinely false goal under a CONSISTENT broadcast must still fail (not
    // be flagged vacuous): no over-rejection, and the real counterexample stands.
    let mut ctx = base_ctx();
    push_good_sq(&mut ctx);
    ctx.push_assume("v_is_5", "v == 5");
    ctx.push_assert("false_goal", "v * v == 99");
    let result = AYEncoder::verify(&ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "under a consistent broadcast a false goal must be a counterexample, got {result:?}"
    );
}

// ───────────────────────────── CONTROLS (c) ─────────────────────────────
// Guarded requires->ensures broadcast: verifies + usable.

#[test]
fn guarded_broadcast_usable() {
    // forall x :: x >= 0 ==> sqrt_sq(x) == x (guarded). Use it on a value known
    // to satisfy the guard. Modeled with an uninterpreted helper so the broadcast
    // is the sole source of the fact.
    let mut ctx = base_ctx();
    ctx.declare_helper_function_typed(
        "sqrt_sq",
        crate::ir::TrustVcType::Int { width: 32 },
        vec![("x".to_string(), crate::ir::TrustVcType::Int { width: 32 })],
    );
    let mut broadcast = ProofObligation::broadcast_assume("broadcast_guarded", "sqrt_sq(x) == x")
        .with_bound_vars(vec!["x".to_string()])
        .with_trigger_patterns(vec![vec!["sqrt_sq(x)".to_string()]]);
    broadcast.broadcast_guard = Some(vec![crate::vc::BroadcastGuardClause {
        condition: "x >= 0".to_string(),
    }]);
    ctx.push_obligation(broadcast);
    ctx.push_assume("v_is_5", "v == 5");
    ctx.push_assert("guarded_goal", "sqrt_sq(v) == 5");
    let result = AYEncoder::verify(&ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "guarded requires->ensures broadcast must verify a guard-satisfying goal, got {result:?}"
    );
}

// ───────────────────────────── CONTROLS (d) ─────────────────────────────
// Opaque-predicate corpus-style broadcast (uninterpreted predicate): still works.

#[test]
fn opaque_predicate_broadcast_usable() {
    let mut ctx = base_ctx();
    ctx.declare_helper_function_typed(
        "p",
        crate::ir::TrustVcType::Bool,
        vec![("x".to_string(), crate::ir::TrustVcType::Int { width: 32 })],
    );
    ctx.push_obligation(
        ProofObligation::broadcast_assume("broadcast_opaque_p", "p(x)")
            .with_bound_vars(vec!["x".to_string()])
            .with_trigger_patterns(vec![vec!["p(x)".to_string()]]),
    );
    ctx.push_assume("v_is_5", "v == 5");
    ctx.push_assert("opaque_goal", "p(v)");
    let result = AYEncoder::verify(&ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "opaque-predicate broadcast forall x::p(x) must verify p(v), got {result:?}"
    );
}

// ───────────────── P2: UNIVERSALLY-QUANTIFIED goal vacuity ─────────────────
// A contradictory #[broadcast] lemma must not prove a universally-quantified
// FALSE goal. Before the P2 fix, the vacuity probe re-verified `¬G` (an
// existential, for a forall goal G), ay returned Unknown rather than Verified,
// and the gate's `_ => None` arm kept the vacuous `Verified`. The gate now
// treats a NON-REFUTED negation (Unknown included) of a *quantified* goal
// conservatively, downgrading to Unknown(VacuousTruth).

#[test]
fn evil_sq_triggered_forall_false_goal_not_verified() {
    // `forall |i: i32| #[trigger] (i + 1) == i` is false for every i32 (i+1 != i
    // for all i, including in wrapping arithmetic). With the explicit `#[trigger]`
    // the negated probe stays a real quantifier, so this is the exact P2 hole.
    let mut ctx = base_ctx();
    push_evil_sq(&mut ctx);
    ctx.push_assert("qfalse_succ", "forall |i: i32| #[trigger] (i + 1) == i");
    let result = AYEncoder::verify(&ctx);
    assert_vacuous(
        &result,
        "triggered forall (i+1)==i under bogus evil_sq (P2 quantified-goal hole)",
    );
}

#[test]
fn evil_sq_forall_self_succ_false_goal_not_verified() {
    // `forall |i: i32| (i * i) == (i * i) + 1` is s == s + 1: no fixpoint, false.
    let mut ctx = base_ctx();
    push_evil_sq(&mut ctx);
    ctx.push_assert("qfalse_ii", "forall(|i: i32| (i * i) == (i * i) + 1)");
    let result = AYEncoder::verify(&ctx);
    assert_vacuous(
        &result,
        "forall (i*i)==(i*i)+1 under bogus evil_sq (P2 quantified-goal hole)",
    );
}

#[test]
fn no_broadcast_triggered_forall_false_goal_counterexample() {
    // Control: WITHOUT a broadcast lemma the same false forall must refute
    // (Counterexample), proving the engine is not a verify-all and the vacuity
    // downgrade above is broadcast-scoped, not blanket over-rejection.
    let mut ctx = base_ctx();
    ctx.push_assert("qfalse_succ", "forall |i: i32| #[trigger] (i + 1) == i");
    let result = AYEncoder::verify(&ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "without a broadcast, false forall (i+1)==i must be a counterexample, got {result:?}"
    );
}

// ────────────── Interpreted-op dead-trigger GROUND REPLAY ──────────────
// A trigger headed by an interpreted arithmetic/BV op (`x * x` -> `bvmul`) can
// never be E-matched by ay, so `add_typed_broadcast` ground-replays the lemma
// (goal-side IR trigger matches + type-boundary battery) instead of asserting
// the live forall. These tests pin that the replay delivers the lemma's proof
// power at SYMBOLIC goal terms (no concrete pin like `v == 5` to fold through)
// while an evil lemma still cannot verify anything.

#[test]
fn good_sq_symbolic_goal_verifies_via_ground_replay() {
    // Ground-replay of the interpreted-op-headed trigger `gx * gx`, exercised
    // with a SOUND goal within the lemma's guard. `push_good_sq` is the honest
    // i8 lemma `|gx| <= 11 ==> gx*gx >= 0` (an UNGUARDED i32 `v*v >= 0` is FALSE
    // under wrapping — v = 92677 overflows negative — so it must never be the
    // vehicle). A symbolic `gv: i8` bounded to the guard makes `gv*gv >= 0`
    // genuinely true and provable ONLY by ground-replaying the lemma at the
    // goal's `gv*gv` (the E-matching stand-in ay cannot do); it is not a
    // vacuous premise (evil_sq_symbolic_goal_still_not_verified is the control).
    let mut ctx = base_ctx();
    ctx.declare_var_parsed("gv", "i8");
    push_good_sq(&mut ctx);
    ctx.push_assume("gv_lo", "gv >= -11");
    ctx.push_assume("gv_hi", "gv <= 11");
    ctx.push_assert("symbolic_true_goal", "gv * gv >= 0");
    let result = AYEncoder::verify(&ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "ground-replayed i8-guarded broadcast gx*gx>=0 must verify guard-bounded \
         symbolic gv*gv>=0, got {result:?}"
    );
}

#[test]
fn evil_sq_symbolic_goal_still_not_verified() {
    // Symbolic companion of the reproduction tests: with no concrete pin, the
    // evil lemma's boundary instance (`0*0 < 0` = false) still poisons the
    // context, so the goal must stay NOT-verified (vacuity-flagged).
    let mut ctx = base_ctx();
    push_evil_sq(&mut ctx);
    ctx.push_assert("symbolic_false_goal", "v * v == 99");
    let result = AYEncoder::verify(&ctx);
    assert_vacuous(
        &result,
        "symbolic assert! v*v==99 under bogus evil_sq (ground replay)",
    );
}

#[test]
fn good_sq_quantified_true_goal_still_verifies() {
    // No over-rejection: a genuinely TRUE universally-quantified goal under a
    // CONSISTENT broadcast must still verify (the negated probe refutes ¬G with a
    // real consistency witness, so the conservative quantified-goal path is not
    // taken). `forall |i: i32| #[trigger] (i * i) == (i * i)` is a tautology.
    let mut ctx = base_ctx();
    push_good_sq(&mut ctx);
    ctx.push_assert(
        "qtrue_refl",
        "forall |i: i32| #[trigger] (i * i) == (i * i)",
    );
    let result = AYEncoder::verify(&ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "a true quantified goal under a consistent broadcast must verify (no \
         over-rejection), got {result:?}"
    );
}
