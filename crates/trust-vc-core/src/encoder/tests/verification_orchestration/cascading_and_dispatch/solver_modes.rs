// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// An assertion with SolverMode::NonlinearArith should verify using
/// int_mode (Sort::Int), where ay's integer theory handles *, /, %
/// symbolically without BV wrapping semantics.
///
/// Previously returned Unknown fail-closed (#2144). Now routed through
/// int_mode for real verification. Part of #2187.
#[test]
fn test_solver_mode_nonlinear_arith_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("small_x", "x == 5"));

    let obligation = crate::vc::ProofObligation::new(
        "nonlinear_check".to_string(),
        "x * x == 25".to_string(),
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::NonlinearArith);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "NonlinearArith solver mode should verify x*x==25 given x==5",
    );
}

/// An assertion with SolverMode::BitVector should verify using ay's BV theory.
///
/// Previously returned Unknown fail-closed (#2144). Now routed through
/// the normal verification path since ay's Logic::All includes BV theory
/// and the encoder uses BV sorts for integer types. Part of #2405.
#[test]
fn test_solver_mode_bit_vector_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("known_x", "x == 255"));

    let obligation = crate::vc::ProofObligation::new(
        "bv_check".to_string(),
        "x > 0".to_string(),
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::BitVector);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "BitVector solver mode should verify x > 0 given x == 255",
    );
}

/// BitVector mode keeps finite-width quantifiers on concrete BV sorts, so
/// bitwise identities can be proved under the original Verus-style mode.
#[test]
fn test_bit_vector_finite_forall_bitwise_verifies() {
    let mut ctx = VerificationContext::new();
    let obligation = crate::vc::ProofObligation::new(
        "bv_forall_bitwise_identity",
        "forall(|x: u8| (x & x) == x)",
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::BitVector);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "BitVector finite forall should verify x & x == x");
}

/// The same finite-BV path must preserve wrapping semantics and reject false
/// universal facts such as `u8::MAX + 1 > u8::MAX`.
#[test]
fn test_bit_vector_finite_forall_rejects_wrapping_falsehood() {
    let mut ctx = VerificationContext::new();
    let obligation = crate::vc::ProofObligation::new(
        "bv_forall_wrapping_false",
        "forall(|x: u8| x + 1 > x)",
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::BitVector);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "BitVector finite forall must reject x + 1 > x because x = 255 wraps",
    );
}

/// Replayed assert_by facts must keep their solver mode. Without mode-aware
/// replay, this finite-BV quantified fact is re-encoded through Int-mode
/// quantifier arithmetic and the setup phase fails before `after_replay`.
#[test]
fn test_bit_vector_assert_by_quantified_fact_replays_with_mode() {
    let mut ctx = VerificationContext::new();
    ctx.add_assert_by_with_solver_mode(
        "bv_quantified_fact",
        "forall(|x: u8| (x & x) == x)",
        vec![],
        Some(crate::vc::SolverMode::BitVector),
    );
    ctx.push_obligation(ProofObligation::assert("after_replay", "true"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "verified BitVector assert_by forall should replay under BitVector mode",
    );
}

/// An assertion with SolverMode::Default should be processed normally,
/// not returned as Unknown.
#[test]
fn test_solver_mode_default_processes_normally() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("known_x", "x == 5"));

    let obligation = crate::vc::ProofObligation::new(
        "default_check".to_string(),
        "x > 0".to_string(),
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::Default);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Default solver mode should process normally and verify x > 0",
    );
}

/// NonlinearArith verifies symbolic NIA: x*x == 25 with x==5.
/// This is the basic smoke test that the mode routes through int_mode.
#[test]
fn test_nonlinear_arith_symbolic_square() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));

    let obligation = crate::vc::ProofObligation::new(
        "nla_square",
        "x * x == 25",
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::NonlinearArith);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NonlinearArith: x*x==25 given x==5 should verify");
}

/// NonlinearArith with unsigned types — verifies divisibility.
#[test]
fn test_nonlinear_arith_unsigned_divisibility() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.declare_var_typed("q", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("a_val", "a == 42"));
    ctx.push_obligation(ProofObligation::assume("b_val", "b == 6"));
    ctx.push_obligation(ProofObligation::assume("q_val", "q == 7"));

    let obligation =
        crate::vc::ProofObligation::new("nla_div", "a == b * q", crate::vc::ObligationKind::Assert)
            .with_solver_mode(crate::vc::SolverMode::NonlinearArith);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "NonlinearArith: 42 == 6*7 should verify");
}

/// NonlinearArith rejects false properties — soundness check.
#[test]
fn test_nonlinear_arith_rejects_false() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 3"));

    let obligation = crate::vc::ProofObligation::new(
        "nla_false",
        "x * x == 10",
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::NonlinearArith);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "NonlinearArith: x*x==10 given x==3 should produce counterexample",
    );
}

/// `NonlinearArith` intentionally interprets fixed-width values as bounded
/// mathematical integers. It is therefore not a wrapping-execution tactic:
/// callers may transfer an exec theorem to this lane only after their premises
/// establish that every arithmetic operation stays in range.
#[test]
fn test_nonlinear_arith_fixed_width_is_math_not_wrapping() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
    ctx.push_obligation(ProofObligation::assume("x_max", "x == 4294967295"));
    ctx.push_obligation(
        ProofObligation::assert("math_successor", "x + 1 > x")
            .with_solver_mode(crate::vc::SolverMode::NonlinearArith),
    );

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "NonlinearArith is bounded mathematical-int semantics, not u32 wrapping",
    );
}

/// NonlinearArith with mixed mode: default assertion + NIA assertion.
/// Both should verify without interference.
#[test]
fn test_nonlinear_arith_mixed_with_default() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
    ctx.push_obligation(ProofObligation::assume("y_val", "y == 3"));

    ctx.push_obligation(ProofObligation::assert("default_check", "x > y"));

    let obligation = crate::vc::ProofObligation::new(
        "nla_check",
        "x * y == 15",
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::NonlinearArith);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Mixed default + NonlinearArith should both verify");
}

/// Upstream Verus `real_nonlinear1`: the degree-2 polynomial division-shape
/// lemma must verify under `by(nonlinear_arith)` via the sound certificate
/// search, which the bare integer/real theory cannot discharge alone.
///
/// `a >= 0 && b >= 0 && a*a + b*b == (a*b + 1)*q ==> q >= 0`.
#[test]
fn test_nonlinear_real_division_lemma_verifies_with_hint() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Real);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Real);
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Real);

    // `P ==> Q` written in the disjunctive-normal form `!(P) || Q` that the
    // obligation-string grammar accepts (syn has no `==>` operator).
    let obligation = crate::vc::ProofObligation::new(
        "real_nonlinear1",
        "!(a >= 0 && b >= 0 && (a * a + b * b == (a * b + 1) * q)) || (q >= 0)",
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::NonlinearArith);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "real_nonlinear1 division-shape lemma should verify under by(nonlinear_arith)",
    );
}

/// Upstream Verus `real_nonlinear2`: the SAME fact WITHOUT the
/// `by(nonlinear_arith)` hint must NOT verify. The fact is TRUE (a,b>=0 ⇒
/// ab+1>=1>0 and a²+b²>=0, so q=(a²+b²)/(ab+1)>=0) and ay's bare NRA lane
/// (>= 43034c4b0c) could even decide it hint-free — but Verus's DEFAULT
/// prover runs Z3 with `smt.arith.nl=false`, and upstream `real_nonlinear2`
/// pins that hint discipline as observable behavior ("This is true, but we
/// expect that it requires nonlinear_arith" ⇒ `assert_one_fails`). The
/// default path therefore refuses hint-free nonlinear-real goals up front
/// (the assertion.rs default-prover boundary) and classifies them as genuine
/// theory INCOMPLETENESS, which the gate surfaces as a model-less
/// `counterexample`/assert_fails verdict — never `unknown`, never a
/// fabricated model (design-unknown-as-failure.md).
#[test]
fn test_nonlinear_real_division_lemma_not_verified_without_hint() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Real);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Real);
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Real);

    // Default solver mode (no nonlinear_arith hint). Same disjunctive-normal
    // form as the verifying case above.
    let obligation = crate::vc::ProofObligation::new(
        "real_nonlinear2",
        "!(a >= 0 && b >= 0 && (a * a + b * b == (a * b + 1) * q)) || (q >= 0)",
        crate::vc::ObligationKind::Assert,
    );
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    // Must NOT verify (Verus parity), must NOT fabricate a model, and any
    // Unknown must carry the INCOMPLETENESS category so the gate maps it to
    // the model-less failure verdict.
    expect_incompleteness_modelless_failure(
        &result,
        "real_nonlinear2 (hint-free nonlinear-real goal on the default prover profile)",
    );
}

// ── Incompleteness-vs-resource Unknown split: end-to-end directional pair ──
//
// These two tests pin BOTH sides of the soundness boundary in
// `design-unknown-as-failure.md` at the `AYEncoder::verify` boundary
// (not just the `UnknownCategory` classifier, which `unknown_category_tests.rs`
// already covers exhaustively):
//
//   * should-FAIL  — a genuine theory/decision-procedure gap on a proof
//     obligation must surface as a MODEL-LESS verification failure (Verus
//     `Invalid(None, None, None)`), never a soft resource `Unknown`, never a
//     fabricated model. This is what lets the gate map the whole upstream
//     "Z3-unknown-as-fail" class (real_nonlinear2 and cluster #2778) to
//     `counterexample`/assert_fails.
//   * should-VERIFY — a real-arithmetic obligation the bare theory CAN decide
//     must still verify. The incompleteness split must NOT spuriously flip a
//     decidable obligation into a failure (the conservative reading is
//     conservative ABOUT undecided facts only).

/// Should-FAIL direction. The hint-free nonlinear-real obligation
/// (upstream `real.rs::real_nonlinear2`) is TRUE but sits outside the DEFAULT
/// prover profile: Verus runs default queries with `smt.arith.nl=false` and
/// upstream pins the hint-free failure (`assert_one_fails`). trust-vc's
/// default path refuses the goal up front (the assertion.rs boundary; ay's
/// bare NRA lane since 43034c4b0c could otherwise decide it and silently
/// diverge from Verus). End-to-end through `AYEncoder::verify` this must be a
/// model-less failure — not verified, the Unknown (if any) is genuinely
/// `Incompleteness`, and no fabricated model is invented. If this regressed to
/// a resource/timeout category the gate would keep reporting a soft `unknown`
/// and real_nonlinear2 would diverge from Verus.
#[test]
fn test_incompleteness_split_nonlinear_real_is_modelless_failure() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Real);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Real);
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Real);

    // Default solver mode (NO by(nonlinear_arith) hint): the nonlinear
    // certificate pre-pass does not fire, and the default-prover boundary
    // refuses the nonlinear-real goal as theory incompleteness.
    let obligation = crate::vc::ProofObligation::new(
        "real_nonlinear2_modelless",
        "!(a >= 0 && b >= 0 && (a * a + b * b == (a * b + 1) * q)) || (q >= 0)",
        crate::vc::ObligationKind::Assert,
    );
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_incompleteness_modelless_failure(
        &result,
        "real_nonlinear2 (hint-free nonlinear-real goal on the default prover profile)",
    );
}

/// Should-VERIFY direction. The SAME nonlinear-real lemma WITH the
/// `by(nonlinear_arith)` hint is decidable (the certificate pre-pass runs), so
/// it must verify. This guards that the incompleteness split is conservative
/// only about facts the theory genuinely cannot decide — it must never demote a
/// decidable obligation that ay can prove into an incompleteness failure.
#[test]
fn test_incompleteness_split_does_not_demote_decidable_real_obligation() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Real);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Real);
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Real);

    // Identical obligation to the should-fail case above, but routed through the
    // nonlinear-arith certificate path (upstream `real.rs::real_nonlinear1`).
    let obligation = crate::vc::ProofObligation::new(
        "real_nonlinear1_decidable",
        "!(a >= 0 && b >= 0 && (a * a + b * b == (a * b + 1) * q)) || (q >= 0)",
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::NonlinearArith);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "a decidable nonlinear-real obligation must verify — the incompleteness \
         split must not demote it to a failure",
    );
}

// ── Verus `==>` source surface: end-to-end parse → lower → verify ──

/// The `real_nonlinear1` division-shape lemma written with the *natural* Verus
/// `==>` operator (not the hand-desugared `!(P) || Q`) must parse through the
/// obligation-string path, lower to a real `TrustVcExpr::Implies`, and verify
/// under `by(nonlinear_arith)` — exactly like the disjunctive-normal-form case
/// above. This is the path the corpus runner uses for direct-source asserts.
#[test]
fn test_implies_source_surface_division_lemma_verifies_with_hint() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", crate::ir::TrustVcType::Real);
    ctx.declare_var_typed("b", crate::ir::TrustVcType::Real);
    ctx.declare_var_typed("q", crate::ir::TrustVcType::Real);

    let obligation = crate::vc::ProofObligation::new(
        "real_nonlinear1_implies_surface",
        "a >= 0 && b >= 0 && (a * a + b * b == (a * b + 1) * q) ==> q >= 0",
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::NonlinearArith);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "`==>` source surface must verify the division lemma identically to `!(P) || Q`",
    );
}

/// A *false* implication written with `==>` must fail closed: `x >= 0 ==> x > 0`
/// is refuted by `x == 0`. This guards the soundness of the `==>` lowering — a
/// real `Implies` premise that does not entail the conclusion must not verify.
#[test]
fn test_implies_source_surface_false_implication_fails_closed() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::Real);

    let obligation = crate::vc::ProofObligation::new(
        "false_implication_surface",
        "x >= 0 ==> x > 0",
        crate::vc::ObligationKind::Assert,
    );
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_not_verified(
        &result,
        "`x >= 0 ==> x > 0` is false (x == 0) and must fail closed, never verify",
    );
}

// ── #2778 diagnostic-parity: `by(bit_vector)` rejections ──

/// Upstream `bitvector.rs::not_supported_int_in_by_bit_vector`:
/// `assert(x == y) by (bit_vector)` with `x, y: int` must fail closed with the
/// byte-exact `expected finite-width integer` diagnostic — the bit-vector
/// prover cannot model unbounded integers.
#[test]
fn test_bit_vector_int_typed_var_expected_finite_width() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::MathInt);
    ctx.declare_var_typed("y", crate::ir::TrustVcType::MathInt);

    let obligation =
        crate::vc::ProofObligation::new("bv_int_eq", "x == y", crate::vc::ObligationKind::Assert)
            .with_solver_mode(crate::vc::SolverMode::BitVector);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    // Upstream `assert_vir_error_msg` substring.
    expect_error_containing(
        &result,
        "expected finite-width integer",
        "by(bit_vector) over int-typed vars must fail closed with finite-width parity message",
    );
}

/// A `nat`-typed free variable in `by(bit_vector)` is likewise unmodellable and
/// must emit the `expected finite-width integer` parity diagnostic.
#[test]
fn test_bit_vector_nat_typed_var_expected_finite_width() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("n", crate::ir::TrustVcType::Nat);

    let obligation =
        crate::vc::ProofObligation::new("bv_nat", "n == n", crate::vc::ObligationKind::Assert)
            .with_solver_mode(crate::vc::SolverMode::BitVector);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_error_containing(
        &result,
        "expected finite-width integer",
        "by(bit_vector) over a nat-typed var must fail closed with finite-width parity message",
    );
}

/// Upstream `overflow.rs::spec_bitshift_negative`:
/// `assert(1i8 >> (-1i8) == 0i8) by(bit_vector)` must fail closed with the
/// byte-exact `bit-shift with possibly negative shift` diagnostic — a signed
/// shift amount is possibly negative, which the bit-vector prover rejects.
#[test]
fn test_bit_vector_signed_shift_rhs_possibly_negative() {
    let mut ctx = VerificationContext::new();
    let obligation = crate::vc::ProofObligation::new(
        "bv_neg_shift",
        "(1i8 >> (-1i8)) == 0i8",
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::BitVector);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    // Upstream `assert_vir_error_msg` substring.
    expect_error_containing(
        &result,
        "bit-shift with possibly negative shift",
        "by(bit_vector) shift with signed RHS must fail closed with possibly-negative-shift parity",
    );
}

/// An *unsigned* shift amount in `by(bit_vector)` is fine: the possibly-negative
/// rejection keys off the RHS *type* (signed) only, never an unsigned operand,
/// so a `u8` shift amount is not falsely rejected. (`1u8 >> 0u8` is provable.)
#[test]
fn test_bit_vector_unsigned_shift_rhs_not_rejected() {
    let mut ctx = VerificationContext::new();
    let obligation = crate::vc::ProofObligation::new(
        "bv_pos_shift",
        "(2u8 >> 1u8) == 1u8",
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::BitVector);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "by(bit_vector) shift with unsigned RHS must not trip the possibly-negative parity check",
    );
}

/// Upstream `overflow.rs::spec_bitshift_defined_for_larger_ints`:
/// `assert(1u8 >> 20u8 == 0u8) by(bit_vector)` must VERIFY. Unlike Rust (where
/// a shift amount >= the bit width is UB), the bit-vector prover models the
/// shift as pure `bvlshr`, so an over-shift (20 >= 8) is fully defined and
/// yields `0`. BitVector mode carries NO shift-UB obligation
/// (`bv_arith.rs::encode_bv_shift`, `bit_vector_mode` short-circuit), so this is
/// the should-VERIFY half of the `by(bit_vector)` shift cluster — the dual of
/// `test_bit_vector_signed_shift_rhs_possibly_negative` (the Err half). Sound:
/// pure BV theory, ay-complete. Part of #2778.
#[test]
fn test_bit_vector_oversized_shift_rhs_yields_zero() {
    let mut ctx = VerificationContext::new();
    let obligation = crate::vc::ProofObligation::new(
        "bv_oversized_shift",
        "(1u8 >> 20u8) == 0u8",
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::BitVector);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "by(bit_vector) over-shift (1u8 >> 20u8) is defined as bvlshr and must verify to 0u8",
    );
}

/// SOUNDNESS GUARD for the over-shift result value. The over-shift
/// `1u8 >> 20u8` must equal EXACTLY `0u8`, not merely "be defined": asserting a
/// WRONG value (`== 1u8`) must NOT verify. This pins that the BitVector-mode
/// shift-UB suppression does not also collapse the result into an
/// underspecified/havoc value (which would make any equality vacuously
/// provable). It fails closed via a genuine bvlshr counterexample, keeping the
/// should-VERIFY case above honest. Part of #2778.
#[test]
fn test_bit_vector_oversized_shift_wrong_value_not_verified() {
    let mut ctx = VerificationContext::new();
    let obligation = crate::vc::ProofObligation::new(
        "bv_oversized_shift_wrong",
        "(1u8 >> 20u8) == 1u8",
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::BitVector);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_not_verified(
        &result,
        "by(bit_vector) over-shift (1u8 >> 20u8) is 0u8, so asserting == 1u8 must fail closed",
    );
}

// ── #2778 assumption-forwarding: end-to-end through `verify_validated` ──
//
// These drive the FULL forwarding pipeline in `typed.rs::verify_validated`
// (partition → capture-suppressed pre-pass → forward verified body asserts into
// the postcondition's assumption set), not just the `forwardable_body_assert` /
// `postcondition_obligation` classifiers (`typed_tests.rs` covers those). They
// pin BOTH directions of the soundness boundary:
//
//   * should-VERIFY — a function whose body proves a straight-line `assert!`
//     and whose postcondition is consistent with the requires verifies cleanly:
//     forwarding the verified body fact into the postcondition assumption set
//     does not break a function that should pass.
//   * should-FAIL (the soundness-critical half) — a body `assert!` that does
//     NOT itself verify is NEVER forwarded. A postcondition whose truth would
//     require that unverified fact must still FAIL with a counterexample. If the
//     pre-pass ever forwarded an UNVERIFIED assert, this postcondition would
//     spuriously "verify" — that is exactly the unsoundness the pre-pass guards
//     against, so this test is the regression wall for it.
//
// The postcondition is materialized as an `Assert` named exactly
// `"postcondition"` (see `attr_extract` / `ProofObligation::assert`), which is
// what `postcondition_obligation` recognizes as the forwarding RECEIVER.

/// should-VERIFY. A straight-line body `assert!` (`x + 1 > x`) verifies under
/// the requires and is forwarded into the postcondition's assumption set; the
/// postcondition (`x > 0`, implied by `x == 5`) verifies. Exercises the happy
/// path of the partition + pre-pass + forward pipeline end-to-end.
#[test]
fn test_forwarding_verified_body_assert_keeps_function_verifying() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::MathInt);
    ctx.push_obligation(ProofObligation::assume("req", "x == 5"));
    // Straight-line body assert — verifies under the requires, becomes a
    // forwarded assumption for the postcondition group.
    ctx.obligations
        .push(ProofObligation::assert("witness", "x + 1 > x"));
    // The function postcondition (the forwarding RECEIVER): consistent with the
    // requires, so it must verify with the forwarded fact in scope.
    ctx.obligations
        .push(ProofObligation::assert("postcondition", "x > 0"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "a verified straight-line body assert forwarded into the postcondition \
         assumption set must not break a function whose postcondition holds",
    );
}

/// should-FAIL (soundness-critical). The body `assert!` (`y == 100`) does NOT
/// verify — `y` is unconstrained by the requires (`x == 5`), so the pre-pass
/// MUST NOT forward it. The postcondition (`y == 100`) is therefore checked
/// WITHOUT that fabricated fact and correctly fails with a counterexample. A
/// regression that forwarded the unverified assert would make this postcondition
/// spuriously verify — the precise unsoundness the capture-suppressed pre-pass
/// is designed to prevent.
#[test]
fn test_forwarding_never_forwards_an_unverified_body_assert() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::MathInt);
    ctx.declare_var_typed("y", crate::ir::TrustVcType::MathInt);
    ctx.push_obligation(ProofObligation::assume("req", "x == 5"));
    // Body assert that does NOT hold under the requires (y is free) — must fail
    // the pre-pass and therefore must NOT be forwarded.
    ctx.obligations
        .push(ProofObligation::assert("unverified_witness", "y == 100"));
    // Postcondition that is provable ONLY if the (unsound) unverified witness
    // were forwarded. It must fail because forwarding requires prior verification.
    ctx.obligations
        .push(ProofObligation::assert("postcondition", "y == 100"));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "SOUNDNESS: an unverified body assert (y == 100, y free) must NEVER be \
         forwarded, so a postcondition depending on it must fail",
    );
}

/// Discriminator for the should-FAIL wall above. This is the SAME obligation
/// stream as `test_forwarding_never_forwards_an_unverified_body_assert` except
/// the requires now ALSO establishes `y == 100`, so the `y == 100` body assert
/// genuinely VERIFIES in the pre-pass and IS forwarded — and the `y == 100`
/// postcondition consequently verifies. The ONLY difference between this pass
/// and the failing wall is whether the body assert itself verified, which is
/// exactly the gate `verify_validated` applies before forwarding. Together the
/// two tests pin that forwarding is keyed on real verification, not on mere
/// presence of a body assert.
#[test]
fn test_forwarding_forwards_a_verified_body_assert() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::MathInt);
    ctx.declare_var_typed("y", crate::ir::TrustVcType::MathInt);
    ctx.push_obligation(ProofObligation::assume("req", "x == 5"));
    ctx.push_obligation(ProofObligation::assume("yreq", "y == 100"));
    // Now the body assert holds under the requires → it verifies → it forwards.
    ctx.obligations
        .push(ProofObligation::assert("verified_witness", "y == 100"));
    ctx.obligations
        .push(ProofObligation::assert("postcondition", "y == 100"));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "a body assert that verifies under the requires is forwarded, so the \
         postcondition that depends on it verifies — the discriminating twin of \
         the unverified-assert wall",
    );
}

// ── Quantified `by(bit_vector)` faithfulness pins (upstream bitvector.rs) ──
//
// These pin, at the `AYEncoder::verify` boundary, that the obligation strings
// the port emits for upstream `test8` / `test_forall` are processed as REAL
// universally-quantified bit-vector facts — not collapsed to `true`.
//
// Gate-integrity context: the port file expresses these as
// `assert_by_bit_vector!(forall(|..| ..))`. The `forall` *identifier* there is a
// local `fn forall<F>(_f: F) -> bool { true }` shim that exists ONLY so the
// macro's `if false { closure }` type-check compiles; verification works on the
// macro tokens, where the extractor lowers `forall(|..| ..)` into a quantified
// obligation string. If a regression ever caused BitVector mode to treat that
// `forall(...)` as the trivial shim (or otherwise drop the body), the
// should-verify cases below would still pass vacuously — so each is paired with
// a should-FAIL discriminator that can only be rejected if the quantifier body
// is genuinely encoded and the wrapping/finite-width semantics are preserved.

/// Upstream `test8`: two-variable bitwise-AND commutativity over the full u32
/// domain must verify as a genuine universal fact, matching the port case
/// `quantified_bitwise_and_commutativity_u32`.
#[test]
fn test_bit_vector_forall_and_commutativity_u32_verifies() {
    let mut ctx = VerificationContext::new();
    let obligation = crate::vc::ProofObligation::new(
        "bv_forall_and_commutativity",
        "forall(|a: u32, b: u32| (a & b) == (b & a))",
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::BitVector);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "test8 forall|a,b| a&b == b&a must verify as a real u32 universal fact",
    );
}

/// Should-FAIL discriminator for `test8`: swapping `&` commutativity for the
/// FALSE claim `a & b == a | b` must be rejected. If the quantifier body were
/// collapsed to the `true` shim, this would spuriously verify; the rejection
/// proves the body is genuinely encoded.
#[test]
fn test_bit_vector_forall_and_equals_or_rejected() {
    let mut ctx = VerificationContext::new();
    let obligation = crate::vc::ProofObligation::new(
        "bv_forall_and_equals_or_false",
        "forall(|a: u32, b: u32| (a & b) == (a | b))",
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::BitVector);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "forall|a,b| a&b == a|b is false (e.g. a=1,b=2) and must be rejected — \
         proving the quantifier body is encoded, not collapsed to `true`",
    );
}

/// Upstream `test_forall` (verifying subset): equal u32 operands have equal
/// logical right shifts, matching the port case
/// `forall_shift_right_equal_width_subset`. The `!(x==y) || ..` disjunctive
/// normal form is the implication shape the obligation grammar accepts.
#[test]
fn test_bit_vector_forall_equal_operands_equal_shift_verifies() {
    let mut ctx = VerificationContext::new();
    let obligation = crate::vc::ProofObligation::new(
        "bv_forall_equal_shift",
        "forall(|x: u32, y: u32| !(x == y) || (x >> 2) == (y >> 2))",
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::BitVector);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "test_forall subset: x==y ==> x>>2 == y>>2 must verify over u32",
    );
}

/// Should-FAIL discriminator for `test_forall`: dropping the `x == y` guard
/// makes `x >> 2 == y >> 2` false for distinct operands, so it must be
/// rejected. Mirrors upstream `test_forall`'s second (FAILS) assertion that the
/// unguarded shift equality does not hold.
#[test]
fn test_bit_vector_forall_unguarded_shift_equality_rejected() {
    let mut ctx = VerificationContext::new();
    let obligation = crate::vc::ProofObligation::new(
        "bv_forall_unguarded_shift_false",
        "forall(|x: u32, y: u32| (x >> 2) == (y >> 2))",
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::BitVector);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "forall|x,y| x>>2 == y>>2 (no x==y guard) is false (e.g. x=0,y=4) and \
         must be rejected — pins that the guard disjunct is genuinely encoded",
    );
}

/// Upstream `test10_fails` / port `quantified_shift_positive_counterexample_u64`:
/// `forall|i: u64| (1u64 << i) > 0` is FALSE because a large shift amount
/// produces 0 (and `1 << 64` wraps to 0). The finite-width BV path must reject
/// it rather than collapsing the quantifier to the `true` shim.
#[test]
fn test_bit_vector_forall_shift_positive_rejected() {
    let mut ctx = VerificationContext::new();
    let obligation = crate::vc::ProofObligation::new(
        "bv_forall_shift_positive_false",
        "forall(|i: u64| (1u64 << i) > 0u64)",
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::BitVector);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "forall|i| (1u64<<i)>0 is false (large i shifts the bit out) and must be \
         rejected — pins finite-width shift semantics under the quantifier",
    );
}

// ── Bitwise-not-through-cast in by(bit_vector) (upstream bitvector.rs `bitnot`) ──
//
// Upstream `bitnot` exercises signed `!`/bitwise-not under by(bit_vector)
// (`test8` is `proof fn test8(b: i32)` with `!(-8i32) + !(-8i32) == 14`,
// `b1 == !(!b1)`, etc.). When a bitwise-not result is then *cast* to a wider
// width — the `(!x) as i64` shape that appears in the cross-width `bitnot`
// cases — the lowering mis-typed `!x` as `bool` (the `Not` IR node is shared by
// logical-not and bitwise-not). That routed `(!x) as i64` through the bool→int
// cast, feeding a `BitVec` term into an `ite` condition and erroring with
// "sort mismatch in ite: expected Bool, got (_ BitVec 32)". `infer_expr_type`
// now propagates the integer operand's type for bitwise-not, so the cast is
// correctly typed `i32 as i64` (a sign-extension). These two tests pin BOTH
// directions of the soundness boundary so the verifying case is not vacuous.

/// should-VERIFY. The bitwise-not-through-cast obligation in the exact shape the
/// upstream `bitnot` cross-width cases emit. `(!x) as i64` and `(!y)` are real
/// bitwise complements; the disjunctive-normal `!(P) || Q` is a genuine i32/i64
/// universal fact. Before the `Not` type-inference fix this ERRORED in the
/// encoder ("sort mismatch in ite"); it must now verify as a real BV fact.
#[test]
fn test_bit_vector_signed_bitnot_through_cast_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i64"));

    let obligation = crate::vc::ProofObligation::new(
        "bv_signed_bitnot_through_cast",
        "!((x as i64) == y) || (((!x) as i64) == (!y))",
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::BitVector);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "`(x as i64)==y ==> (!x as i64)==(!y)` must verify — bitwise-not through a \
         widening cast is a real i32/i64 BV fact, not a bool→int cast",
    );
}

/// should-FAIL (soundness-critical discriminator). The SAME bitwise-not-through-
/// cast shape, but a FALSE consequent: `(!x) as i64 == (!x) as i64 + 1` can never
/// hold. If the cast lowering ever collapsed `!x` to a vacuous bool→int value (or
/// otherwise dropped the bitwise-not body) this could spuriously verify; the
/// counterexample proves the complement is genuinely encoded with its real value.
#[test]
fn test_bit_vector_signed_bitnot_through_cast_false_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));

    let obligation = crate::vc::ProofObligation::new(
        "bv_signed_bitnot_through_cast_false",
        "((!x) as i64) == ((!x) as i64) + 1i64",
        crate::vc::ObligationKind::Assert,
    )
    .with_solver_mode(crate::vc::SolverMode::BitVector);
    ctx.obligations.push(obligation);

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "`(!x as i64) == (!x as i64) + 1` is false for every x and must produce a \
         counterexample — pins that the bitwise-not-through-cast value is real",
    );
}

/// Concrete sign pin: `!(-8i32) as i64 == 7` is the TRUE value of the upstream
/// `test8` constant (`!(-8) == 7` in two's complement). The sibling FALSE claim
/// `== 8` must be refuted. Together these pin that the bitwise-not-through-cast
/// fix computes the correct numeric value, not merely "verifies".
#[test]
fn test_bit_vector_signed_bitnot_through_cast_concrete_value() {
    let mut verify_ctx = VerificationContext::new();
    verify_ctx.obligations.push(
        crate::vc::ProofObligation::new(
            "bv_bitnot_neg8_true",
            "((!(-8i32)) as i64) == 7i64",
            crate::vc::ObligationKind::Assert,
        )
        .with_solver_mode(crate::vc::SolverMode::BitVector),
    );
    expect_verified(
        &AYEncoder::verify(&verify_ctx),
        "!(-8i32) as i64 == 7 is the correct two's-complement value and must verify",
    );

    let mut refute_ctx = VerificationContext::new();
    refute_ctx.obligations.push(
        crate::vc::ProofObligation::new(
            "bv_bitnot_neg8_false",
            "((!(-8i32)) as i64) == 8i64",
            crate::vc::ObligationKind::Assert,
        )
        .with_solver_mode(crate::vc::SolverMode::BitVector),
    );
    expect_counterexample(
        &AYEncoder::verify(&refute_ctx),
        "!(-8i32) as i64 == 8 is wrong (the value is 7) and must be refuted",
    );
}
