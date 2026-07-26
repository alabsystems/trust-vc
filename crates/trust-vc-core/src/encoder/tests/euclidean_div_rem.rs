//! Euclidean integer division/remainder encoder-primitive soundness (#2778).
//!
//! Verus's `/` and `%` on integers are *Euclidean* — they round the quotient
//! toward -inf so the remainder is always non-negative (`q*b + r == a`,
//! `0 <= r < |b|`). This is exactly Rust's `*::div_euclid` / `*::rem_euclid`,
//! and differs from the truncated `/`/`%` that follow the dividend's sign.
//!
//! These tests pin the `int_euclidean_div` / `int_euclidean_mod` encoder
//! primitives directly against the ay solver in both directions:
//! - should-verify: the Euclidean constants and the defining identities hold;
//! - should-fail: the truncated quotient/remainder are demonstrably NOT what
//!   the Euclidean primitive produces (so the primitive is not silently a
//!   truncating alias), and a wrong constant is refuted.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use ay_dpll::api::{Logic, Solver};

struct DirectEuclideanEnv {
    solver: Solver,
    variables: std::collections::HashMap<String, Term>,
    collection_lengths: std::collections::HashMap<String, Term>,
    var_types: std::collections::HashMap<String, crate::ir::TrustVcType>,
    functions: std::collections::HashMap<String, FuncDecl>,
}

impl DirectEuclideanEnv {
    fn new() -> Self {
        Self {
            solver: Solver::try_new(Logic::All).unwrap(),
            variables: std::collections::HashMap::new(),
            collection_lengths: std::collections::HashMap::new(),
            var_types: std::collections::HashMap::new(),
            functions: std::collections::HashMap::new(),
        }
    }

    fn parser(&mut self) -> AstExpressionParser<'_> {
        AstExpressionParser::new(
            &mut self.solver,
            &self.variables,
            &mut self.collection_lengths,
            &self.var_types,
            &self.functions,
        )
    }
}

/// Returns true iff `term == expected` is *valid* (its negation is UNSAT).
fn term_equals_const(solver: &mut Solver, term: Term, expected: i64) -> bool {
    let expected_term = solver.int_const(expected);
    let eq = solver.try_eq(term, expected_term).unwrap();
    let neg = solver.try_not(eq).unwrap();
    solver.try_push().unwrap();
    solver.try_assert_term(neg).unwrap();
    let sat_result = solver.try_check_sat().unwrap();
    let unsat = sat_result.result().is_unsat();
    solver.try_pop().unwrap();
    unsat
}

/// Returns true iff `term == expected` is *satisfiable* (could be that value).
fn term_can_equal_const(solver: &mut Solver, term: Term, expected: i64) -> bool {
    let expected_term = solver.int_const(expected);
    let eq = solver.try_eq(term, expected_term).unwrap();
    solver.try_push().unwrap();
    solver.try_assert_term(eq).unwrap();
    let sat_result = solver.try_check_sat().unwrap();
    let sat = sat_result.result().is_sat();
    solver.try_pop().unwrap();
    sat
}

/// SHOULD-VERIFY: the Euclidean div/mod constants match Verus `/`/`%`
/// (`div_signed_euclidean` / `mod_signed_euclidean`): quotient rounds toward
/// -inf and the remainder is always non-negative.
#[test]
fn euclidean_div_rem_signed_constants_match_verus() {
    // (a, b, euclid_div, euclid_mod)
    let cases = [
        (7, 3, 2, 1),
        (-7, 3, -3, 2),
        (7, -3, -2, 1),
        (-7, -3, 3, 2),
        (8, 3, 2, 2),
        (-8, 3, -3, 1),
        (8, -3, -2, 2),
        (-8, -3, 3, 1),
    ];
    for (a, b, exp_div, exp_mod) in cases {
        let mut env = DirectEuclideanEnv::new();
        let (div_term, mod_term) = {
            let mut parser = env.parser();
            let a_term = parser.solver.int_const(a);
            let b_term = parser.solver.int_const(b);
            let div_term = parser.int_euclidean_div(a_term, b_term).unwrap();
            let a_term2 = parser.solver.int_const(a);
            let b_term2 = parser.solver.int_const(b);
            let mod_term = parser.int_euclidean_mod(a_term2, b_term2).unwrap();
            (div_term, mod_term)
        };
        assert!(
            term_equals_const(&mut env.solver, div_term, exp_div),
            "euclid_div({a}, {b}) must equal {exp_div}"
        );
        assert!(
            term_equals_const(&mut env.solver, mod_term, exp_mod),
            "euclid_mod({a}, {b}) must equal {exp_mod}"
        );
    }
}

/// SHOULD-VERIFY: the defining Euclidean identity `q*b + r == a` holds, with a
/// non-negative remainder `0 <= r < |b|`, for the four sign combinations.
#[test]
fn euclidean_div_rem_defining_identity_holds() {
    let cases = [(7, 3), (-7, 3), (7, -3), (-7, -3), (-8, 3), (8, -3)];
    for (a, b) in cases {
        let mut env = DirectEuclideanEnv::new();
        let (q, r) = {
            let mut parser = env.parser();
            let a_term = parser.solver.int_const(a);
            let b_term = parser.solver.int_const(b);
            let q = parser.int_euclidean_div(a_term, b_term).unwrap();
            let a_term2 = parser.solver.int_const(a);
            let b_term2 = parser.solver.int_const(b);
            let r = parser.int_euclidean_mod(a_term2, b_term2).unwrap();
            (q, r)
        };

        // q*b + r == a
        let b_term = env.solver.int_const(b);
        let qb = env.solver.try_mul(q, b_term).unwrap();
        let recon = env.solver.try_add(qb, r).unwrap();
        assert!(
            term_equals_const(&mut env.solver, recon, a),
            "euclid: q*b + r must reconstruct a for ({a}, {b})"
        );

        // 0 <= r  (always non-negative)
        let zero = env.solver.int_const(0);
        let r_ge_0 = env.solver.try_ge(r, zero).unwrap();
        let neg_ge = env.solver.try_not(r_ge_0).unwrap();
        env.solver.try_push().unwrap();
        env.solver.try_assert_term(neg_ge).unwrap();
        let ge_sat_result = env.solver.try_check_sat().unwrap();
        let ge_unsat = ge_sat_result.result().is_unsat();
        env.solver.try_pop().unwrap();
        assert!(ge_unsat, "euclid remainder must be >= 0 for ({a}, {b})");

        // r < |b|
        let abs_b = b.unsigned_abs() as i64;
        let abs_b_term = env.solver.int_const(abs_b);
        let r_lt_absb = env.solver.try_lt(r, abs_b_term).unwrap();
        let neg_lt = env.solver.try_not(r_lt_absb).unwrap();
        env.solver.try_push().unwrap();
        env.solver.try_assert_term(neg_lt).unwrap();
        let lt_sat_result = env.solver.try_check_sat().unwrap();
        let lt_unsat = lt_sat_result.result().is_unsat();
        env.solver.try_pop().unwrap();
        assert!(lt_unsat, "euclid remainder must be < |b| for ({a}, {b})");
    }
}

/// SHOULD-FAIL direction: the Euclidean primitive is genuinely NOT a truncating
/// alias. For `-7 / 3` the truncated quotient is `-2` (and truncated remainder
/// `-1`), but the Euclidean primitive yields `-3` / `2`. Asserting the
/// truncated values must be refutable, and asserting the Euclidean values is
/// the only satisfiable possibility.
#[test]
fn euclidean_div_rem_rejects_truncated_results() {
    let mut env = DirectEuclideanEnv::new();
    let (div_term, mod_term) = {
        let mut parser = env.parser();
        let a = parser.solver.int_const(-7);
        let b = parser.solver.int_const(3);
        let div_term = parser.int_euclidean_div(a, b).unwrap();
        let a2 = parser.solver.int_const(-7);
        let b2 = parser.solver.int_const(3);
        let mod_term = parser.int_euclidean_mod(a2, b2).unwrap();
        (div_term, mod_term)
    };

    // Truncated quotient -2 must NOT be a possible value of euclid_div(-7, 3).
    assert!(
        !term_can_equal_const(&mut env.solver, div_term, -2),
        "euclid_div(-7, 3) must NOT equal the truncated quotient -2"
    );
    // Truncated remainder -1 must NOT be a possible value of euclid_mod(-7, 3):
    // the Euclidean remainder is always non-negative.
    assert!(
        !term_can_equal_const(&mut env.solver, mod_term, -1),
        "euclid_mod(-7, 3) must NOT equal the truncated remainder -1"
    );
}

/// SHOULD-FAIL direction: a wrong Euclidean constant is refuted. `-7 / 3` is
/// `-3` under Euclidean rounding, so claiming `-4` must be unsatisfiable.
#[test]
fn euclidean_div_rejects_wrong_constant() {
    let mut env = DirectEuclideanEnv::new();
    let div_term = {
        let mut parser = env.parser();
        let a = parser.solver.int_const(-7);
        let b = parser.solver.int_const(3);
        parser.int_euclidean_div(a, b).unwrap()
    };
    assert!(
        !term_can_equal_const(&mut env.solver, div_term, -4),
        "euclid_div(-7, 3) is -3, so -4 must be refuted"
    );
    assert!(
        term_can_equal_const(&mut env.solver, div_term, -3),
        "euclid_div(-7, 3) must be able to equal the correct value -3"
    );
}

// ---------------------------------------------------------------------------
// End-to-end: Verus `int` `/` and `%` flow through `encode_int_arith` and must
// now select the Euclidean primitive (not truncation). These mirror the
// upstream `div_signed_euclidean` / `mod_signed_euclidean` /
// `div_mod_signed_properties` `by(bit_vector)` cases (cluster #2778), driven
// through the `VerificationContext` string path over `TrustVcType::MathInt`.
// ---------------------------------------------------------------------------

fn int_ty() -> crate::ir::TrustVcType {
    crate::ir::TrustVcType::MathInt
}

/// SHOULD-VERIFY: `(-7) / 3 == -3` over `int` (Euclidean). The truncated
/// quotient is `-2`; the Euclidean lowering must make this assertion verify.
#[test]
fn int_div_negative_dividend_is_euclidean_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", int_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == -7"));
    ctx.push_obligation(ProofObligation::assert("euclid_q", "a / 3 == -3"));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 int Euclidean: -7 / 3 == -3 (rounds toward -inf, not truncated -2)",
    );
}

/// SHOULD-FAIL: the truncated quotient `-2` for `(-7) / 3` over `int` must be
/// refuted, proving the lowering is Euclidean and not silently truncating.
#[test]
fn int_div_negative_dividend_truncated_quotient_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", int_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == -7"));
    ctx.push_obligation(ProofObligation::assert("trunc_q", "a / 3 == -2"));
    expect_counterexample(
        &AYEncoder::verify(&ctx),
        "#2778 int Euclidean: -7 / 3 is -3, so the truncated -2 must be refuted",
    );
}

/// SHOULD-VERIFY: `(-7) % 3 == 2` over `int` (Euclidean remainder is always
/// non-negative). The truncated remainder is `-1`.
#[test]
fn int_rem_negative_dividend_is_nonnegative_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", int_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == -7"));
    ctx.push_obligation(ProofObligation::assert("euclid_r", "a % 3 == 2"));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 int Euclidean: -7 % 3 == 2 (non-negative remainder, not truncated -1)",
    );
}

/// SHOULD-FAIL: the truncated (sign-of-dividend) remainder `-1` for `(-7) % 3`
/// over `int` must be refuted.
#[test]
fn int_rem_negative_dividend_truncated_remainder_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", int_ty());
    ctx.push_obligation(ProofObligation::assume("a_val", "a == -7"));
    ctx.push_obligation(ProofObligation::assert("trunc_r", "a % 3 == -1"));
    expect_counterexample(
        &AYEncoder::verify(&ctx),
        "#2778 int Euclidean: -7 % 3 is 2, so the truncated -1 must be refuted",
    );
}

/// SHOULD-VERIFY: the defining identity `(a/b)*b + (a%b) == a` over `int` for a
/// fixed non-zero divisor, the `int`-cast analogue of upstream
/// `div_mod_signed_properties`'s first assertion. The divisor is concrete (`3`)
/// so the LIA+div theory decides it; the dividend stays fully symbolic, so the
/// identity is exercised across every sign of `a`. (A *symbolic* divisor makes
/// `(a/b)*b` nonlinear and the ay solver soundly returns `Unknown` — that is
/// fail-closed, not in scope here.)
#[test]
fn int_div_mod_reconstruction_identity_fixed_divisor_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", int_ty());
    ctx.push_obligation(ProofObligation::assert("recon", "(a / 3) * 3 + a % 3 == a"));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 int Euclidean: (a/3)*3 + (a%3) == a for all signed int a",
    );
}

/// SHOULD-VERIFY: the Euclidean remainder is non-negative and bounded for a
/// fixed positive divisor — `0 <= a % 3 < 3` over `int` (upstream
/// `div_mod_signed_properties` second/third assertions, divisor pinned to a
/// concrete positive value so the query is decidable).
#[test]
fn int_mod_nonnegative_and_bounded_fixed_divisor_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", int_ty());
    ctx.push_obligation(ProofObligation::assert("bounds", "a % 3 >= 0 && a % 3 < 3"));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 int Euclidean: 0 <= a % 3 < 3 for all signed int a (non-negative bounded remainder)",
    );
}

/// SHOULD-FAIL: a *false strengthening* of the remainder bound — `a % 3 > 0`,
/// i.e. strictly positive even when `a` is a multiple of `3` — must be refuted,
/// because an exact division (`a == 0`) gives remainder `0`. This pins that the
/// Euclidean remainder genuinely reaches `0` and is not over-constrained.
#[test]
fn int_mod_strictly_positive_is_refuted_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", int_ty());
    ctx.push_obligation(ProofObligation::assert("strict_pos", "a % 3 > 0"));
    expect_counterexample(
        &AYEncoder::verify(&ctx),
        "#2778 int Euclidean: a % 3 > 0 is false — a = 0 (or any multiple of 3) gives remainder 0",
    );
}

// ---------------------------------------------------------------------------
// Literal-divisor purification soundness (#2778). The Euclidean div/mod-by-
// constant purification recognizes ONLY a compile-time literal divisor and
// routes it to decidable LIA+div. These tests pin the four soundness corners:
//   1. the true reconstruction identity verifies (covered above);
//   2. a FALSE reconstruction (`== a + 1`) must NOT verify — no spurious axiom;
//   3. dropping the remainder (`(a/3)*3 == a`) must NOT verify;
//   4. a SYMBOLIC divisor stays on the native path → Unknown (fail-closed),
//      never spuriously decided;
//   5. a genuinely nonlinear `var*var` goal stays Unknown.
// ---------------------------------------------------------------------------

/// SHOULD-FAIL: a FALSE reconstruction `(a/3)*3 + a%3 == a + 1`. The purified
/// Euclidean axioms make the LHS provably equal to `a`, so the `+ 1` variant is
/// refuted with a counterexample. This is the no-false-`Verified` guard: the
/// literal-divisor recognition must not assert a too-strong (wrong) identity.
#[test]
fn int_div_mod_reconstruction_off_by_one_is_refuted_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", int_ty());
    ctx.push_obligation(ProofObligation::assert(
        "recon_bad",
        "(a / 3) * 3 + a % 3 == a + 1",
    ));
    expect_counterexample(
        &AYEncoder::verify(&ctx),
        "#2778 int Euclidean: (a/3)*3 + a%3 == a+1 is FALSE and must be refuted",
    );
}

/// SHOULD-FAIL: dropping the remainder — `(a/3)*3 == a` — holds only when `a` is
/// a multiple of `3`, so it must be refuted (e.g. `a = 1` gives `0 != 1`). Pins
/// that purification keeps the quotient genuinely floored, not an exact inverse.
#[test]
fn int_div_times_divisor_without_remainder_is_refuted_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", int_ty());
    ctx.push_obligation(ProofObligation::assert(
        "recon_missing_rem",
        "(a / 3) * 3 == a",
    ));
    expect_counterexample(
        &AYEncoder::verify(&ctx),
        "#2778 int Euclidean: (a/3)*3 == a is FALSE for non-multiples of 3 (e.g. a = 1)",
    );
}

/// SOUNDNESS: a SYMBOLIC divisor `b` with NO `b != 0` premise must NOT verify
/// the reconstruction identity — it is genuinely false at `b == 0`, where
/// div/mod stay uninterpreted (`a%0` is unconstrained), so `(a/b)*b + a%b`
/// need not equal `a`. Verus likewise cannot prove this without `b != 0`.
/// With the divisor-guarded lemma instantiation the verdict is now a concrete
/// COUNTEREXAMPLE at `b == 0` (previously fail-closed `Unknown`): the guards
/// make every lemma vacuous there, leaving the solver free to pick
/// `a % 0 != a - (a/0)*0`. Refutation is the correct-direction improvement;
/// the load-bearing half remains "never spuriously Verified".
#[test]
fn int_div_mod_reconstruction_symbolic_divisor_no_premise_refuted() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", int_ty());
    ctx.declare_var_typed("b", int_ty());
    ctx.push_obligation(ProofObligation::assert(
        "recon_symbolic",
        "(a / b) * b + a % b == a",
    ));
    let result = AYEncoder::verify(&ctx);
    expect_not_verified(
        &result,
        "#2778 soundness: symbolic-divisor reconstruction without b != 0 must NOT be Verified",
    );
    expect_counterexample(
        &result,
        "#2778: without b != 0 the reconstruction is falsifiable at b == 0 (div/mod uninterpreted)",
    );
}

// ---------------------------------------------------------------------------
// Divisor-guarded Euclidean lemma instantiation for SYMBOLIC divisors (#2778,
// upstream nonlinear.rs test4 `lemma_div_pos_is_pos` and division-positivity
// shapes). The encoder asserts, per `a / b` / `a % b` occurrence:
//   b != 0 -> a == (a/b)*b + a%b && 0 <= a%b < |b|
//   a >= 0 && b > 0 -> a/b >= 0        (direct quotient-sign lemma)
// leaving a/0, a%0 uninterpreted. Should-verify AND should-fail directions.
// ---------------------------------------------------------------------------

/// SHOULD-VERIFY: upstream nonlinear.rs `test4` (`lemma_div_pos_is_pos`) —
/// `0 <= x && 0 < d ==> 0 <= x / d` with a fully SYMBOLIC divisor. The direct
/// quotient-sign lemma discharges it in pure LIA.
#[test]
fn int_div_pos_dividend_pos_divisor_quotient_nonneg_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", int_ty());
    ctx.declare_var_typed("d", int_ty());
    ctx.push_obligation(ProofObligation::assume("x_nonneg", "x >= 0"));
    ctx.push_obligation(ProofObligation::assume("d_pos", "d > 0"));
    ctx.push_obligation(ProofObligation::assert("q_nonneg", "x / d >= 0"));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778 nonlinear test4: 0 <= x && 0 < d ==> 0 <= x/d (symbolic divisor)",
    );
}

/// SHOULD-VERIFY: Euclidean remainder bounds for a SYMBOLIC positive divisor —
/// `d > 0 ==> 0 <= x % d < d` (division-positivity shape from the guarded
/// remainder-bound lemmas; no sign premise on `x` needed).
#[test]
fn int_mod_symbolic_pos_divisor_bounds_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", int_ty());
    ctx.declare_var_typed("d", int_ty());
    ctx.push_obligation(ProofObligation::assume("d_pos", "d > 0"));
    ctx.push_obligation(ProofObligation::assert(
        "r_bounds",
        "x % d >= 0 && x % d < d",
    ));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778: d > 0 ==> 0 <= x % d < d with a symbolic divisor",
    );
}

/// SHOULD-VERIFY: remainder bounds for a SYMBOLIC NEGATIVE divisor —
/// `d < 0 ==> 0 <= x % d < -d` (exercises the `b < 0 -> r < -b` lemma arm).
#[test]
fn int_mod_symbolic_neg_divisor_bounds_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", int_ty());
    ctx.declare_var_typed("d", int_ty());
    ctx.push_obligation(ProofObligation::assume("d_neg", "d < 0"));
    ctx.push_obligation(ProofObligation::assert(
        "r_bounds_neg",
        "x % d >= 0 && x % d < 0 - d",
    ));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778: d < 0 ==> 0 <= x % d < -d with a symbolic divisor",
    );
}

/// SHOULD-VERIFY: the defining reconstruction `(x/d)*d + x%d == x` now
/// verifies once the `d != 0` premise is supplied (upstream
/// `div_mod_signed_properties` first assertion, symbolic divisor).
#[test]
fn int_div_mod_reconstruction_symbolic_divisor_nonzero_premise_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", int_ty());
    ctx.declare_var_typed("d", int_ty());
    ctx.push_obligation(ProofObligation::assume("d_nonzero", "d != 0"));
    ctx.push_obligation(ProofObligation::assert(
        "recon_symbolic_guarded",
        "(x / d) * d + x % d == x",
    ));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778: d != 0 ==> (x/d)*d + x%d == x with a symbolic divisor",
    );
}

/// SHOULD-FAIL: dropping the `d > 0` premise from the test4 shape —
/// `x >= 0` alone does NOT give `x / d >= 0` (e.g. x = 1, d = -1 has
/// quotient -1). Must not be spuriously Verified.
#[test]
fn int_div_quotient_nonneg_missing_divisor_sign_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", int_ty());
    ctx.declare_var_typed("d", int_ty());
    ctx.push_obligation(ProofObligation::assume("x_nonneg", "x >= 0"));
    ctx.push_obligation(ProofObligation::assert("q_nonneg_bad", "x / d >= 0"));
    expect_not_verified(
        &AYEncoder::verify(&ctx),
        "#2778 should-fail: x >= 0 alone must NOT prove x/d >= 0 (d may be negative or 0)",
    );
}

/// SHOULD-FAIL: dropping the `x >= 0` premise — `d > 0` alone does NOT give
/// `x / d >= 0` (e.g. x = -1, d = 2 has Euclidean quotient -1).
#[test]
fn int_div_quotient_nonneg_missing_dividend_sign_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", int_ty());
    ctx.declare_var_typed("d", int_ty());
    ctx.push_obligation(ProofObligation::assume("d_pos", "d > 0"));
    ctx.push_obligation(ProofObligation::assert("q_nonneg_bad2", "x / d >= 0"));
    expect_not_verified(
        &AYEncoder::verify(&ctx),
        "#2778 should-fail: d > 0 alone must NOT prove x/d >= 0 (x may be negative)",
    );
}

/// SHOULD-FAIL: a FALSE strengthening of the remainder bound — `x % d < d - 1`
/// fails at d == 1 (remainder 0 is not < 0). Pins that the guarded bound
/// lemmas assert exactly `r < d`, nothing stronger.
#[test]
fn int_mod_symbolic_divisor_overtight_bound_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", int_ty());
    ctx.declare_var_typed("d", int_ty());
    ctx.push_obligation(ProofObligation::assume("d_pos", "d > 0"));
    ctx.push_obligation(ProofObligation::assert("r_too_tight", "x % d < d - 1"));
    expect_not_verified(
        &AYEncoder::verify(&ctx),
        "#2778 should-fail: x % d < d - 1 is FALSE at d == 1",
    );
}

/// SOUNDNESS (div-by-zero stays UNINTERPRETED): with `d == 0` assumed, nothing
/// may be concluded about `x / d` — in particular it must NOT equal any
/// specific constant. Verus spec `x/0` is likewise uninterpreted (never folded
/// to 0). Mechanically the assumed zero is const-folded onto the pre-existing
/// literal-division-by-zero Error path (fail-closed); if that fold ever
/// changes, the guarded lemmas are all vacuous at `d == 0`, so the goal still
/// must not verify.
#[test]
fn int_div_by_zero_stays_uninterpreted_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", int_ty());
    ctx.declare_var_typed("d", int_ty());
    ctx.push_obligation(ProofObligation::assume("d_zero", "d == 0"));
    ctx.push_obligation(ProofObligation::assert("div0_pinned", "x / d == 0"));
    expect_not_verified(
        &AYEncoder::verify(&ctx),
        "#2778 soundness: x / 0 is uninterpreted — must NOT be provably 0",
    );
}

/// SOUNDNESS (mod-by-zero stays UNINTERPRETED): same as above for `%` — with
/// `d == 0` assumed, `x % d >= 0` must NOT be provable (SMT-LIB mod-by-zero is
/// unconstrained, even in sign). Same fail-closed const-fold mechanics as the
/// div variant above.
#[test]
fn int_mod_by_zero_stays_uninterpreted_not_verified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", int_ty());
    ctx.declare_var_typed("d", int_ty());
    ctx.push_obligation(ProofObligation::assume("d_zero", "d == 0"));
    ctx.push_obligation(ProofObligation::assert("mod0_pinned", "x % d >= 0"));
    expect_not_verified(
        &AYEncoder::verify(&ctx),
        "#2778 soundness: x % 0 is uninterpreted — even its sign must NOT be provable",
    );
}

/// SHOULD-VERIFY (functional consistency): `x / d == x / d` with NO premise on
/// `d` — so `d == 0` is among the cases — is trivially valid: the SAME
/// `__euclid!div(x, d)` application is equal to itself. Pins that
/// "uninterpreted at zero" means unconstrained, not inconsistent. (A literal
/// `d == 0` *assumption* is const-folded onto the pre-existing
/// division-by-zero Error path instead — fail-closed, exercised by the two
/// `_stays_uninterpreted_` tests above.)
#[test]
fn int_div_symbolic_divisor_self_equality_verifies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", int_ty());
    ctx.declare_var_typed("d", int_ty());
    ctx.push_obligation(ProofObligation::assert("div_self_eq", "x / d == x / d"));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "#2778: x / d == x / d holds for every d, including d == 0",
    );
}

/// AUDITED EXPECTATION FLIP (ay pin 477f3d06d9 -> e043cf975d): the bare
/// perfect-square goal `(a + b) * (a + b) >= 0` now VERIFIES hint-free.
///
/// History: this test (formerly `int_var_times_var_nonlinear_stays_unknown`)
/// pinned `Unknown` — its original concern was the literal-divisor
/// purification accidentally opening the nonlinear gate (an unsoundness
/// vector). What fires now is different and legitimate: the ay NIA rational
/// SOS/Positivstellensatz UNSAT pre-phase (ay a084749365, gated on actual
/// nonlinearity by e05b2c007e) soundly discharges true quadratic-form facts.
/// It is UNSAT-only by construction (it can never fabricate a model), and it
/// extends the default-lane int-NIA capability already pinned by
/// `nia_zero_bound_products`, `arithmetic_normalization`
/// (gcd/commutativity chains), and `regression_math_int`. Unlike `real` —
/// where upstream real.rs `real_nonlinear2` pins the hint-free FAILURE and
/// the `unhinted_nonlinear_real_construct` boundary enforces it — no
/// upstream expected-fail case pins hint-free int failure, so this is a
/// sound capability superset, not a parity break.
///
/// The flip-gate soundness audit lives in
/// `int_var_times_var_nonlinear_negatives_stay_unverified` below.
#[test]
fn int_var_times_var_perfect_square_verifies_via_sos() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", int_ty());
    ctx.declare_var_typed("b", int_ty());
    ctx.push_obligation(ProofObligation::assert(
        "nl_square",
        "(a + b) * (a + b) >= 0",
    ));
    expect_verified(
        &AYEncoder::verify(&ctx),
        "(a+b)*(a+b) >= 0 is a true quadratic-form fact — discharged by the ay NIA \
         SOS/Positivstellensatz UNSAT pre-phase (ay a084749365)",
    );
}

/// SOUNDNESS pins for the SOS pre-phase (the flip-gate audit of
/// `int_var_times_var_perfect_square_verifies_via_sos`): only TRUE
/// quadratic-form theorems may verify. `(a+b)^2 >= 1` is FALSE at `a = -b`
/// and `a*b >= 0` is false at mixed signs — neither may ever be Verified.
#[test]
fn int_var_times_var_nonlinear_negatives_stay_unverified() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", int_ty());
    ctx.declare_var_typed("b", int_ty());
    ctx.push_obligation(ProofObligation::assert(
        "nl_square_off_by_one",
        "(a + b) * (a + b) >= 1",
    ));
    expect_not_verified(
        &AYEncoder::verify(&ctx),
        "#2778 soundness: (a+b)^2 >= 1 is refutable (a = -b) and must NOT verify",
    );

    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("a", int_ty());
    ctx.declare_var_typed("b", int_ty());
    ctx.push_obligation(ProofObligation::assert("nl_bare_product", "a * b >= 0"));
    expect_not_verified(
        &AYEncoder::verify(&ctx),
        "#2778 soundness: a*b >= 0 is refutable (mixed signs) and must NOT verify",
    );
}
