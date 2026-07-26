// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Differential testing harness for ay soundness verification.
//!
//! Instead of comparing ay against Z3 (which is not available in this pure-Rust
//! codebase), each test case uses known mathematical truths as the oracle:
//! tautologies must verify, contradictions must produce counterexamples.
//!
//! Coverage: arithmetic identities, boolean tautologies, bitvector properties,
//! real arithmetic, quantifier soundness, comparison chains, mixed-theory queries,
//! and collection axioms.
//!
//! Part of #2735.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ============================================================================
// Harness infrastructure
// ============================================================================

/// A differential test case records an input and the expected verification outcome.
struct DifferentialCase {
    name: &'static str,
    setup: fn(&mut VerificationContext),
    expected: ExpectedOutcome,
}

#[derive(Clone, Copy)]
enum ExpectedOutcome {
    /// The assertion is a known tautology — ay must confirm.
    Verified,
    /// The assertion is valid, but current ay-dpll support may still return
    /// Unknown on harder quantifier shapes.
    VerifiedOrUnknown,
    /// The assertion is false or not universally true — ay must refute.
    Counterexample,
    /// ay should reject (counterexample or unknown) — the assertion is invalid.
    FailClosed,
    /// The query is malformed — ay should report an encoding error.
    Error,
}

/// A named test case builder that constructs a `(VerificationContext, ExpectedOutcome)` pair.
type OverflowTestCase<'a> = Vec<(
    &'a str,
    Box<dyn Fn() -> (VerificationContext, ExpectedOutcome)>,
)>;

fn run_differential_cases(cases: &[DifferentialCase]) {
    for case in cases {
        let mut ctx = VerificationContext::new();
        (case.setup)(&mut ctx);
        let result = AYEncoder::verify(&ctx);
        match case.expected {
            ExpectedOutcome::Verified => expect_verified(&result, case.name),
            ExpectedOutcome::VerifiedOrUnknown => expect_verified_or_unknown(&result, case.name),
            ExpectedOutcome::Counterexample => expect_counterexample(&result, case.name),
            ExpectedOutcome::FailClosed => expect_fail_closed(&result, case.name),
            ExpectedOutcome::Error => expect_error(&result, case.name),
        }
    }
}

// ============================================================================
// 1. Arithmetic identities (i32)
// ============================================================================

#[test]
fn test_differential_arithmetic_suite() {
    let cases = vec![
        DifferentialCase {
            name: "1 + 1 == 2",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.push_obligation(ProofObligation::assume("val", "x == 1"));
                ctx.push_obligation(ProofObligation::assert("check", "x + 1 == 2"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "1 + 1 != 3 (counterexample)",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.push_obligation(ProofObligation::assume("val", "x == 1"));
                ctx.push_obligation(ProofObligation::assert("check", "x + 1 == 3"));
            },
            expected: ExpectedOutcome::Counterexample,
        },
        DifferentialCase {
            name: "additive identity: x + 0 == x",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.push_obligation(ProofObligation::assert("add_id", "x + 0 == x"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "additive commutativity: x + y == y + x",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.push_obligation(ProofObligation::assert("add_comm", "x + y == y + x"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "multiplicative identity: x * 1 == x",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.push_obligation(ProofObligation::assert("mul_id", "x * 1 == x"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "multiplicative annihilation: x * 0 == 0",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.push_obligation(ProofObligation::assert("mul_zero", "x * 0 == 0"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "subtraction self: x - x == 0",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.push_obligation(ProofObligation::assert("sub_self", "x - x == 0"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "negation double: -(-x) == x",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i8"));
                ctx.push_obligation(ProofObligation::assume("no_min", "x != -128i8"));
                ctx.push_obligation(ProofObligation::assert("double_neg", "-(-x) == x"));
            },
            expected: ExpectedOutcome::Verified,
        },
    ];
    run_differential_cases(&cases);
}

// ============================================================================
// 2. Boolean tautologies and contradictions
// ============================================================================

#[test]
fn test_differential_boolean_suite() {
    let cases = vec![
        DifferentialCase {
            name: "double negation: !!b == b",
            setup: |ctx| {
                ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("bool"));
                ctx.push_obligation(ProofObligation::assert("double_not", "!!b == b"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "excluded middle: b || !b",
            setup: |ctx| {
                ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("bool"));
                ctx.push_obligation(ProofObligation::assert("excluded_middle", "b || !b"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "contradiction: b && !b",
            setup: |ctx| {
                ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("bool"));
                ctx.push_obligation(ProofObligation::assert("contradiction", "b && !b"));
            },
            expected: ExpectedOutcome::Counterexample,
        },
        DifferentialCase {
            name: "modus ponens: (x > 5) implies (x > 0)",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.push_obligation(ProofObligation::assume("x_gt_5", "x > 5"));
                ctx.push_obligation(ProofObligation::assert("implication", "!(x > 5) || x > 0"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "De Morgan: !(a && b) equiv (!a || !b)",
            setup: |ctx| {
                ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("bool"));
                ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("bool"));
                // assert !(a && b) == (!a || !b) indirectly:
                // assume !(a && b), then check !a || !b
                ctx.push_obligation(ProofObligation::assume("de_morgan_lhs", "!(a && b)"));
                ctx.push_obligation(ProofObligation::assert("de_morgan_rhs", "!a || !b"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "De Morgan converse: (!a || !b) implies !(a && b)",
            setup: |ctx| {
                ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("bool"));
                ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("bool"));
                ctx.push_obligation(ProofObligation::assume("de_morgan_rhs", "!a || !b"));
                ctx.push_obligation(ProofObligation::assert("de_morgan_lhs", "!(a && b)"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "idempotence of conjunction: a && a == a",
            setup: |ctx| {
                ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("bool"));
                ctx.push_obligation(ProofObligation::assume("a_true", "a"));
                ctx.push_obligation(ProofObligation::assert("idem_and", "a && a"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "idempotence of disjunction: a || a implies a",
            setup: |ctx| {
                ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("bool"));
                ctx.push_obligation(ProofObligation::assume("disj", "a || a"));
                ctx.push_obligation(ProofObligation::assert("idem_or", "a"));
            },
            expected: ExpectedOutcome::Verified,
        },
    ];
    run_differential_cases(&cases);
}

// ============================================================================
// 3. Comparison chains and transitivity
// ============================================================================

#[test]
fn test_differential_comparison_suite() {
    let cases = vec![
        DifferentialCase {
            name: "i32(5) < i64(10) — cross-width comparison",
            setup: |ctx| {
                ctx.declare_var_typed("small", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.declare_var_typed("big", crate::ir::TrustVcType::parse_or_opaque("i64"));
                ctx.push_obligation(ProofObligation::assume("small_val", "small == 5"));
                ctx.push_obligation(ProofObligation::assume("big_val", "big == 10"));
                ctx.push_obligation(ProofObligation::assert("compare", "small < big"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "u8(200) == u32(200) — cross-width equality",
            setup: |ctx| {
                ctx.declare_var_typed("small", crate::ir::TrustVcType::parse_or_opaque("u8"));
                ctx.declare_var_typed("big", crate::ir::TrustVcType::parse_or_opaque("u32"));
                ctx.push_obligation(ProofObligation::assume("small_val", "small == 200"));
                ctx.push_obligation(ProofObligation::assume("big_val", "big == 200"));
                ctx.push_obligation(ProofObligation::assert(
                    "equal_after_promotion",
                    "small == big",
                ));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "x < 0 when x == 5 (counterexample)",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.push_obligation(ProofObligation::assume("x_val", "x == 5"));
                ctx.push_obligation(ProofObligation::assert("negative", "x < 0"));
            },
            expected: ExpectedOutcome::Counterexample,
        },
        DifferentialCase {
            name: "transitivity: a < b && b < c implies a < c",
            setup: |ctx| {
                ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.declare_var_typed("c", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.push_obligation(ProofObligation::assume("a_lt_b", "a < b"));
                ctx.push_obligation(ProofObligation::assume("b_lt_c", "b < c"));
                ctx.push_obligation(ProofObligation::assert("a_lt_c", "a < c"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "reflexivity: x == x",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.push_obligation(ProofObligation::assert("reflexive", "x == x"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "anti-symmetry: a <= b && b <= a implies a == b",
            setup: |ctx| {
                ctx.declare_var_typed("a", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.declare_var_typed("b", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.push_obligation(ProofObligation::assume("a_le_b", "a <= b"));
                ctx.push_obligation(ProofObligation::assume("b_le_a", "b <= a"));
                ctx.push_obligation(ProofObligation::assert("a_eq_b", "a == b"));
            },
            expected: ExpectedOutcome::Verified,
        },
    ];
    run_differential_cases(&cases);
}

// ============================================================================
// 4. Bitvector properties (u8 to avoid solver timeouts)
// ============================================================================

#[test]
fn test_differential_bitvector_suite() {
    let cases = vec![
        DifferentialCase {
            name: "bv: x & 0 == 0 (bitwise AND with zero)",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
                ctx.push_obligation(ProofObligation::assert("and_zero", "x & 0 == 0"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "bv: x | 0 == x (bitwise OR identity)",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
                ctx.push_obligation(ProofObligation::assert("or_zero", "(x | 0) == x"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "bv: x ^ x == 0 (XOR self cancellation)",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
                ctx.push_obligation(ProofObligation::assert("xor_self", "(x ^ x) == 0"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "bv: x & x == x (AND idempotence)",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
                ctx.push_obligation(ProofObligation::assert("and_idem", "(x & x) == x"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "bv: x | x == x (OR idempotence)",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
                ctx.push_obligation(ProofObligation::assert("or_idem", "(x | x) == x"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "bv: u8 wrapping — 255 + 1 wraps to 0",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
                ctx.push_obligation(ProofObligation::assume("max_val", "x == 255"));
                ctx.push_obligation(ProofObligation::assert("wrap", "x + 1 == 0"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "bv: u8 upper bound — x <= 255 always holds",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
                ctx.push_obligation(ProofObligation::assert("upper_bound", "x <= 255"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "bv: u8 non-negative — x >= 0 always holds",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
                ctx.push_obligation(ProofObligation::assert("non_neg", "x >= 0"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "bv: x & 255 == x for u8 (all-ones mask)",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u8"));
                ctx.push_obligation(ProofObligation::assert("mask_all", "(x & 255) == x"));
            },
            expected: ExpectedOutcome::Verified,
        },
    ];
    run_differential_cases(&cases);
}

// ============================================================================
// 5. Quantifier soundness
// ============================================================================

#[test]
fn test_differential_quantifier_suite() {
    let cases = vec![
        DifferentialCase {
            name: "forall: reflexivity — forall(|x: i32| x == x)",
            setup: |ctx| {
                ctx.push_obligation(ProofObligation::assert(
                    "reflexivity",
                    "forall(|x: i32| x == x)",
                ));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "forall: commutativity — forall(|x: i32, y: i32| x + y == y + x)",
            setup: |ctx| {
                ctx.push_obligation(ProofObligation::assert(
                    "commutativity",
                    "forall(|x: i32, y: i32| x + y == y + x)",
                ));
            },
            expected: ExpectedOutcome::VerifiedOrUnknown,
        },
        DifferentialCase {
            name: "forall: false universal — forall(|x: i32| x > 0)",
            setup: |ctx| {
                ctx.push_obligation(ProofObligation::assert(
                    "all_positive",
                    "forall(|x: i32| x > 0)",
                ));
            },
            expected: ExpectedOutcome::FailClosed,
        },
        DifferentialCase {
            name: "exists: no witness — exists(|x: i32| x != x)",
            setup: |ctx| {
                ctx.push_obligation(ProofObligation::assert(
                    "no_witness",
                    "exists(|x: i32| x != x)",
                ));
            },
            expected: ExpectedOutcome::FailClosed,
        },
        DifferentialCase {
            name: "forall: bad type — forall(|x: Vec<i32>| x == x)",
            setup: |ctx| {
                ctx.push_obligation(ProofObligation::assert(
                    "bad_type",
                    "forall(|x: Vec<i32>| x == x)",
                ));
            },
            expected: ExpectedOutcome::Error,
        },
    ];
    run_differential_cases(&cases);
}

// ============================================================================
// 6. Real arithmetic identities
// ============================================================================

#[test]
fn test_differential_real_arithmetic_suite() {
    let cases = vec![
        DifferentialCase {
            name: "real: x + 0 == x (additive identity)",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("real"));
                ctx.push_obligation(ProofObligation::assert("real_add_id", "x + 0 == x"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "real: x * 1 == x (multiplicative identity)",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("real"));
                ctx.push_obligation(ProofObligation::assert("real_mul_id", "x * 1 == x"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "real: x - x == 0 (additive inverse)",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("real"));
                ctx.push_obligation(ProofObligation::assert("real_sub_self", "x - x == 0"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "real: -x + x == 0 (negation cancellation)",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("real"));
                ctx.push_obligation(ProofObligation::assert("real_neg_cancel", "-x + x == 0"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "real: x > 0 implies x + 1 > 1 (monotonicity)",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("real"));
                ctx.push_obligation(ProofObligation::assume("x_pos", "x > 0"));
                ctx.push_obligation(ProofObligation::assert("mono", "x + 1 > 1"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "real: x * 0 == 0 (annihilation)",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("real"));
                ctx.push_obligation(ProofObligation::assert("real_mul_zero", "x * 0 == 0"));
            },
            expected: ExpectedOutcome::Verified,
        },
    ];
    run_differential_cases(&cases);
}

// ============================================================================
// 7. Mixed-theory interactions
// ============================================================================

#[test]
fn test_differential_mixed_theory_suite() {
    let cases = vec![
        DifferentialCase {
            name: "mixed: bool from comparison — (x > 5) == (x > 5)",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.push_obligation(ProofObligation::assert("cmp_refl", "(x > 5) == (x > 5)"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "mixed: arithmetic in bool context — (x + 1 > x)",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i8"));
                ctx.push_obligation(ProofObligation::assume("no_overflow", "x < 127i8"));
                ctx.push_obligation(ProofObligation::assert("succ_gt", "x + 1 > x"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "mixed: trichotomy — x < y || x == y || x > y",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.push_obligation(ProofObligation::assert(
                    "trichotomy",
                    "x < y || x == y || x > y",
                ));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "mixed: !(x < y && x > y) — comparisons are exclusive",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.push_obligation(ProofObligation::assert(
                    "exclusive_cmp",
                    "!(x < y && x > y)",
                ));
            },
            expected: ExpectedOutcome::Verified,
        },
    ];
    run_differential_cases(&cases);
}

// ============================================================================
// 8. Unsigned arithmetic edge cases
// ============================================================================

#[test]
fn test_differential_unsigned_edge_cases() {
    let cases = vec![
        DifferentialCase {
            name: "u32: 0 is the minimum",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
                ctx.push_obligation(ProofObligation::assert("u32_min", "x >= 0"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "u32: x < x is always false (counterexample)",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
                ctx.push_obligation(ProofObligation::assert("strict_lt_self", "x < x"));
            },
            expected: ExpectedOutcome::Counterexample,
        },
        DifferentialCase {
            name: "u32: x <= x is always true",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("u32"));
                ctx.push_obligation(ProofObligation::assert("le_self", "x <= x"));
            },
            expected: ExpectedOutcome::Verified,
        },
    ];
    run_differential_cases(&cases);
}

// ============================================================================
// 9. Signed integer edge cases
// ============================================================================

#[test]
fn test_differential_signed_edge_cases() {
    let cases = vec![
        DifferentialCase {
            name: "i8: range check — x >= -128 always holds",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i8"));
                ctx.push_obligation(ProofObligation::assert("i8_min", "x >= -128i8"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "i8: range check — x <= 127 always holds",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i8"));
                ctx.push_obligation(ProofObligation::assert("i8_max", "x <= 127i8"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "i8: -1 * -1 == 1",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i8"));
                ctx.push_obligation(ProofObligation::assume("neg_one", "x == -1i8"));
                ctx.push_obligation(ProofObligation::assert("neg_neg", "x * x == 1"));
            },
            expected: ExpectedOutcome::Verified,
        },
    ];
    run_differential_cases(&cases);
}

// ============================================================================
// 10. Implication and conditional reasoning
// ============================================================================

#[test]
fn test_differential_implication_suite() {
    let cases = vec![
        DifferentialCase {
            name: "contrapositive: (a implies b) iff (!b implies !a)",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
                // If x > 10 then x > 5. Contrapositive: if x <= 5 then x <= 10.
                ctx.push_obligation(ProofObligation::assume("x_le_5", "x <= 5"));
                ctx.push_obligation(ProofObligation::assert("x_le_10", "x <= 10"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "strengthening: x == 5 implies x >= 0",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.push_obligation(ProofObligation::assume("exact", "x == 5"));
                ctx.push_obligation(ProofObligation::assert("weaker", "x >= 0"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "chain: x > 0 && x < 10 implies x >= 1 && x <= 9",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.push_obligation(ProofObligation::assume("lower", "x > 0"));
                ctx.push_obligation(ProofObligation::assume("upper", "x < 10"));
                ctx.push_obligation(ProofObligation::assert("tight_lower", "x >= 1"));
            },
            expected: ExpectedOutcome::Verified,
        },
        DifferentialCase {
            name: "chain: x > 0 && x < 10 implies x <= 9",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.push_obligation(ProofObligation::assume("lower", "x > 0"));
                ctx.push_obligation(ProofObligation::assume("upper", "x < 10"));
                ctx.push_obligation(ProofObligation::assert("tight_upper", "x <= 9"));
            },
            expected: ExpectedOutcome::Verified,
        },
    ];
    run_differential_cases(&cases);
}

// ============================================================================
// 11. Overflow and boundary soundness (with overflow checks enabled)
// ============================================================================

#[test]
fn test_differential_overflow_boundary_suite() {
    // These tests use with_overflow_checks() to verify overflow detection
    let cases: OverflowTestCase<'_> = vec![
        (
            "overflow: i8 addition at boundary is detected",
            Box::new(|| {
                let mut ctx = VerificationContext::new().with_overflow_checks();
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i8"));
                ctx.push_obligation(ProofObligation::assume("at_max", "x == 127i8"));
                ctx.push_obligation(ProofObligation::assert("overflow_add", "x + 1 > 0"));
                (ctx, ExpectedOutcome::FailClosed)
            }),
        ),
        (
            "overflow: safe i8 addition verifies",
            Box::new(|| {
                let mut ctx = VerificationContext::new().with_overflow_checks();
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i8"));
                ctx.push_obligation(ProofObligation::assume("safe", "x == 1i8"));
                ctx.push_obligation(ProofObligation::assert("safe_add", "x + 1 == 2"));
                (ctx, ExpectedOutcome::Verified)
            }),
        ),
    ];

    for (name, builder) in &cases {
        let (ctx, expected) = builder();
        let result = AYEncoder::verify(&ctx);
        match expected {
            ExpectedOutcome::Verified => expect_verified(&result, name),
            ExpectedOutcome::VerifiedOrUnknown => expect_verified_or_unknown(&result, name),
            ExpectedOutcome::Counterexample => expect_counterexample(&result, name),
            ExpectedOutcome::FailClosed => expect_fail_closed(&result, name),
            ExpectedOutcome::Error => expect_error(&result, name),
        }
    }
}

// ============================================================================
// 12. Soundness negative tests — known false claims must NOT verify
// ============================================================================

#[test]
fn test_differential_soundness_negative_suite() {
    let cases = vec![
        DifferentialCase {
            name: "soundness: x > 0 is not universally true for i32",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.push_obligation(ProofObligation::assert("false_claim", "x > 0"));
            },
            expected: ExpectedOutcome::Counterexample,
        },
        DifferentialCase {
            name: "soundness: x == y is not universally true",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.declare_var_typed("y", crate::ir::TrustVcType::parse_or_opaque("i32"));
                ctx.push_obligation(ProofObligation::assert("false_eq", "x == y"));
            },
            expected: ExpectedOutcome::Counterexample,
        },
        DifferentialCase {
            name: "soundness: x + 1 == x is never true",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("i8"));
                // x + 1 == x is false for all x where x + 1 doesn't overflow
                ctx.push_obligation(ProofObligation::assume("no_overflow", "x < 127i8"));
                ctx.push_obligation(ProofObligation::assert("absurd", "x + 1 == x"));
            },
            expected: ExpectedOutcome::Counterexample,
        },
        DifferentialCase {
            name: "soundness: false literal should produce counterexample",
            setup: |ctx| {
                ctx.declare_var_typed("x", crate::ir::TrustVcType::parse_or_opaque("bool"));
                ctx.push_obligation(ProofObligation::assume("x_true", "x"));
                ctx.push_obligation(ProofObligation::assert("assert_false", "!x"));
            },
            expected: ExpectedOutcome::Counterexample,
        },
    ];
    run_differential_cases(&cases);
}
