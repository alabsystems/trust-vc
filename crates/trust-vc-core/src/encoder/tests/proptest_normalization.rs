//! Property-based tests for arithmetic normalization.
//!
//! These tests verify that normalization preserves semantic meaning:
//! rewriting expressions should not change whether they verify.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use proptest::prelude::*;

proptest! {
    /// Addition is commutative: a + b == b + a always verifies.
    #[test]
    fn prop_addition_commutative(a in -1000i32..1000, b in -1000i32..1000) {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("a", i32_ty());
        ctx.declare_var_typed("b", i32_ty());
        ctx.push_assume("a_value", &format!("a == {a}"));
        ctx.push_assume("b_value", &format!("b == {b}"));
        ctx.push_obligation(ProofObligation::assert("commutative", "a + b == b + a"));

        let result = ctx.verify();

        prop_assert!(
            matches!(result, VerifyResult::Verified),
            "Failed for a={a}, b={b}: {result:?}",
        );
    }

    /// Multiplication distributes over addition: a*(b+c) == a*b + a*c.
    #[test]
    fn prop_mul_distributes_over_add(
        a in -100i32..100,
        b in -100i32..100,
        c in -100i32..100,
    ) {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("a", i32_ty());
        ctx.declare_var_typed("b", i32_ty());
        ctx.declare_var_typed("c", i32_ty());
        ctx.push_assume("a_value", &format!("a == {a}"));
        ctx.push_assume("b_value", &format!("b == {b}"));
        ctx.push_assume("c_value", &format!("c == {c}"));
        ctx.push_assume("mul_sum_lo", "a * (b + c) >= -2147483648");
        ctx.push_assume("mul_sum_hi", "a * (b + c) <= 2147483647");
        ctx.push_assume("sum_mul_lo", "a * b + a * c >= -2147483648");
        ctx.push_assume("sum_mul_hi", "a * b + a * c <= 2147483647");
        ctx.push_assume("mul_ab_lo", "a * b >= -2147483648");
        ctx.push_assume("mul_ab_hi", "a * b <= 2147483647");
        ctx.push_assume("mul_ac_lo", "a * c >= -2147483648");
        ctx.push_assume("mul_ac_hi", "a * c <= 2147483647");
        ctx.push_assume("sum_bc_lo", "b + c >= -2147483648");
        ctx.push_assume("sum_bc_hi", "b + c <= 2147483647");
        ctx.push_obligation(ProofObligation::assert(
            "distributive",
            "a * (b + c) == a * b + a * c",
        ));

        let result = ctx.verify();

        prop_assert!(
            matches!(result, VerifyResult::Verified),
            "Failed for a={a}, b={b}, c={c}: {result:?}",
        );
    }

    /// Double negation: -(-a) == a.
    #[test]
    fn prop_double_negation(a in -2147483647i32..2147483647) {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("a", i32_ty());
        ctx.push_assume("a_value", &format!("a == {a}"));
        ctx.push_obligation(ProofObligation::assert("double_neg", "-(-a) == a"));

        let result = ctx.verify();

        prop_assert!(
            matches!(result, VerifyResult::Verified),
            "Failed for a={a}: {result:?}",
        );
    }

    /// Subtraction identity: a - a == 0.
    #[test]
    fn prop_sub_self_is_zero(a in -1000i32..1000) {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("a", i32_ty());
        ctx.push_assume("a_value", &format!("a == {a}"));
        ctx.push_obligation(ProofObligation::assert("sub_self", "a - a == 0"));

        let result = ctx.verify();

        prop_assert!(
            matches!(result, VerifyResult::Verified),
            "Failed for a={a}: {result:?}",
        );
    }

    /// Adding zero: a + 0 == a.
    #[test]
    fn prop_add_zero_identity(a in -1000i32..1000) {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("a", i32_ty());
        ctx.push_assume("a_value", &format!("a == {a}"));
        ctx.push_obligation(ProofObligation::assert("add_zero", "a + 0 == a"));

        let result = ctx.verify();

        prop_assert!(
            matches!(result, VerifyResult::Verified),
            "Failed for a={a}: {result:?}",
        );
    }

    /// Multiplying by one: a * 1 == a.
    #[test]
    fn prop_mul_one_identity(a in -1000i32..1000) {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("a", i32_ty());
        ctx.push_assume("a_value", &format!("a == {a}"));
        ctx.push_obligation(ProofObligation::assert("mul_one", "a * 1 == a"));

        let result = ctx.verify();

        prop_assert!(
            matches!(result, VerifyResult::Verified),
            "Failed for a={a}: {result:?}",
        );
    }

    /// Multiplying by zero: a * 0 == 0.
    #[test]
    fn prop_mul_zero(a in -1000i32..1000) {
        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("a", i32_ty());
        ctx.push_assume("a_value", &format!("a == {a}"));
        ctx.push_obligation(ProofObligation::assert("mul_zero", "a * 0 == 0"));

        let result = ctx.verify();

        prop_assert!(
            matches!(result, VerifyResult::Verified),
            "Failed for a={a}: {result:?}",
        );
    }

    /// Order preserved: if a < b then a + 1 <= b (in-range values).
    #[test]
    fn prop_less_implies_plus_one_leq(a in -1000i32..999, b in -999i32..1000) {
        prop_assume!(a < b);

        let mut ctx = VerificationContext::new();
        ctx.declare_var_typed("a", i32_ty());
        ctx.declare_var_typed("b", i32_ty());
        ctx.push_assume("a_value", &format!("a == {a}"));
        ctx.push_assume("b_value", &format!("b == {b}"));
        ctx.push_assume("ordered", "a < b");
        ctx.push_obligation(ProofObligation::assert("order", "a + 1 <= b"));

        let result = ctx.verify();

        prop_assert!(
            matches!(result, VerifyResult::Verified),
            "Failed for a={a}, b={b}: {result:?}",
        );
    }
}
