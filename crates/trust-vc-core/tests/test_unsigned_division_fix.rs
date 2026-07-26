// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Test for unsigned division and remainder fix (#1449)

mod common;

use trust_vc_core::vc::{ProofObligation, VerificationContext};
use trust_vc_core::VerifyResult;

#[test]
fn test_unsigned_division_max_by_two() {
    common::with_clean_verification(|| {
        // Test that u32::MAX / 2 produces correct result
        let mut ctx = VerificationContext::new();

        // Declare unsigned variables
        ctx.declare_var_typed(
            "max_val",
            trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"),
        );
        ctx.declare_var_typed(
            "result",
            trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"),
        );

        // Set max_val to u32::MAX (4294967295)
        ctx.push_obligation(ProofObligation::assume("set_max", "max_val == 4294967295"));

        // Compute result = max_val / 2
        ctx.push_obligation(ProofObligation::assume("divide", "result == max_val / 2"));

        // Assert result should be 2147483647 (u32::MAX / 2)
        ctx.push_obligation(ProofObligation::assert(
            "check_result",
            "result == 2147483647",
        ));

        let result = ctx.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "u32::MAX / 2 should equal 2147483647, got: {:?}",
            result
        );
    })
}

#[test]
fn test_unsigned_remainder() {
    common::with_clean_verification(|| {
        // Test unsigned remainder operation
        let mut ctx = VerificationContext::new();

        // Declare unsigned variables
        ctx.declare_var_typed("a", trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"));
        ctx.declare_var_typed("b", trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"));
        ctx.declare_var_typed(
            "remainder",
            trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"),
        );

        // Set a = 17, b = 5
        ctx.push_obligation(ProofObligation::assume("set_a", "a == 17"));
        ctx.push_obligation(ProofObligation::assume("set_b", "b == 5"));

        // Compute remainder = a % b
        ctx.push_obligation(ProofObligation::assume("compute_rem", "remainder == a % b"));

        // Assert remainder should be 2 (17 % 5 = 2)
        ctx.push_obligation(ProofObligation::assert("check_remainder", "remainder == 2"));

        let result = ctx.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "17 % 5 should equal 2, got: {:?}",
            result
        );
    })
}

#[test]
fn test_unsigned_division_large_values() {
    common::with_clean_verification(|| {
        // Test division with large unsigned values
        let mut ctx = VerificationContext::new();

        // Declare unsigned variables
        ctx.declare_var_typed(
            "large",
            trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"),
        );
        ctx.declare_var_typed(
            "divisor",
            trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"),
        );
        ctx.declare_var_typed(
            "result",
            trust_vc_core::ir::TrustVcType::parse_or_opaque("u32"),
        );

        // Set large = 3000000000 (larger than i32::MAX)
        ctx.push_obligation(ProofObligation::assume("set_large", "large == 3000000000"));
        ctx.push_obligation(ProofObligation::assume("set_divisor", "divisor == 1000"));

        // Compute result = large / divisor
        ctx.push_obligation(ProofObligation::assume(
            "divide",
            "result == large / divisor",
        ));

        // Assert result should be 3000000
        ctx.push_obligation(ProofObligation::assert("check_result", "result == 3000000"));

        let result = ctx.verify();

        assert!(
            matches!(result, VerifyResult::Verified),
            "3000000000 / 1000 should equal 3000000, got: {:?}",
            result
        );
    })
}
