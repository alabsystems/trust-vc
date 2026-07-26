//! Test to diagnose issue #365 - verifier accepting false assertions
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_core::vc::{ProofObligation, VerificationContext};
use trust_vc_core::VerifyResult;

#[test]
fn test_false_should_not_verify() {
    // Create a verification context
    let mut ctx = VerificationContext::new();

    // Add a literally false assertion
    ctx.push_obligation(ProofObligation::assert("false_literal", "false"));

    // Verify it
    let result = ctx.verify();

    // It should NOT verify!
    match result {
        VerifyResult::Verified => {
            panic!("BUG: false assertion verified as true!");
        }
        VerifyResult::Counterexample { .. } => {
            // This is correct
        }
        _ => {
            panic!("Unexpected result: {:?}", result);
        }
    }
}

#[test]
fn test_true_should_verify() {
    // Create a verification context
    let mut ctx = VerificationContext::new();

    // Add a literally true assertion
    ctx.push_obligation(ProofObligation::assert("true_literal", "true"));

    // Verify it
    let result = ctx.verify();

    // It should verify!
    match result {
        VerifyResult::Verified => {
            // This is correct
        }
        VerifyResult::Counterexample { .. } => {
            panic!("BUG: true assertion failed to verify!");
        }
        _ => {
            panic!("Unexpected result: {:?}", result);
        }
    }
}

#[test]
fn test_contradiction_should_not_verify() {
    // Create a verification context
    let mut ctx = VerificationContext::new();

    // Declare a variable
    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

    // Add a contradictory assertion
    ctx.push_obligation(ProofObligation::assert("contradiction", "x > 0 && x < 0"));

    // Verify it
    let result = ctx.verify();

    // It should NOT verify!
    match result {
        VerifyResult::Verified => {
            panic!("BUG: contradiction verified as true!");
        }
        VerifyResult::Counterexample { .. } => {
            // This is correct
        }
        _ => {
            panic!("Unexpected result: {:?}", result);
        }
    }
}

#[test]
fn test_tautology_should_verify() {
    // Create a verification context
    let mut ctx = VerificationContext::new();

    // Declare a variable
    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));

    // Add a tautological assertion
    ctx.push_obligation(ProofObligation::assert("tautology", "x == x"));

    // Verify it
    let result = ctx.verify();

    // It should verify!
    match result {
        VerifyResult::Verified => {
            // This is correct
        }
        VerifyResult::Counterexample { .. } => {
            panic!("BUG: tautology failed to verify!");
        }
        _ => {
            panic!("Unexpected result: {:?}", result);
        }
    }
}
