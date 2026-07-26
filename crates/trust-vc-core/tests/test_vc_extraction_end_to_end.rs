// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! End-to-end test demonstrating automatic VC extraction and verification.
//!
//! `verify_function_from_file` now wires function bodies to `result`, so these
//! assertions stay exact to catch regressions in the extraction pipeline.

use std::fs;
use std::path::Path;
use trust_vc_core::vc::{ProofObligation, VerificationContext};
use trust_vc_core::VerifyResult;

#[test]
fn test_end_to_end_vc_extraction() {
    // Create a temporary test file with an annotated function
    let test_dir = Path::new("target/test_vc_extraction_e2e");
    fs::create_dir_all(test_dir).unwrap();

    let test_file = test_dir.join("test.rs");
    let code = r#"
#[trust_vc::proof]
#[trust_vc::requires(n >= 0)]
#[trust_vc::ensures(result == n)]
fn identity(n: i32) -> i32 {
    trust_vc::assert!(n >= 0);
    n
}

#[trust_vc::proof]
#[trust_vc::requires(x < 2147483647)]
#[trust_vc::ensures(result > x)]
fn increment(x: i32) -> i32 {
    x + 1
}
"#;
    fs::write(&test_file, code).unwrap();

    // Test extraction for identity function
    let result = trust_vc_core::verify_function_from_file(test_file.to_str().unwrap(), "identity");

    assert!(
        matches!(result, Ok(VerifyResult::Verified)),
        "identity should verify end-to-end because body->result extraction is wired, got {:?}",
        result
    );

    // Test extraction for increment function
    let result = trust_vc_core::verify_function_from_file(test_file.to_str().unwrap(), "increment");

    assert!(
        matches!(result, Ok(VerifyResult::Verified)),
        "increment should verify end-to-end because body->result extraction is wired, got {:?}",
        result
    );

    // Clean up
    fs::remove_dir_all(test_dir).ok();
}

#[test]
fn test_manual_vc_construction_baseline() {
    // This test shows how VCs work when manually constructed
    // to verify our extraction is on the right track

    let mut ctx = VerificationContext::new();

    // Function: identity(n: i32) -> i32 { n }
    // requires: n >= 0
    // ensures: result == n
    ctx.declare_var_typed("n", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed(
        "result",
        trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"),
    );
    ctx.push_obligation(ProofObligation::assume("requires", "n >= 0"));
    ctx.push_obligation(ProofObligation::assume("body", "result == n")); // This connects body to result
    ctx.push_obligation(ProofObligation::assert("ensures", "result == n"));

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Manual VC construction should verify: {:?}",
        result
    );
}

#[test]
fn test_manual_vc_requires_body_connection() {
    // This manual VC example shows why the body->result assumption is required.

    let mut ctx = VerificationContext::new();

    // Function: increment(x: i32) -> i32 { x + 1 }
    ctx.declare_var_typed("x", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.declare_var_typed(
        "result",
        trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"),
    );
    // Use the direct overflow-prevention bound for the stable BV proof path.
    ctx.push_obligation(ProofObligation::assume("requires", "x < 2147483647"));
    // Without the body->result assumption, verification fails:
    // ctx.push_obligation(ProofObligation::assume("body", "result == x + 1"));
    ctx.push_obligation(ProofObligation::assert("ensures", "result > x"));

    let result = ctx.verify();

    // This should fail because the manual VC omits the body connection.
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "Without body connection, should find counterexample"
    );

    // Now add the body connection
    ctx.push_obligation(ProofObligation::assume("body", "result == x + 1"));
    let result2 = ctx.verify();

    // Now it should verify
    assert!(
        matches!(result2, VerifyResult::Verified),
        "With body connection, should verify"
    );
}
