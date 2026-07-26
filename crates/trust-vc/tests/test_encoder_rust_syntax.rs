// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// Test to demonstrate that the encoder cannot parse Rust syntax (P1 #1118)

use trust_vc_core::vc::VerificationContext;

#[test]
fn test_encoder_cannot_parse_rust_reference_operator() {
    // The encoder expects SMT-LIB-like syntax but macros collect Rust syntax.
    // With the typed preparation path (#1927), the error now occurs during
    // lowering (range expression unsupported) rather than string parsing.

    let mut ctx = VerificationContext::new();

    // Add a Rust expression with reference operator &
    // This is valid Rust: (0..=5).contains(&i)
    ctx.push_assert("rust_reference", "(0..=5).contains(&i)"); // Rust syntax with &
    ctx.declare_var_parsed("i", "i32");

    // Try to verify - should fail with parse error
    let result = ctx.verify();

    // Expected: Error. Depending on which parser path resolves first, this can
    // surface as either typed-lowering unsupported expression or parse failure.
    match result {
        trust_vc_core::VerifyResult::Error { message } => {
            assert!(
                (message.contains("Failed to lower obligation 'rust_reference'")
                    && message.contains("unsupported expression"))
                    || message.contains("Failed to parse 'rust_reference'"),
                "Got different error: {}",
                message
            );
        }
        _ => panic!(
            "Expected error for Rust reference operator, got {:?}",
            result
        ),
    }
}

#[test]
fn test_encoder_cannot_parse_rust_method_calls() {
    // Rust method call syntax is not SMT-LIB

    let mut ctx = VerificationContext::new();

    // Rust method call syntax
    ctx.push_assert("method_call", "s.len() > 0"); // Rust method call

    let result = ctx.verify();

    // Should fail — `s` is unresolved during typed preparation lowering.
    match result {
        trust_vc_core::VerifyResult::Error { message } => {
            assert!(
                message.contains("Failed to lower obligation 'method_call'")
                    && message.contains("unresolved variable `s`"),
                "Got error: {}",
                message
            );
        }
        _ => panic!("Expected error for Rust method call, got {:?}", result),
    }
}

#[test]
fn test_encoder_expects_smt_lib_not_rust() {
    // The fundamental problem: encoder expects SMT-LIB but gets Rust

    // Various Rust syntax that won't parse
    let rust_expressions = vec![
        "x.is_some()",   // Option method
        "vec![1, 2, 3]", // Vec literal
        "Some(x)",       // Enum variant
        "x as i32",      // Type cast
        "x..y",          // Range
        "&mut x",        // Mutable reference
        "x?",            // Try operator
        "x.0",           // Tuple access
    ];

    for expr in rust_expressions {
        let mut ctx = VerificationContext::new();
        let name = format!("rust_{}", expr.replace(|c: char| !c.is_alphanumeric(), "_"));
        ctx.push_assert(&name, expr);

        let result = ctx.verify();

        // All should fail because encoder expects SMT-LIB
        match result {
            trust_vc_core::VerifyResult::Error { .. } => {
                // Expected - encoder can't parse Rust
            }
            _ => {
                panic!(
                    "Encoder unexpectedly parsed Rust syntax '{}': {:?}",
                    expr, result
                );
            }
        }
    }
}

#[test]
fn test_encoder_works_with_smt_lib_like_syntax() {
    // Show that encoder works when given SMT-LIB-like syntax

    let mut ctx = VerificationContext::new();

    // SMT-LIB-like syntax (what encoder expects)
    ctx.push_assert("smt_syntax", "x > 0 && x < 10"); // SMT-LIB style
    ctx.declare_var_parsed("x", "i32");

    // Add assumption that x is 5
    ctx.push_assume("x_equals_5", "x == 5");

    let result = ctx.verify();

    // Should verify successfully with SMT-LIB syntax
    match result {
        trust_vc_core::VerifyResult::Verified => {
            // Good - encoder works with SMT-LIB syntax
        }
        _ => panic!("Encoder failed with SMT-LIB syntax: {:?}", result),
    }
}
