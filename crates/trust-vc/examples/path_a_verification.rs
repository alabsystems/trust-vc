//! Example showing Path A (direct VerificationContext API) - the CORRECT approach
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This demonstrates the correct way to use trust_vc verification after the
//! architectural pivot in #397. Path B (macro-based) has been deleted because
//! it fundamentally cannot work with ay's requirements.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

/// Example 1: Simple assertion verification
fn verify_simple_assertion() {
    println!("Example 1: Verifying x + 0 == x");

    let mut ctx = VerificationContext::new();

    // CRITICAL: Must explicitly declare ALL variables to ay
    ctx.declare_var_parsed("x", "i32");

    // Add the assertion to verify
    ctx.push_assert("identity", "x + 0 == x");

    // Verify using ay
    match ctx.verify() {
        VerifyResult::Verified => {
            println!("  ✓ Verified: x + 0 == x holds for all x");
        }
        _ => {
            println!("  ✗ Failed to verify");
        }
    }
}

/// Example 2: Preconditions and assertions
fn verify_with_precondition() {
    println!("\nExample 2: Verifying with precondition");

    let mut ctx = VerificationContext::new();

    // Declare variables.
    //
    // We use `int` (Verus's unbounded mathematical integer) rather than `i32`.
    // For a bounded `i32`, `x + 1` wraps at `i32::MAX`, so `x > 0 ==> x + 1 > 1`
    // is genuinely FALSE at the boundary (x = i32::MAX makes x + 1 negative) and
    // ay correctly reports that counterexample. The mathematical claim we want to
    // demonstrate holds over `int`, which models reasoning without overflow.
    ctx.declare_var_parsed("x", "int");

    // Add precondition (assumption)
    ctx.push_assume("precondition", "x > 0");

    // Add assertion that should hold given the precondition
    ctx.push_assert("consequence", "x + 1 > 1");

    match ctx.verify() {
        VerifyResult::Verified => {
            println!("  ✓ Verified: if x > 0, then x + 1 > 1");
        }
        _ => {
            println!("  ✗ Failed to verify");
        }
    }
}

/// Example 3: Local variables (the Path B problem)
fn verify_with_local_variables() {
    println!("\nExample 3: Handling local variables correctly");

    let mut ctx = VerificationContext::new();

    // In Path B, this would fail because y was never declared
    // In Path A, we explicitly declare ALL variables.
    //
    // `int` (unbounded) keeps this a pure mathematical fact: over `i32`,
    // `y == x + 1` overflows at x = i32::MAX (y wraps negative, so y > x fails).
    ctx.declare_var_parsed("x", "int");
    ctx.declare_var_parsed("y", "int"); // CRITICAL: Must declare locals too!

    // Define the relationship between variables
    ctx.push_assume("y_definition", "y == x + 1");

    // Now we can use y in assertions
    ctx.push_assert("y_greater", "y > x");

    match ctx.verify() {
        VerifyResult::Verified => {
            println!("  ✓ Verified: if y = x + 1, then y > x");
        }
        _ => {
            println!("  ✗ Failed to verify");
        }
    }
}

/// Example 4: Finding counterexamples
fn verify_false_assertion() {
    println!("\nExample 4: Finding counterexamples for false assertions");

    let mut ctx = VerificationContext::new();

    ctx.declare_var_parsed("x", "i32");

    // This is false - x could be 0
    ctx.push_assert("false_claim", "x > 0");

    match ctx.verify() {
        VerifyResult::Counterexample {
            obligation_name,
            model,
            ..
        } => {
            println!("  ✓ Found counterexample for '{}'", obligation_name);
            if let Some(m) = model {
                println!("    Model: {}", m);
            }
        }
        VerifyResult::Verified => {
            println!("  ✗ Incorrectly verified a false assertion!");
        }
        _ => {
            println!("  ? Unknown result");
        }
    }
}

/// Example 5: Multiple assertions
fn verify_multiple_assertions() {
    println!("\nExample 5: Verifying multiple assertions");

    let mut ctx = VerificationContext::new();

    // `int` keeps the chained algebra exact: with `i32`, `b == a * 2` and
    // `c == a * 3` overflow for large `a`, so `b > 0` / `c == a * 3` would have
    // legitimate wraparound counterexamples. Over `int` these are clean facts.
    ctx.declare_var_parsed("a", "int");
    ctx.declare_var_parsed("b", "int");
    ctx.declare_var_parsed("c", "int");

    // Set up relationships
    ctx.push_assume("a_positive", "a > 0");
    ctx.push_assume("b_def", "b == a * 2");
    ctx.push_assume("c_def", "c == b + a");

    // Multiple assertions to verify
    ctx.push_assert("b_positive", "b > 0");
    ctx.push_assert("c_greater", "c > b");
    ctx.push_assert("c_triple", "c == a * 3");

    match ctx.verify() {
        VerifyResult::Verified => {
            println!("  ✓ All assertions verified");
        }
        VerifyResult::Counterexample {
            obligation_name, ..
        } => {
            println!("  ✗ Failed on assertion: {}", obligation_name);
        }
        _ => {
            println!("  ? Unknown result");
        }
    }
}

fn main() {
    println!("Path A Verification Examples");
    println!("============================");
    println!("This is the CORRECT way to use trust_vc after architectural pivot #397\n");

    verify_simple_assertion();
    verify_with_precondition();
    verify_with_local_variables();
    verify_false_assertion();
    verify_multiple_assertions();

    println!("\nKey Points:");
    println!("- Always use explicit VerificationContext");
    println!("- Declare ALL variables (including locals) to ay");
    println!("- Use string-based assertions that ay can parse");
    println!("- No macros, no thread-local state, no magic");
}
