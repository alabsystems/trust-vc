//! Basic trust_vc verification examples using Path A (direct API)
//!
//! This example demonstrates simple contracts (requires/ensures) and assertions
//! using the direct VerificationContext API. This is the correct approach after
//! the architectural pivot - macros cannot access compiler internals.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

/// Example 1: Simple precondition and postcondition verification
///
/// This demonstrates how to verify that if x > 0, then x + 1 > x
fn verify_increment() {
    println!("Example 1: Verifying increment function contract");

    let mut ctx = VerificationContext::new();

    // Declare the input variable.
    //
    // We model with `int` (Verus's unbounded mathematical integer), not `i32`.
    // Over a 32-bit `i32`, `x + 1` wraps at `i32::MAX`, so `result > x` has a real
    // overflow counterexample (x = i32::MAX -> result = i32::MIN) that ay reports
    // correctly. The contract we mean to teach ("incrementing grows the value")
    // is a fact about mathematical integers, so we encode it over `int`.
    ctx.declare_var_parsed("x", "int");

    // Add precondition: x > 0
    ctx.push_assume("requires", "x > 0");

    // Model the computation: result = x + 1
    ctx.declare_var_parsed("result", "int");
    ctx.push_assume("computation", "result == x + 1");

    // Add postcondition to verify: result > x
    ctx.push_assert("ensures", "result > x");

    match ctx.verify() {
        VerifyResult::Verified => {
            println!("  ✓ Verified: if x > 0, then x + 1 > x");
        }
        VerifyResult::Counterexample {
            obligation_name,
            model,
            ..
        } => {
            println!("  ✗ Counterexample for {}: {:?}", obligation_name, model);
        }
        _ => {
            println!("  ? Unknown result");
        }
    }
}

/// Example 2: Multiple preconditions verification
///
/// Verifies that multiplying two positive numbers gives a positive result
fn verify_multiply_positive() {
    println!("\nExample 2: Verifying multiplication of positives");

    let mut ctx = VerificationContext::new();

    // Declare variables over `int`: `positive * positive > 0` is a fact about
    // mathematical integers. For `i32` it is false under wraparound
    // (e.g. i32::MAX * 2 wraps negative), which ay would (correctly) refute.
    ctx.declare_var_parsed("x", "int");
    ctx.declare_var_parsed("y", "int");
    ctx.declare_var_parsed("result", "int");

    // Add preconditions (both must be positive)
    ctx.push_assume("x_positive", "x > 0");
    ctx.push_assume("y_positive", "y > 0");

    // Model the computation
    ctx.push_assume("computation", "result == x * y");

    // Verify postcondition
    ctx.push_assert("result_positive", "result > 0");

    match ctx.verify() {
        VerifyResult::Verified => {
            println!("  ✓ Verified: positive × positive = positive");
        }
        VerifyResult::Counterexample {
            obligation_name,
            model,
            ..
        } => {
            println!("  ✗ Counterexample for {}: {:?}", obligation_name, model);
        }
        _ => {
            println!("  ? Unknown result");
        }
    }
}

/// Example 3: Counter increment with old value reference
///
/// Demonstrates verifying state changes by referencing old values
fn verify_counter_increment() {
    println!("\nExample 3: Verifying counter increment");

    let mut ctx = VerificationContext::new();

    // Declare variables for old and new counter states over `int`. Adding a
    // positive amount strictly grows the counter as a mathematical fact; an
    // `i32` counter near `i32::MAX` would wrap, which ay would refute.
    ctx.declare_var_parsed("counter_old", "int");
    ctx.declare_var_parsed("counter_new", "int");
    ctx.declare_var_parsed("amount", "int");

    // Precondition: amount > 0
    ctx.push_assume("amount_positive", "amount > 0");

    // Model the state change
    ctx.push_assume("increment", "counter_new == counter_old + amount");

    // Verify the postcondition
    ctx.push_assert("correct_increment", "counter_new > counter_old");

    match ctx.verify() {
        VerifyResult::Verified => {
            println!("  ✓ Verified: counter increases when adding positive amount");
        }
        VerifyResult::Counterexample {
            obligation_name,
            model,
            ..
        } => {
            println!("  ✗ Counterexample for {}: {:?}", obligation_name, model);
        }
        _ => {
            println!("  ? Unknown result");
        }
    }
}

/// Example 4: Absolute difference verification
///
/// Verifies properties of absolute difference between two non-negative numbers
fn verify_abs_difference() {
    println!("\nExample 4: Verifying absolute difference properties");

    let mut ctx = VerificationContext::new();

    // Declare variables over `int`. The absolute-difference properties below are
    // statements about mathematical integers; modelling them over `int` keeps the
    // subtraction free of signed-overflow wraparound artifacts.
    ctx.declare_var_parsed("x", "int");
    ctx.declare_var_parsed("y", "int");
    ctx.declare_var_parsed("result", "int");

    // Preconditions: both inputs are non-negative
    ctx.push_assume("x_nonneg", "x >= 0");
    ctx.push_assume("y_nonneg", "y >= 0");

    // Model the absolute difference computation
    // result = if x > y then x - y else y - x
    ctx.push_assume(
        "abs_diff",
        "(x > y && result == x - y) || (x <= y && result == y - x)",
    );

    // Verify assertions about the result
    ctx.push_assert("result_nonneg", "result >= 0");

    match ctx.verify() {
        VerifyResult::Verified => {
            println!("  ✓ Verified: absolute difference is non-negative");
        }
        VerifyResult::Counterexample {
            obligation_name,
            model,
            ..
        } => {
            println!("  ✗ Counterexample for {}: {:?}", obligation_name, model);
        }
        _ => {
            println!("  ? Unknown result");
        }
    }

    // Second property: result is bounded by max of inputs
    let mut ctx2 = VerificationContext::new();
    ctx2.declare_var_parsed("x", "int");
    ctx2.declare_var_parsed("y", "int");
    ctx2.declare_var_parsed("result", "int");
    ctx2.push_assume("x_nonneg", "x >= 0");
    ctx2.push_assume("y_nonneg", "y >= 0");
    ctx2.push_assume(
        "abs_diff",
        "(x > y && result == x - y) || (x <= y && result == y - x)",
    );

    // result <= max(x, y)
    ctx2.push_assert(
        "bounded",
        "(x >= y && result <= x) || (y > x && result <= y)",
    );

    match ctx2.verify() {
        VerifyResult::Verified => {
            println!("  ✓ Verified: result <= max(x, y)");
        }
        VerifyResult::Counterexample {
            obligation_name,
            model,
            ..
        } => {
            println!("  ✗ Counterexample for {}: {:?}", obligation_name, model);
        }
        _ => {
            println!("  ? Unknown result");
        }
    }
}

/// Example 5: Division safety verification
///
/// Verifies a bound on truncating integer division.
///
/// SUPPORTED-FRAGMENT NOTE: the full Euclidean identity
/// `result*divisor <= dividend < (result+1)*divisor` is *nonlinear* (it
/// multiplies two unknowns, `result` and `divisor`). ay's decision procedure is
/// complete for linear integer arithmetic but returns `Unknown` on such
/// nonlinear obligations, so we stay inside the decidable fragment by dividing
/// by a *constant* divisor. Dividing a non-negative value by 2 never grows it
/// and never goes negative — a linear, provable fact.
fn verify_safe_division() {
    println!("\nExample 5: Verifying safe division");

    let mut ctx = VerificationContext::new();

    // `int` (unbounded) so the bound is a pure arithmetic statement.
    ctx.declare_var_parsed("dividend", "int");
    ctx.declare_var_parsed("result", "int");

    // Precondition: the value being halved is non-negative.
    ctx.push_assume("dividend_nonneg", "dividend >= 0");

    // Model halving (constant divisor keeps the obligation linear).
    ctx.push_assume("division", "result == dividend / 2");

    // Verify the result stays within [0, dividend].
    ctx.push_assert("division_property", "result >= 0 && result <= dividend");

    match ctx.verify() {
        VerifyResult::Verified => {
            println!("  ✓ Verified: halving a non-negative value stays in [0, dividend]");
        }
        VerifyResult::Counterexample {
            obligation_name,
            model,
            ..
        } => {
            println!("  ✗ Counterexample for {}: {:?}", obligation_name, model);
        }
        _ => {
            println!("  ? Unknown result (likely integer division semantics)");
        }
    }
}

fn main() {
    println!("=== Basic TrustVc Verification Examples (Path A) ===\n");

    verify_increment();
    verify_multiply_positive();
    verify_counter_increment();
    verify_abs_difference();
    verify_safe_division();

    println!("\n=== Examples Complete ===");
}
