//! Termination proof examples using Path A (direct API)
//!
//! This example demonstrates how to encode termination proofs using the
//! VerificationContext API. Since macros cannot access compiler internals,
//! we model termination using well-founded ordering constraints.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

/// Example 1: Factorial termination verification
///
/// Verifies that factorial terminates by showing n decreases on each recursive call
fn verify_factorial_termination() {
    println!("Example 1: Verifying factorial termination");

    let mut ctx = VerificationContext::new();

    // Variables for the recursive call
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("n_next", "u64");

    // Precondition: we're in the recursive case
    ctx.push_assume("recursive_case", "n > 0");

    // Model the recursive call: factorial(n-1)
    ctx.push_assume("recursive_call", "n_next == n - 1");

    // Verify termination: n_next < n (measure decreases)
    ctx.push_assert("measure_decreases", "n_next < n");

    // Also verify n_next is still valid (non-negative for u64)
    ctx.push_assert("valid_next", "n_next >= 0");

    match ctx.verify() {
        VerifyResult::Verified => {
            println!("  ✓ Verified: factorial terminates (n decreases)");
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

/// Example 2: Fibonacci termination verification
///
/// Verifies both recursive calls in Fibonacci decrease the measure
fn verify_fibonacci_termination() {
    println!("\nExample 2: Verifying Fibonacci termination");

    // First recursive call: fib(n-1)
    let mut ctx1 = VerificationContext::new();
    ctx1.declare_var_parsed("n", "u64");
    ctx1.declare_var_parsed("n_minus_1", "u64");
    ctx1.push_assume("recursive_case", "n > 1");
    ctx1.push_assume("first_call", "n_minus_1 == n - 1");
    ctx1.push_assert("first_decreases", "n_minus_1 < n");

    match ctx1.verify() {
        VerifyResult::Verified => {
            println!("  ✓ Verified: fib(n-1) decreases measure");
        }
        _ => {
            println!("  ✗ Failed to verify first recursive call");
        }
    }

    // Second recursive call: fib(n-2)
    let mut ctx2 = VerificationContext::new();
    ctx2.declare_var_parsed("n", "u64");
    ctx2.declare_var_parsed("n_minus_2", "u64");
    ctx2.push_assume("recursive_case", "n > 1");
    ctx2.push_assume("second_call", "n_minus_2 == n - 2");
    ctx2.push_assert("second_decreases", "n_minus_2 < n");

    match ctx2.verify() {
        VerifyResult::Verified => {
            println!("  ✓ Verified: fib(n-2) decreases measure");
        }
        _ => {
            println!("  ✗ Failed to verify second recursive call");
        }
    }
}

/// Example 3: Euclidean algorithm (GCD) termination
///
/// Verifies that the *subtractive* Euclidean algorithm terminates by exhibiting
/// a measure that strictly decreases on each recursive call.
///
/// SUPPORTED-FRAGMENT NOTE: the modulo-based step `gcd(a, b) -> gcd(b, a % b)`
/// relies on the fact `a % b < b`, which is nonlinear in the symbolic divisor
/// `b`; ay returns `Unknown` for that obligation. The subtractive variant
/// `gcd(a, b) -> gcd(b, a - b)` (valid when `a >= b > 0`) terminates for the same
/// reason but with a *linear* measure `a + b`, which ay decides directly. We use
/// `nat` (Verus's non-negative unbounded integer) so the subtraction is well
/// defined and never wraps.
fn verify_gcd_termination() {
    println!("\nExample 3: Verifying GCD termination");

    let mut ctx = VerificationContext::new();

    // Variables for gcd(a, b) and the recursive call gcd(b, a - b).
    ctx.declare_var_parsed("a", "nat");
    ctx.declare_var_parsed("b", "nat");
    ctx.declare_var_parsed("a_next", "nat");
    ctx.declare_var_parsed("b_next", "nat");

    // Precondition: we're in the recursive case with a >= b > 0.
    ctx.push_assume("ordered", "a >= b");
    ctx.push_assume("b_positive", "b > 0");

    // Model the recursive call: gcd(b, a - b).
    ctx.push_assume("recursive_call_a", "a_next == b");
    ctx.push_assume("recursive_call_b", "b_next == a - b");

    // Verify termination: the measure a + b strictly decreases (it drops by b > 0).
    ctx.push_assert("measure_decreases", "a_next + b_next < a + b");

    match ctx.verify() {
        VerifyResult::Verified => {
            println!("  ✓ Verified: subtractive GCD terminates (measure a + b decreases)");
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

/// Example 4: Collatz sequence termination (unverifiable but interesting)
///
/// The Collatz conjecture is that this sequence always reaches 1, but this
/// is an open problem in mathematics. We can still model it!
fn model_collatz_step() {
    println!("\nExample 4: Modeling Collatz sequence step");

    let mut ctx = VerificationContext::new();

    // `nat` (unbounded, non-negative) rather than `u64`: the Collatz step
    // `3 * n + 1` overflows a 64-bit value for large odd `n`, so over `u64` the
    // "next value is positive" claim has a real wraparound counterexample. The
    // mathematical step is what we mean to model, so we use `nat`.
    ctx.declare_var_parsed("n", "nat");
    ctx.declare_var_parsed("n_next", "nat");

    // Precondition: n > 1 (not at base case)
    ctx.push_assume("not_done", "n > 1");

    // Model the Collatz step
    ctx.push_assume(
        "collatz_step",
        "(n % 2 == 0 && n_next == n / 2) || (n % 2 == 1 && n_next == 3 * n + 1)",
    );

    // We can't prove termination (open problem!), but we can verify the step is correct
    ctx.push_assert("step_valid", "n_next > 0");

    match ctx.verify() {
        VerifyResult::Verified => {
            println!("  ✓ Verified: Collatz step produces valid next value");
        }
        _ => {
            println!("  ✗ Failed to verify Collatz step");
        }
    }

    println!("  Note: Collatz termination is an open problem in mathematics!");
}

/// Example 5: Lexicographic ordering for Ackermann function
///
/// Demonstrates termination with lexicographic ordering on pairs (m, n)
fn verify_ackermann_termination() {
    println!("\nExample 5: Verifying Ackermann termination (lexicographic)");

    // Case 1: ackermann(m-1, 1) when n = 0
    let mut ctx1 = VerificationContext::new();
    ctx1.declare_var_parsed("m", "u64");
    ctx1.push_assume("case1_condition", "m > 0");
    ctx1.declare_var_parsed("m_next", "u64");
    ctx1.push_assume("case1_call", "m_next == m - 1");
    ctx1.push_assert("case1_decreases", "m_next < m");

    match ctx1.verify() {
        VerifyResult::Verified => {
            println!("  ✓ Case 1: (m-1, 1) < (m, 0) lexicographically");
        }
        _ => {
            println!("  ✗ Failed to verify case 1");
        }
    }

    // Case 2: First call ackermann(m, n-1) when n > 0
    let mut ctx2 = VerificationContext::new();
    ctx2.declare_var_parsed("m", "u64");
    ctx2.declare_var_parsed("n", "u64");
    ctx2.declare_var_parsed("n_next", "u64");
    ctx2.push_assume("case2_condition", "m > 0 && n > 0");
    ctx2.push_assume("case2_first_call", "n_next == n - 1");
    // Same m, but n decreases
    ctx2.push_assert("case2_first_decreases", "n_next < n");

    match ctx2.verify() {
        VerifyResult::Verified => {
            println!("  ✓ Case 2a: (m, n-1) < (m, n) lexicographically");
        }
        _ => {
            println!("  ✗ Failed to verify case 2a");
        }
    }

    // Case 2b: Second call ackermann(m-1, result) where result is from first call
    let mut ctx3 = VerificationContext::new();
    ctx3.declare_var_parsed("m", "u64");
    ctx3.declare_var_parsed("m_next", "u64");
    ctx3.push_assume("case2b_condition", "m > 0");
    ctx3.push_assume("case2b_call", "m_next == m - 1");
    ctx3.push_assert("case2b_decreases", "m_next < m");

    match ctx3.verify() {
        VerifyResult::Verified => {
            println!("  ✓ Case 2b: (m-1, _) < (m, n) lexicographically");
        }
        _ => {
            println!("  ✗ Failed to verify case 2b");
        }
    }
}

fn main() {
    println!("=== Termination Proof Examples (Path A) ===\n");

    verify_factorial_termination();
    verify_fibonacci_termination();
    verify_gcd_termination();
    model_collatz_step();
    verify_ackermann_termination();

    println!("\n=== Examples Complete ===");
}
