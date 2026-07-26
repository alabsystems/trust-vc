// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Migration guide from Path B (macros) to Path A (explicit API)
//!
//! This example shows how to convert from the broken macro-based approach
//! to the working VerificationContext API approach.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

/// Path B approach (BROKEN - DO NOT USE):
/// ```rust,ignore
/// #[proof]
/// fn lemma_sum_positive(x: i32, y: i32) {
///     requires!(x > 0 && y > 0);
///     trust_vc::assert!(x + y > 0);
/// }
/// ```
///
/// Problems with Path B:
/// - Variables x, y are never declared to ay
/// - Thread-local state causes RefCell panics
/// - Macros collect strings but don't build proper VCs
///
/// Path A approach (WORKING):
/// NOTE: Currently returns Unknown due to expression parser limitations with assumptions.
/// This is a known issue - the ay encoder needs improvement to handle assumptions properly.
fn verify_sum_positive() -> VerifyResult {
    let mut ctx = VerificationContext::new();

    // CRITICAL: Explicitly declare all variables
    ctx.declare_var_parsed("x", "i32");
    ctx.declare_var_parsed("y", "i32");

    // Add preconditions (was: requires!)
    // Note: x + y > 0 with x > 0, y > 0 is NOT true under BV32 overflow
    // semantics — large positive i32 values wrap to negative on addition.
    ctx.push_assume("x_positive", "x > 0");
    ctx.push_assume("y_positive", "y > 0");

    // Add assertion to prove (was: trust_vc::assert!)
    ctx.push_assert("sum_positive", "x + y > 0");

    // Run verification
    ctx.verify()
}

/// Example: Simple assertion without preconditions
fn verify_identity() -> VerifyResult {
    let mut ctx = VerificationContext::new();

    ctx.declare_var_parsed("n", "i32");
    ctx.push_assert("identity", "n + 0 == n");

    ctx.verify()
}

/// Example: Postcondition verification
fn verify_increment_postcondition() -> VerifyResult {
    let mut ctx = VerificationContext::new();

    // Function: fn increment(x: int) -> int { x + 1 }
    //
    // We model over `int` (Verus's unbounded mathematical integer). With a
    // bounded `i32`, `result == x + 1` wraps at `x == i32::MAX`, so `result > x`
    // has a legitimate overflow counterexample and would NOT verify. To prove the
    // postcondition over `i32` you must instead add the precondition
    // `x < i32::MAX` (see the macro quickstart `proof_macro_quickstart.rs`).
    ctx.declare_var_parsed("x", "int");
    ctx.declare_var_parsed("result", "int");

    // Model the function behavior
    ctx.push_assume("function_def", "result == x + 1");

    // Postcondition (was: ensures!)
    ctx.push_assert("postcondition", "result > x");

    ctx.verify()
}

/// Example: Termination measure
fn verify_termination() -> VerifyResult {
    let mut ctx = VerificationContext::new();

    // For recursive function with decreases(n)
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("n_next", "u64");

    // Recursive case condition
    ctx.push_assume("recursive_case", "n > 0");
    ctx.push_assume("next_value", "n_next == n - 1");

    // Prove measure decreases
    ctx.push_assert("decreases", "n_next < n");
    ctx.push_assert("bounded", "n_next >= 0");

    ctx.verify()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_path_a_examples() {
        // Identity should verify (no assumptions needed)
        assert!(matches!(verify_identity(), VerifyResult::Verified));

        // Sum positive fails: x + y can overflow i32 even with x > 0, y > 0
        // (BV32 signed overflow wraps large positives to negative).
        assert!(matches!(
            verify_sum_positive(),
            VerifyResult::Unknown { .. } | VerifyResult::Counterexample { .. }
        ));

        // Increment postcondition should verify
        assert!(matches!(
            verify_increment_postcondition(),
            VerifyResult::Verified
        ));

        // Termination should verify
        assert!(matches!(verify_termination(), VerifyResult::Verified));
    }
}

fn main() {
    println!("Path A Migration Examples");
    println!("=========================");

    println!("\n1. Identity: {:?}", verify_identity());
    println!("2. Sum positive: {:?}", verify_sum_positive());
    println!(
        "3. Increment postcondition: {:?}",
        verify_increment_postcondition()
    );
    println!("4. Termination: {:?}", verify_termination());

    println!("\nKey differences from Path B:");
    println!("- Must explicitly declare ALL variables with ctx.declare_var_parsed()");
    println!("- Use ctx.push_assume() instead of requires!()");
    println!("- Use ctx.push_assert() instead of trust_vc::assert!()");
    println!("- No thread-local state or RefCell issues");
    println!("- Direct control over verification context");
}
