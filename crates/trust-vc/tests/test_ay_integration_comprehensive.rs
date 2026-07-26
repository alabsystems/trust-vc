// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Comprehensive ay integration tests for issue #443
//!
//! This file tests the ay solver integration thoroughly, covering:
//! - Multiple SMT theories (arithmetic, arrays, bitvectors)
//! - Complex constraints with multiple variables
//! - Error conditions and edge cases
//! - Performance characteristics
//! - Model extraction and counterexamples

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

// ============================================================================
// Basic Arithmetic Tests
// ============================================================================

#[test]
fn test_integer_arithmetic_operations() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");
    ctx.declare_var_parsed("y", "i32");
    ctx.declare_var_parsed("z", "i32");

    // Test various arithmetic operations
    ctx.push_assume("setup", "x == 10 && y == 5");
    ctx.push_assert("addition", "x + y == 15");
    ctx.push_assert("subtraction", "x - y == 5");
    ctx.push_assert("multiplication", "x * 2 == 20");
    ctx.push_assert("division", "x / y == 2");
    ctx.push_assert("modulo", "x % 3 == 1");

    let result = ctx.verify();
    // Solver now handles concrete arithmetic correctly
    assert!(
        matches!(result, VerifyResult::Verified),
        "Concrete arithmetic with x==10, y==5 should verify, got: {:?}",
        result
    );
}

#[test]
fn test_integer_comparisons() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("a", "i32");
    ctx.declare_var_parsed("b", "i32");

    ctx.push_assume("setup", "a == 10 && b == 20");
    ctx.push_assert("less_than", "a < b");
    ctx.push_assert("less_equal", "a <= b && a <= 10");
    ctx.push_assert("greater", "b > a");
    ctx.push_assert("greater_equal", "b >= a && b >= 20");
    ctx.push_assert("not_equal", "a != b");

    let result = ctx.verify();
    // AY verifies simple comparison constraints with concrete values
    assert!(
        matches!(result, VerifyResult::Verified),
        "Comparisons with concrete values should verify, got: {:?}",
        result
    );
}

#[test]
fn test_overflow_behavior() {
    // Test that we handle potential overflow correctly
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");

    // We use bitvectors for i32, which wrap on overflow
    // At i32::MAX, x + 1 wraps to i32::MIN, which is less than x
    ctx.push_assume("large_value", "x == 2147483647"); // i32::MAX
    ctx.push_assert("overflow", "x + 1 > x");

    let result = ctx.verify();
    // With bitvector semantics, i32::MAX + 1 wraps to i32::MIN (negative)
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "Overflow test should produce counterexample (bitvectors wrap), got: {:?}",
        result
    );
}

// ============================================================================
// Boolean Logic Tests
// ============================================================================

#[test]
fn test_boolean_operations() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("p", "bool");
    ctx.declare_var_parsed("q", "bool");
    ctx.declare_var_parsed("r", "bool");

    // Test logical operations
    ctx.push_assume("setup", "p == true && q == false");
    ctx.push_assert("and", "(p && q) == false");
    ctx.push_assert("or", "(p || q) == true");
    ctx.push_assert("not", "!q == true");
    ctx.push_assert("implies", "(!p || q) == (p ==> q)");

    let result = ctx.verify();
    // Re-pinned 2026-07-04: `==>` parses as real implication since the 1fcb336
    // parser feature (2026-06-03); the old Error pin was stale. Semantic controls
    // (step-2 ledger): (p ==> q) == true under p=T,q=F -> Counterexample;
    // (!p || q) == (q ==> p) under p=T,q=F -> Counterexample (rules out reverse
    // implication); vacuous (q ==> p) == true -> Verified.
    assert!(
        matches!(result, VerifyResult::Verified),
        "(!p || q) == (p ==> q) is a tautology and ==> is supported; got: {:?}",
        result
    );
}

#[test]
fn test_boolean_tautologies() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("p", "bool");

    // Law of excluded middle
    ctx.push_assert("excluded_middle", "p || !p");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Tautology should verify, got: {:?}",
        result
    );
}

#[test]
fn test_boolean_contradictions() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("p", "bool");

    // Contradiction
    ctx.push_assert("contradiction", "p && !p");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "Contradiction should fail, got: {:?}",
        result
    );
}

// ============================================================================
// Complex Constraint Tests
// ============================================================================

#[test]
fn test_multiple_variables_and_constraints() {
    let mut ctx = VerificationContext::new();

    // Declare multiple variables
    for i in 0..5 {
        ctx.declare_var_parsed(&format!("x{}", i), "i32");
    }

    // Add complex constraints
    ctx.push_assume("ordering", "x0 < x1 && x1 < x2 && x2 < x3 && x3 < x4");
    ctx.push_assume("spacing", "x1 - x0 == 1 && x2 - x1 == 1");
    ctx.push_assume("start", "x0 == 0");

    // Verify consequences
    ctx.push_assert("x2_value", "x2 == 2");
    ctx.push_assert("x4_greater", "x4 > 3");
    ctx.push_assert("sum", "x0 + x1 + x2 >= 3");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Complex constraints should verify, got: {:?}",
        result
    );
}

#[test]
fn test_nonlinear_arithmetic() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");
    ctx.declare_var_parsed("y", "i32");

    // Nonlinear constraints (might be challenging for ay)
    ctx.push_assume("squares", "x * x == 4 && y * y == 9");
    ctx.push_assume("positive", "x > 0 && y > 0");
    ctx.push_assert("values", "x == 2 && y == 3");

    let result = ctx.verify();
    // BV32: x*x==4 with x>0 has multiple solutions (e.g., x=2 works but BV wrap
    // creates other positive roots). y=3 isn't the only positive y with y*y==9 in BV32.
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "Nonlinear BV arithmetic has multiple positive roots — should find counterexample, got: {:?}",
        result
    );
}

// ============================================================================
// Quantifier Tests (if supported)
// ============================================================================

#[test]
fn test_universal_quantification() {
    let mut ctx = VerificationContext::new();

    // This tests if quantifiers are supported
    // forall x: x + 0 == x
    ctx.push_assert("identity", "forall x: i32 :: x + 0 == x");

    let result = ctx.verify();
    // Quantifier syntax with type annotations (`:`) is not supported by the parser
    assert!(
        matches!(result, VerifyResult::Error { .. }),
        "Universal quantifier should return parse Error, got: {:?}",
        result
    );
}

#[test]
fn test_existential_quantification() {
    let mut ctx = VerificationContext::new();

    // exists x: x * x == 4
    ctx.push_assert("exists_square", "exists x: i32 :: x * x == 4");

    let result = ctx.verify();
    // Quantifier syntax with type annotations (`:`) is not supported by the parser
    assert!(
        matches!(result, VerifyResult::Error { .. }),
        "Existential quantifier should return parse Error, got: {:?}",
        result
    );
}

// ============================================================================
// Array/Sequence Tests (if supported)
// ============================================================================

#[test]
fn test_array_operations() {
    let mut ctx = VerificationContext::new();

    // Try to use array syntax
    ctx.declare_var_parsed("arr", "Seq<i32>");
    ctx.declare_var_parsed("idx", "i32");

    ctx.push_assume("bounds", "idx >= 0 && idx < arr.len");
    ctx.push_assert("access", "arr[idx] == arr.select(idx)");

    let result = ctx.verify();
    // arr.len property access syntax is not yet supported (requires parentheses)
    assert!(
        matches!(result, VerifyResult::Error { .. }),
        "Array property syntax should return Error, got: {:?}",
        result
    );
}

// ============================================================================
// Error Handling Tests
// ============================================================================

#[test]
fn test_empty_context() {
    let ctx = VerificationContext::new();

    // Empty context must return Error per #808 soundness fix
    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Error { .. }),
        "Empty context must return Error (soundness #808), got: {:?}",
        result
    );
}

#[test]
fn test_undeclared_variable_reference() {
    let mut ctx = VerificationContext::new();

    // Reference undeclared variable
    ctx.push_assert("undefined", "unknown_var == 5");

    let result = ctx.verify();
    // Should fail or return unknown
    assert!(
        !matches!(result, VerifyResult::Verified),
        "Undefined variable should not verify"
    );
}

#[test]
fn test_type_mismatch() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");
    ctx.declare_var_parsed("b", "bool");

    // Type error: comparing int and bool
    ctx.push_assert("type_error", "x == b");

    // Encoder catches ay-core sort mismatch panic and returns Unknown/Error
    let result = ctx.verify();
    assert!(
        !matches!(result, VerifyResult::Verified),
        "Type mismatch should not verify, got: {:?}",
        result
    );
}

// ============================================================================
// Counterexample Extraction Tests
// ============================================================================

#[test]
fn test_counterexample_extraction() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");
    ctx.declare_var_parsed("y", "i32");

    // Add constraint that has counterexamples
    ctx.push_assert("false_claim", "x + y > 100");

    let result = ctx.verify();
    // Unconstrained x + y > 100 is falsifiable (e.g. x=0, y=0)
    assert!(
        matches!(
            result,
            VerifyResult::Counterexample {
                obligation_name: ref name,
                ..
            } if name == "false_claim"
        ),
        "Expected counterexample for false_claim, got: {:?}",
        result
    );
}

#[test]
fn test_multiple_counterexamples() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");

    // Add multiple false assertions
    ctx.push_assert("claim1", "x > 10");
    ctx.push_assert("claim2", "x < 5");

    let result = ctx.verify();
    // Both claims are unsatisfiable for any single x, so solver finds a counterexample
    assert!(
        matches!(
            result,
            VerifyResult::Counterexample {
                obligation_name: ref name,
                ..
            } if name == "claim1" || name == "claim2"
        ),
        "Expected counterexample for one of the claims, got: {:?}",
        result
    );
}

// ============================================================================
// Performance and Scaling Tests
// ============================================================================

#[test]
fn test_many_variables() {
    let mut ctx = VerificationContext::new();

    // Create many variables
    let n = 50;
    for i in 0..n {
        ctx.declare_var_parsed(&format!("v{}", i), "i32");
    }

    // Add simple constraints
    for i in 0..n - 1 {
        ctx.push_assume(&format!("order{}", i), &format!("v{} < v{}", i, i + 1));
    }

    ctx.push_assume("start", "v0 == 0");
    ctx.push_assert("end", &format!("v{} >= {}", n - 1, n - 1));

    let result = ctx.verify();
    // Current ay discharges this concrete chain successfully.
    assert!(
        matches!(result, VerifyResult::Verified),
        "Many variables with chained constraints should verify, got: {:?}",
        result
    );
}

#[test]
fn test_deeply_nested_expressions() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("x", "i32");

    // Build deeply nested expression
    let mut expr = "x".to_string();
    for _ in 0..10 {
        expr = format!("({} + 1)", expr);
    }

    ctx.push_assume("value", "x == 0");
    ctx.push_assert("nested", &format!("{} == 10", expr));

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "Nested expressions should verify, got: {:?}",
        result
    );
}

// ============================================================================
// Regression Tests for Known Issues
// ============================================================================

#[test]
fn test_false_literal_should_fail() {
    // Regression test for issue where "false" might verify incorrectly
    let mut ctx = VerificationContext::new();
    ctx.push_assert("false_literal", "false");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "False literal should not verify, got: {:?}",
        result
    );
}

#[test]
fn test_true_literal_should_verify() {
    let mut ctx = VerificationContext::new();
    ctx.push_assert("true_literal", "true");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "True literal should verify, got: {:?}",
        result
    );
}

// ============================================================================
// Integration with Proof Obligations
// ============================================================================

#[test]
fn test_proof_obligation_workflow() {
    // Simulate what should happen for a proof function
    let mut ctx = VerificationContext::new();

    // Function: fn abs(x: i32) -> i32
    ctx.declare_var_parsed("x", "i32");
    ctx.declare_var_parsed("result", "i32");

    // Specification
    ctx.push_assume(
        "abs_def",
        "(x >= 0 && result == x) || (x < 0 && result == -x)",
    );

    // Postcondition to verify
    ctx.push_assert("abs_nonneg", "result >= 0");

    let result = ctx.verify();
    // BV32: abs(i32::MIN) overflows (-(-2^31) = -2^31 in BV), so result >= 0 fails.
    // Solver correctly finds counterexample at x = i32::MIN.
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "abs(i32::MIN) overflows in BV32 — should find counterexample, got: {:?}",
        result
    );
}

#[test]
fn test_loop_invariant_pattern() {
    // Pattern for loop invariant verification
    let mut ctx = VerificationContext::new();

    // Loop variables
    ctx.declare_var_parsed("i", "i32");
    ctx.declare_var_parsed("sum", "i32");
    ctx.declare_var_parsed("n", "i32");

    // Loop invariant: sum == i * (i + 1) / 2
    ctx.push_assume("invariant", "sum == i * (i + 1) / 2");
    ctx.push_assume("bounds", "i >= 0 && i <= n");

    // After one iteration: i' = i + 1, sum' = sum + i + 1
    ctx.declare_var_parsed("i_next", "i32");
    ctx.declare_var_parsed("sum_next", "i32");
    ctx.push_assume("step", "i_next == i + 1 && sum_next == sum + i + 1");

    // Verify invariant is maintained
    ctx.push_assert(
        "invariant_maintained",
        "sum_next == i_next * (i_next + 1) / 2",
    );

    let result = ctx.verify();
    // BV32: nonlinear i*(i+1)/2 overflows for large i, breaking the invariant.
    // Solver finds concrete BV counterexample.
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "Nonlinear BV invariant overflows — should find counterexample, got: {:?}",
        result
    );
}
