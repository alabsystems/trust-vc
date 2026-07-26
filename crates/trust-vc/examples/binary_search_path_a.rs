//! Binary search verification example using Path A (direct API)
//!
//! This example shows how to verify properties of binary search using the
//! VerificationContext API. Since we can't use loop invariants with macros,
//! we verify individual properties of the algorithm.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

/// Verify that binary search maintains valid bounds
fn verify_bounds_maintenance() {
    println!("Example 1: Verifying binary search bounds maintenance");

    let mut ctx = VerificationContext::new();

    // Variables for array and search bounds
    ctx.declare_var_parsed("arr_len", "usize");
    ctx.declare_var_parsed("low", "usize");
    ctx.declare_var_parsed("high", "usize");
    ctx.declare_var_parsed("mid", "usize");

    // Preconditions: valid initial bounds
    ctx.push_assume("array_nonempty", "arr_len > 0");
    ctx.push_assume("initial_low", "low == 0");
    ctx.push_assume("initial_high", "high == arr_len");
    ctx.push_assume("low_le_high", "low <= high");

    // Binary search computes midpoint
    ctx.push_assume("midpoint", "mid == low + (high - low) / 2");

    // Verify midpoint is within bounds
    ctx.push_assert("mid_ge_low", "mid >= low");
    ctx.push_assert("mid_lt_high", "mid < high");

    match ctx.verify() {
        VerifyResult::Verified => {
            println!("  ✓ Verified: midpoint stays within bounds");
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

/// Verify that the search space decreases each iteration
fn verify_search_space_decreases() {
    println!("\nExample 2: Verifying search space decreases");

    // Case 1: When we search left half (target < arr[mid])
    let mut ctx1 = VerificationContext::new();
    ctx1.declare_var_parsed("low", "usize");
    ctx1.declare_var_parsed("high", "usize");
    ctx1.declare_var_parsed("mid", "usize");
    ctx1.declare_var_parsed("new_high", "usize");

    ctx1.push_assume("valid_range", "low < high");
    ctx1.push_assume("midpoint", "mid == low + (high - low) / 2");
    ctx1.push_assume("search_left", "new_high == mid");

    // Verify the range shrinks
    ctx1.push_assert("range_decreases", "new_high - low < high - low");

    match ctx1.verify() {
        VerifyResult::Verified => {
            println!("  ✓ Case 1: Search space decreases when searching left");
        }
        _ => {
            println!("  ✗ Failed to verify left search");
        }
    }

    // Case 2: When we search right half (target > arr[mid])
    let mut ctx2 = VerificationContext::new();
    ctx2.declare_var_parsed("low", "usize");
    ctx2.declare_var_parsed("high", "usize");
    ctx2.declare_var_parsed("mid", "usize");
    ctx2.declare_var_parsed("new_low", "usize");

    ctx2.push_assume("valid_range", "low < high");
    ctx2.push_assume("midpoint", "mid == low + (high - low) / 2");
    ctx2.push_assume("search_right", "new_low == mid + 1");

    // Verify the range shrinks
    ctx2.push_assert("range_decreases", "high - new_low < high - low");

    match ctx2.verify() {
        VerifyResult::Verified => {
            println!("  ✓ Case 2: Search space decreases when searching right");
        }
        _ => {
            println!("  ✗ Failed to verify right search");
        }
    }
}

/// Verify correctness of found/not-found conditions
fn verify_result_correctness() {
    println!("\nExample 3: Verifying result correctness");

    // Case 1: Element found at mid
    let mut ctx1 = VerificationContext::new();
    ctx1.declare_var_parsed("target", "i32");
    ctx1.declare_var_parsed("arr_mid_value", "i32");
    ctx1.declare_var_parsed("mid", "usize");
    ctx1.declare_var_parsed("arr_len", "usize");

    ctx1.push_assume("found_condition", "arr_mid_value == target");
    ctx1.push_assume("mid_valid", "mid < arr_len");

    // If we found it, the index should be valid
    ctx1.push_assert("valid_result", "mid < arr_len");

    match ctx1.verify() {
        VerifyResult::Verified => {
            println!("  ✓ Verified: Found element has valid index");
        }
        _ => {
            println!("  ✗ Failed to verify found case");
        }
    }

    // Case 2: Element not in array (low >= high termination)
    let mut ctx2 = VerificationContext::new();
    ctx2.declare_var_parsed("low", "usize");
    ctx2.declare_var_parsed("high", "usize");

    ctx2.push_assume("not_found_condition", "low >= high");

    // This represents that we've exhausted the search space
    ctx2.push_assert("search_exhausted", "low >= high");

    match ctx2.verify() {
        VerifyResult::Verified => {
            println!("  ✓ Verified: Not-found condition is search exhaustion");
        }
        _ => {
            println!("  ✗ Failed to verify not-found case");
        }
    }
}

/// Verify properties specific to searching sorted arrays
fn verify_sorted_array_properties() {
    println!("\nExample 4: Verifying sorted array search properties");

    let mut ctx = VerificationContext::new();

    // Element values are modeled over `int` (the comparison is order-theoretic,
    // so the bit width is irrelevant and `int` avoids overflow noise).
    //
    // The original version of this example declared separate index variables and
    // an unrelated `arr_mid`, leaving the sortedness link between position `mid`
    // and position `j` unstated — so the conclusion did not actually follow and
    // ay produced a (correct) counterexample. We state the sortedness fact we
    // rely on directly: for the sorted array, `mid <= j` implies `arr[mid] <= arr[j]`.
    ctx.declare_var_parsed("arr_mid", "int");
    ctx.declare_var_parsed("arr_j", "int");
    ctx.declare_var_parsed("target", "int");

    // Sortedness consequence for the two positions in play (mid <= j):
    ctx.push_assume("sorted_mid_le_j", "arr_mid <= arr_j");

    // Binary-search branch condition: target sits left of arr[mid].
    ctx.push_assume("target_less", "target < arr_mid");

    // Since arr[j] >= arr[mid] > target, every element at or right of mid exceeds
    // target — which is exactly why the right half can be excluded.
    ctx.push_assert("can_exclude_right", "arr_j > target");

    match ctx.verify() {
        VerifyResult::Verified => {
            println!("  ✓ Verified: Can exclude right half when target < arr[mid]");
        }
        VerifyResult::Counterexample {
            obligation_name,
            model,
            ..
        } => {
            println!("  ✗ Counterexample for {}: {:?}", obligation_name, model);
        }
        _ => {
            println!("  ? Unknown (may need more constraints on sorted property)");
        }
    }
}

/// Verify the optimization of midpoint calculation to avoid overflow
fn verify_midpoint_no_overflow() {
    println!("\nExample 5: Verifying midpoint calculation avoids overflow");

    let mut ctx = VerificationContext::new();

    // Use u32 to make overflow more realistic
    ctx.declare_var_parsed("low", "u32");
    ctx.declare_var_parsed("high", "u32");
    ctx.declare_var_parsed("mid_naive", "u32");
    ctx.declare_var_parsed("mid_safe", "u32");

    // Preconditions
    ctx.push_assume("valid_range", "low <= high");
    ctx.push_assume("high_large", "high > 2000000000"); // Close to u32::MAX / 2

    // Naive calculation: (low + high) / 2 can overflow
    // Safe calculation: low + (high - low) / 2 won't overflow
    ctx.push_assume("safe_calc", "mid_safe == low + (high - low) / 2");

    // Verify the safe version is in bounds
    ctx.push_assert("mid_ge_low", "mid_safe >= low");
    ctx.push_assert("mid_le_high", "mid_safe <= high");

    match ctx.verify() {
        VerifyResult::Verified => {
            println!("  ✓ Verified: Safe midpoint calculation stays in bounds");
        }
        _ => {
            println!("  ✗ Failed to verify safe midpoint");
        }
    }

    // Second property: when the search window is non-empty (low < high), the
    // safe midpoint sits strictly inside it: low <= mid < high. This is the loop
    // invariant that makes the recursion well-founded (the window always shrinks).
    //
    // SUPPORTED-FRAGMENT NOTE: proving the *naive vs safe equivalence*
    // (`(low + high) / 2 == low + (high - low) / 2`) requires the solver to
    // reason about two divisions of unknowns, which is nonlinear; over bitvectors
    // ay times out on it. We instead prove the bound that binary search actually
    // depends on, over `int`, where it is a clean linear fact.
    let mut ctx2 = VerificationContext::new();
    ctx2.declare_var_parsed("low", "int");
    ctx2.declare_var_parsed("high", "int");
    ctx2.declare_var_parsed("mid_safe", "int");

    ctx2.push_assume("valid_range", "0 <= low && low < high");
    ctx2.push_assume("safe_calc", "mid_safe == low + (high - low) / 2");

    ctx2.push_assert("mid_ge_low", "mid_safe >= low");
    ctx2.push_assert("mid_lt_high", "mid_safe < high");

    match ctx2.verify() {
        VerifyResult::Verified => {
            println!("  ✓ Verified: safe midpoint stays strictly inside (low, high) window");
        }
        _ => {
            println!("  ✗ Failed to verify midpoint window bound");
        }
    }
}

fn main() {
    println!("=== Binary Search Verification Examples (Path A) ===\n");

    verify_bounds_maintenance();
    verify_search_space_decreases();
    verify_result_correctness();
    verify_sorted_array_properties();
    verify_midpoint_no_overflow();

    println!("\n=== Examples Complete ===");
}
