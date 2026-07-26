// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 25 — Competition dry-run under overflow checking.
//!
//! Combines full Init/Step/Exit VC decomposition (Tier 18 pattern) WITH
//! overflow checking (Tier 21-24 pattern). This is the exact workflow a
//! competitor follows during the 90-minute VerifyThis clock:
//!
//!   1. Read problem → identify algorithm
//!   2. Decompose into Init/Step/Exit VCs
//!   3. Write pre/post conditions and loop invariants
//!   4. Verify each VC with check_overflow = true
//!   5. Confirm negative tests reject wrong invariants
//!
//! GROUP A: Prefix Sum — accumulator over bounded Seq elements.
//!   Invariant: p[i] == a[0] + a[1] + ... + a[i].
//!   Overflow-sensitive: accumulation can overflow without element bounds.
//!
//! GROUP B: Find Minimum — conditional update with index tracking.
//!   Invariant: min_val <= a[j] for all j <= i.
//!   Competition pattern: scan + conditional swap with proof that
//!   the minimum property is preserved.
//!
//! Part of #2187.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationContext.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::VerifyResult;

// ========================================================================
// GROUP A: Prefix Sum under Overflow Checking
//
// Given Seq<i32> `a` with elements bounded by ±1000, compute prefix sums
// where p[i] = a[0] + a[1] + ... + a[i].
//
// Competition relevance: prefix sums appear in range queries, cumulative
// statistics, and as building blocks for more complex algorithms.
// The accumulation `p[i] = p[i-1] + a[i]` is overflow-sensitive.
//
// INIT:  p[0] = a[0], invariant trivially holds at i=0.
// STEP:  p[i] = p[i-1] + a[i], invariant: p[i] bounded.
// EXIT:  p[n-1] == a[0] + ... + a[n-1] (concrete 4-element execution).
// NEG:   Wrong update (p[i] = a[i]) breaks prefix sum property.
// ========================================================================

/// Tier 25a INIT: Prefix sum initialization.
///
/// p[0] = a[0]. The prefix sum at position 0 is just the first element.
/// Under overflow checking, the assignment involves no arithmetic.
#[test]
fn test_vt_tier25a_prefix_sum_init() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a", "Seq<i32>");
    ctx.declare_var_parsed("p_0", "i32");

    ctx.push_assume("len", "a.len() >= 1 && a.len() <= 100");
    ctx.push_assume("elem0_bound", "a.index(0) >= -1000 && a.index(0) <= 1000");

    // Init: p[0] = a[0]
    ctx.push_assume("init", "p_0 == a.index(0)");

    // Bound: p[0] within ±1000
    ctx.push_assert("bound_init", "p_0 >= -1000 && p_0 <= 1000");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 25a INIT: prefix sum init should verify under overflow: {:?}",
        result,
    );
}

/// Tier 25a STEP: Prefix sum accumulation preserves bound.
///
/// Given: p_old bounded by ±(i * 1000), a[i] bounded by ±1000.
/// Step: p_new = p_old + a[i].
/// Prove: p_new bounded by ±((i+1) * 1000).
///
/// This is the core overflow-sensitive operation. Without element bounds,
/// the sum would overflow. Competition strategy: bound elements first,
/// then prove accumulation stays within i32.
#[test]
fn test_vt_tier25a_prefix_sum_step() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a", "Seq<i32>");
    ctx.declare_var_parsed("p_old", "i32");
    ctx.declare_var_parsed("p_new", "i32");
    ctx.declare_var_parsed("i", "u64");

    ctx.push_assume("len", "a.len() >= 1 && a.len() <= 100");
    ctx.push_assume("i_bound", "i >= 1 && i < a.len()");

    // Element bounded
    ctx.push_assume("elem_bound", "a.index(i) >= -1000 && a.index(i) <= 1000");
    // Inductive hypothesis: partial sum bounded by prior steps
    ctx.push_assume("ih_bound", "p_old >= -100000 && p_old <= 100000");

    // Step: p_new = p_old + a[i]
    ctx.push_assume("step", "p_new == p_old + a.index(i)");

    // Invariant preserved: p_new bounded
    ctx.push_assert("bound_preserved", "p_new >= -101000 && p_new <= 101000");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 25a STEP: prefix sum step should verify under overflow: {:?}",
        result,
    );
}

/// Tier 25a EXIT: Prefix sum concrete execution over 4 elements.
///
/// a = [10, 20, -5, 15]. Execute prefix sum step-by-step:
///   p0 = 10, p1 = 30, p2 = 25, p3 = 40.
/// Postcondition: p3 == 40 == a[0] + a[1] + a[2] + a[3].
///
/// Discrimination: removing any step assumption breaks the proof.
/// Under overflow checking, all additions are checked.
#[test]
fn test_vt_tier25a_prefix_sum_exit() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a", "Seq<i32>");
    ctx.declare_var_parsed("p0", "i32");
    ctx.declare_var_parsed("p1", "i32");
    ctx.declare_var_parsed("p2", "i32");
    ctx.declare_var_parsed("p3", "i32");

    ctx.push_assume("len", "a.len() == 4");
    ctx.push_assume("a0", "a.index(0) == 10");
    ctx.push_assume("a1", "a.index(1) == 20");
    ctx.push_assume("a2", "a.index(2) == -5");
    ctx.push_assume("a3", "a.index(3) == 15");

    // Step-by-step execution
    ctx.push_assume("step0", "p0 == a.index(0)");
    ctx.push_assume("step1", "p1 == p0 + a.index(1)");
    ctx.push_assume("step2", "p2 == p1 + a.index(2)");
    ctx.push_assume("step3", "p3 == p2 + a.index(3)");

    // Postcondition: final prefix sum == total
    ctx.push_assert("total", "p3 == 40");
    // Intermediate check: p2 == a[0] + a[1] + a[2]
    ctx.push_assert("intermediate", "p2 == 25");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 25a EXIT: prefix sum exit should verify under overflow: {:?}",
        result,
    );
}

/// Tier 25a NEGATIVE: Wrong prefix sum update breaks property.
///
/// If p[i] = a[i] instead of p[i-1] + a[i], the prefix sum property
/// p[i] == sum(a[0..=i]) does not hold.
#[test]
fn test_vt_tier25a_prefix_sum_wrong_update_negative() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("a", "Seq<i32>");
    ctx.declare_var_parsed("p0", "i32");
    ctx.declare_var_parsed("p1", "i32");

    ctx.push_assume("len", "a.len() == 3");
    ctx.push_assume("a0", "a.index(0) == 10");
    ctx.push_assume("a1", "a.index(1) == 20");

    ctx.push_assume("step0", "p0 == a.index(0)");
    // WRONG: p1 = a[1] instead of p0 + a[1]
    ctx.push_assume("wrong_step1", "p1 == a.index(1)");

    // p1 should equal a[0] + a[1] = 30, but p1 = 20 (WRONG)
    ctx.push_assert("wrong_total", "p1 == a.index(0) + a.index(1)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 25a NEG: wrong prefix update must produce Counterexample: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Find Minimum under Overflow Checking
//
// Given Seq<i32> `s`, find the minimum value and its index.
// Maintain: min_val and min_idx such that min_val == s[min_idx] and
// min_val <= s[j] for all j <= i.
//
// Competition relevance: find-min/find-max is a fundamental loop pattern.
// The conditional update `if s[i] < min_val` is the key invariant step.
// Under overflow checking, comparisons are safe but the invariant
// reasoning must be overflow-aware.
//
// INIT:  min_val = s[0], min_idx = 0.
// STEP:  if s[i] < min_val then min_val = s[i], min_idx = i.
// EXIT:  min_val <= all elements (concrete 4-element execution).
// NEG:   Wrong comparison direction (>) misses the actual minimum.
// ========================================================================

/// Tier 25b INIT: Find minimum initialization.
///
/// min_val = s[0], min_idx = 0. The minimum at position 0 is trivially
/// the element itself. Under overflow, no arithmetic involved.
#[test]
fn test_vt_tier25b_find_min_init() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("min_val", "i32");
    ctx.declare_var_parsed("min_idx", "u64");

    ctx.push_assume("len", "s.len() >= 1 && s.len() <= 100");

    // Init: min_val = s[0], min_idx = 0
    ctx.push_assume("init_val", "min_val == s.index(0)");
    ctx.push_assume("init_idx", "min_idx == 0");

    // Invariant at i=0: min_val <= s[0]
    ctx.push_assert("inv_le_s0", "min_val <= s.index(0)");
    // min_idx is valid
    ctx.push_assert("idx_valid", "min_idx < s.len()");
    // min_val == s[min_idx]
    ctx.push_assert("val_at_idx", "min_val == s.index(min_idx)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 25b INIT: find min init should verify under overflow: {:?}",
        result,
    );
}

/// Tier 25b STEP: Conditional min update preserves invariant.
///
/// IH: min_val <= s[j] for j in {0, 1, ..., i-1}, min_val == s[min_idx].
/// Step: if s[i] < min_val then min_val_new = s[i], else min_val_new = min_val.
/// Goal: min_val_new <= min_val AND min_val_new <= s[i].
///
/// Concrete: 3-element array, step at i=2.
#[test]
fn test_vt_tier25b_find_min_step() {
    fn branch_context(branch_taken: bool) -> VerificationContext {
        let mut ctx = VerificationContext::new();
        ctx.enable_overflow_checks();
        ctx.declare_var_parsed("s", "Seq<i32>");
        ctx.declare_var_parsed("min_val", "i32");
        ctx.declare_var_parsed("min_val_new", "i32");

        ctx.push_assume("len", "s.len() == 3");

        // IH: min_val <= s[0] and min_val <= s[1]
        ctx.push_assume("ih_s0", "min_val <= s.index(0)");
        ctx.push_assume("ih_s1", "min_val <= s.index(1)");

        // Prove each conditional branch separately; the disjunctive encoding
        // is semantically equivalent but current ay times out on it.
        if branch_taken {
            ctx.push_assume("branch_taken", "s.index(2) < min_val");
            ctx.push_assume("update_taken", "min_val_new == s.index(2)");
        } else {
            ctx.push_assume("branch_not_taken", "s.index(2) >= min_val");
            ctx.push_assume("update_not_taken", "min_val_new == min_val");
        }

        // Invariant extended: min_val_new <= all three elements
        ctx.push_assert("new_le_s0", "min_val_new <= s.index(0)");
        ctx.push_assert("new_le_s1", "min_val_new <= s.index(1)");
        ctx.push_assert("new_le_s2", "min_val_new <= s.index(2)");
        ctx
    }

    let result_taken = branch_context(true).verify();
    assert!(
        matches!(result_taken, VerifyResult::Verified),
        "TIER 25b STEP: find min taken branch should verify under overflow: {:?}",
        result_taken,
    );

    let result_not_taken = branch_context(false).verify();
    assert!(
        matches!(result_not_taken, VerifyResult::Verified),
        "TIER 25b STEP: find min not-taken branch should verify under overflow: {:?}",
        result_not_taken,
    );
}

/// Tier 25b EXIT: Find minimum concrete 4-element execution.
///
/// s = [30, 10, 50, 20]. Execute find-min step-by-step:
///   i=0: min=30. i=1: 10<30→min=10. i=2: 50>=10→min=10. i=3: 20>=10→min=10.
/// Postcondition: min_val == 10, min_val <= all elements.
///
/// Discrimination: removing step1 breaks the proof (10 < 30 transition).
#[test]
fn test_vt_tier25b_find_min_exit() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("m0", "i32"); // min_val after i=0
    ctx.declare_var_parsed("m1", "i32"); // min_val after i=1
    ctx.declare_var_parsed("m2", "i32"); // min_val after i=2
    ctx.declare_var_parsed("m3", "i32"); // min_val after i=3

    ctx.push_assume("len", "s.len() == 4");
    ctx.push_assume("s0", "s.index(0) == 30");
    ctx.push_assume("s1", "s.index(1) == 10");
    ctx.push_assume("s2", "s.index(2) == 50");
    ctx.push_assume("s3", "s.index(3) == 20");

    // Step-by-step execution
    ctx.push_assume("step0", "m0 == s.index(0)");
    ctx.push_assume(
        "step1",
        "(s.index(1) < m0 && m1 == s.index(1)) || (s.index(1) >= m0 && m1 == m0)",
    );
    ctx.push_assume(
        "step2",
        "(s.index(2) < m1 && m2 == s.index(2)) || (s.index(2) >= m1 && m2 == m1)",
    );
    ctx.push_assume(
        "step3",
        "(s.index(3) < m2 && m3 == s.index(3)) || (s.index(3) >= m2 && m3 == m2)",
    );

    // Postcondition: final min is 10 and <= all elements
    ctx.push_assert("min_is_10", "m3 == 10");
    ctx.push_assert("min_le_s0", "m3 <= s.index(0)");
    ctx.push_assert("min_le_s1", "m3 <= s.index(1)");
    ctx.push_assert("min_le_s2", "m3 <= s.index(2)");
    ctx.push_assert("min_le_s3", "m3 <= s.index(3)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 25b EXIT: find min exit should verify under overflow: {:?}",
        result,
    );
}

/// Tier 25b NEGATIVE: Wrong comparison direction misses minimum.
///
/// If we use `s[i] > min_val` instead of `s[i] < min_val`, we track
/// the maximum, not the minimum. The min_val <= s[j] invariant breaks.
#[test]
fn test_vt_tier25b_find_min_wrong_comparison_negative() {
    let mut ctx = VerificationContext::new();
    ctx.enable_overflow_checks();
    ctx.declare_var_parsed("s", "Seq<i32>");
    ctx.declare_var_parsed("min_val", "i32");
    ctx.declare_var_parsed("min_val_new", "i32");

    ctx.push_assume("len", "s.len() == 3");
    ctx.push_assume("s0", "s.index(0) == 30");
    ctx.push_assume("s1", "s.index(1) == 10");
    ctx.push_assume("s2", "s.index(2) == 50");

    // Init: min_val = s[0] = 30
    ctx.push_assume("init", "min_val == s.index(0)");

    // WRONG: use > instead of <. At i=1: 10 > 30 is false → keep 30.
    // At i=2: 50 > 30 is true → min_val_new = 50. But 50 is the MAX.
    ctx.push_assume(
        "wrong_step1",
        "(s.index(1) > min_val && min_val == s.index(1)) || \
         (s.index(1) <= min_val && min_val == min_val)",
    );
    ctx.push_assume(
        "wrong_step2",
        "(s.index(2) > min_val && min_val_new == s.index(2)) || \
         (s.index(2) <= min_val && min_val_new == min_val)",
    );

    // Should fail: min_val_new is 50, not <= s[1]=10
    ctx.push_assert("wrong_le_s1", "min_val_new <= s.index(1)");

    let result = ctx.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 25b NEG: wrong comparison must produce Counterexample for min property: {:?}",
        result,
    );
}
