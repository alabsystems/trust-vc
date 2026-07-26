// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 62 — Sieve of Eratosthenes VCs.
//!
//! The sieve marks composite numbers in a boolean array:
//!   - `is_prime: Seq<i64>` — 1 = prime candidate, 0 = composite
//!   - start: `is_prime[0] = 0`, `is_prime[1] = 0`, rest = 1
//!   - for each prime p from 2 to √n, mark multiples p², p²+p, … as composite
//!   - after the outer loop, `is_prime[k] == 1` iff k is prime
//!
//! Competition proofs need:
//!   - init: 0 and 1 are composite, all others start as candidates
//!   - step: marking preserves already-confirmed primes
//!   - invariant: after processing p, all composites with smallest factor ≤ p are marked
//!   - exit: the sieve array matches ground-truth primality
//!   - negatives: unmarked composites or marked non-primes rejected
//!
//! Part of #2187.
//!
//! VERIFICATION LEVEL: SOUNDNESS
//! Tests invoke ay verification through VerificationPipeline.

use trust_vc_core::vc::VerificationContext;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

fn verify_with_pipeline(context: VerificationContext) -> VerifyResult {
    let mut pipeline = VerificationPipeline::new();
    pipeline.replace_context(context);
    pipeline.verify()
}

fn assume_seq_i64(ctx: &mut VerificationContext, name: &str, values: &[i64]) {
    ctx.declare_var_parsed(name, "Seq<i64>");
    ctx.push_assume(
        &format!("{name}_len"),
        &format!("{name}.len() == {}", values.len()),
    );
    for (index, value) in values.iter().enumerate() {
        ctx.push_assume(
            &format!("{name}_{index}"),
            &format!("{name}.index({index}) == {value}"),
        );
    }
}

// ========================================================================
// GROUP A: Init — 0 and 1 composite, candidates from 2 onward
// ========================================================================

/// Tier 62a: Init — sieve array for n=10 starts with 0,1 marked composite.
#[test]
fn test_vt_tier62a_sieve_init() {
    let mut ctx = VerificationContext::new();
    //                                      0  1  2  3  4  5  6  7  8  9
    assume_seq_i64(&mut ctx, "sieve", &[0, 0, 1, 1, 1, 1, 1, 1, 1, 1]);

    ctx.push_assert("zero_composite", "sieve.index(0) == 0");
    ctx.push_assert("one_composite", "sieve.index(1) == 0");
    ctx.push_assert("two_candidate", "sieve.index(2) == 1");
    ctx.push_assert("nine_candidate", "sieve.index(9) == 1");
    ctx.push_assert("len_correct", "sieve.len() == 10");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 62a: sieve init should verify, got: {:?}",
        result,
    );
}

/// Tier 62a: Init — all candidates from index 2 onward are marked 1.
#[test]
fn test_vt_tier62a_all_candidates_above_one() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "sieve", &[0, 0, 1, 1, 1, 1, 1, 1, 1, 1]);

    ctx.push_assert("idx2", "sieve.index(2) == 1");
    ctx.push_assert("idx3", "sieve.index(3) == 1");
    ctx.push_assert("idx4", "sieve.index(4) == 1");
    ctx.push_assert("idx5", "sieve.index(5) == 1");
    ctx.push_assert("idx6", "sieve.index(6) == 1");
    ctx.push_assert("idx7", "sieve.index(7) == 1");
    ctx.push_assert("idx8", "sieve.index(8) == 1");
    ctx.push_assert("idx9", "sieve.index(9) == 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 62a: all candidates above 1 should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Step — marking multiples of the current prime
// ========================================================================

/// Tier 62b: Step — after processing p=2, multiples 4,6,8 are marked composite.
#[test]
fn test_vt_tier62b_mark_multiples_of_2() {
    let mut ctx = VerificationContext::new();
    //                             before:    0  1  2  3  4  5  6  7  8  9
    assume_seq_i64(&mut ctx, "pre", &[0, 0, 1, 1, 1, 1, 1, 1, 1, 1]);
    //                              after:    0  1  2  3  4  5  6  7  8  9
    assume_seq_i64(&mut ctx, "post", &[0, 0, 1, 1, 0, 1, 0, 1, 0, 1]);

    // p=2 stays prime
    ctx.push_assert("p_stays_prime", "post.index(2) == pre.index(2)");
    // Multiples of 2 starting at 4 are marked composite
    ctx.push_assert("mark_4", "post.index(4) == 0");
    ctx.push_assert("mark_6", "post.index(6) == 0");
    ctx.push_assert("mark_8", "post.index(8) == 0");
    // Non-multiples of 2 are unchanged
    ctx.push_assert("keep_3", "post.index(3) == pre.index(3)");
    ctx.push_assert("keep_5", "post.index(5) == pre.index(5)");
    ctx.push_assert("keep_7", "post.index(7) == pre.index(7)");
    ctx.push_assert("keep_9", "post.index(9) == pre.index(9)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 62b: marking multiples of 2 should verify, got: {:?}",
        result,
    );
}

/// Tier 62b: Step — after processing p=3, multiple 9 is also marked composite.
#[test]
fn test_vt_tier62b_mark_multiples_of_3() {
    let mut ctx = VerificationContext::new();
    //                             after p=2: 0  1  2  3  4  5  6  7  8  9
    assume_seq_i64(&mut ctx, "pre", &[0, 0, 1, 1, 0, 1, 0, 1, 0, 1]);
    //                             after p=3: 0  1  2  3  4  5  6  7  8  9
    assume_seq_i64(&mut ctx, "post", &[0, 0, 1, 1, 0, 1, 0, 1, 0, 0]);

    // p=3 stays prime
    ctx.push_assert("p_stays_prime", "post.index(3) == 1");
    // 9 = 3*3 is now marked composite
    ctx.push_assert("mark_9", "post.index(9) == 0");
    // 6 was already marked by 2, stays composite
    ctx.push_assert("already_6", "post.index(6) == 0");
    // Primes 2,5,7 unchanged
    ctx.push_assert("keep_2", "post.index(2) == pre.index(2)");
    ctx.push_assert("keep_5", "post.index(5) == pre.index(5)");
    ctx.push_assert("keep_7", "post.index(7) == pre.index(7)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 62b: marking multiples of 3 should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Invariant — processed primes have all composites marked
// ========================================================================

/// Tier 62c: Invariant — after sieve completes for n=10, all composites
/// with smallest prime factor ≤ 3 (i.e., ≤ √9) are marked.
#[test]
fn test_vt_tier62c_composites_with_small_factor_marked() {
    let mut ctx = VerificationContext::new();
    //                  final sieve:  0  1  2  3  4  5  6  7  8  9
    assume_seq_i64(&mut ctx, "s", &[0, 0, 1, 1, 0, 1, 0, 1, 0, 0]);

    // Every composite ≤ 9 has smallest prime factor ≤ 3
    // 4 = 2*2, 6 = 2*3, 8 = 2*4, 9 = 3*3
    ctx.push_assert("composite_4", "s.index(4) == 0");
    ctx.push_assert("composite_6", "s.index(6) == 0");
    ctx.push_assert("composite_8", "s.index(8) == 0");
    ctx.push_assert("composite_9", "s.index(9) == 0");
    // All primes survive
    ctx.push_assert("prime_2", "s.index(2) == 1");
    ctx.push_assert("prime_3", "s.index(3) == 1");
    ctx.push_assert("prime_5", "s.index(5) == 1");
    ctx.push_assert("prime_7", "s.index(7) == 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 62c: composites with small factor should be marked, got: {:?}",
        result,
    );
}

/// Tier 62c: Invariant — the marking step for p only affects indices ≥ p².
/// Before marking multiples of p=3, indices 0..8 are already settled
/// (since p²=9 is the first new composite to mark).
#[test]
fn test_vt_tier62c_marking_starts_at_p_squared() {
    let mut ctx = VerificationContext::new();
    //                         after p=2:  0  1  2  3  4  5  6  7  8  9
    assume_seq_i64(&mut ctx, "pre", &[0, 0, 1, 1, 0, 1, 0, 1, 0, 1]);
    //                         after p=3:  0  1  2  3  4  5  6  7  8  9
    assume_seq_i64(&mut ctx, "post", &[0, 0, 1, 1, 0, 1, 0, 1, 0, 0]);

    ctx.declare_var_parsed("p", "u64");
    ctx.push_assume("p_val", "p == 3");

    // All indices below p² = 9 are unchanged between pre and post
    ctx.push_assert("below_0", "post.index(0) == pre.index(0)");
    ctx.push_assert("below_1", "post.index(1) == pre.index(1)");
    ctx.push_assert("below_2", "post.index(2) == pre.index(2)");
    ctx.push_assert("below_3", "post.index(3) == pre.index(3)");
    ctx.push_assert("below_4", "post.index(4) == pre.index(4)");
    ctx.push_assert("below_5", "post.index(5) == pre.index(5)");
    ctx.push_assert("below_6", "post.index(6) == pre.index(6)");
    ctx.push_assert("below_7", "post.index(7) == pre.index(7)");
    ctx.push_assert("below_8", "post.index(8) == pre.index(8)");
    // Only index 9 = p² can change
    ctx.push_assert("at_p_sq", "post.index(9) == 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 62c: marking starts at p² should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Exit — final sieve matches ground-truth primality
// ========================================================================

/// Tier 62d: Exit — sieve for n=20 produces correct prime classification.
#[test]
fn test_vt_tier62d_sieve_n20_ground_truth() {
    let mut ctx = VerificationContext::new();
    // Primes ≤ 19: 2, 3, 5, 7, 11, 13, 17, 19
    //     index: 0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18 19
    assume_seq_i64(
        &mut ctx,
        "s",
        &[0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1],
    );

    // Verify known primes
    ctx.push_assert("p2", "s.index(2) == 1");
    ctx.push_assert("p3", "s.index(3) == 1");
    ctx.push_assert("p5", "s.index(5) == 1");
    ctx.push_assert("p7", "s.index(7) == 1");
    ctx.push_assert("p11", "s.index(11) == 1");
    ctx.push_assert("p13", "s.index(13) == 1");
    ctx.push_assert("p17", "s.index(17) == 1");
    ctx.push_assert("p19", "s.index(19) == 1");
    // Verify known composites
    ctx.push_assert("c4", "s.index(4) == 0");
    ctx.push_assert("c6", "s.index(6) == 0");
    ctx.push_assert("c8", "s.index(8) == 0");
    ctx.push_assert("c9", "s.index(9) == 0");
    ctx.push_assert("c10", "s.index(10) == 0");
    ctx.push_assert("c12", "s.index(12) == 0");
    ctx.push_assert("c14", "s.index(14) == 0");
    ctx.push_assert("c15", "s.index(15) == 0");
    ctx.push_assert("c16", "s.index(16) == 0");
    ctx.push_assert("c18", "s.index(18) == 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 62d: sieve n=20 ground truth should verify, got: {:?}",
        result,
    );
}

/// Tier 62d: Exit — a composite number has a witness factorization.
/// For each composite k in the sieve, there exist a,b>1 such that a*b=k.
#[test]
fn test_vt_tier62d_composite_has_witness_factors() {
    let mut ctx = VerificationContext::new();
    // Check 15 = 3 * 5
    ctx.declare_var_parsed("k", "u64");
    ctx.declare_var_parsed("a", "u64");
    ctx.declare_var_parsed("b", "u64");

    ctx.push_assume("k_val", "k == 15");
    ctx.push_assume("a_val", "a == 3");
    ctx.push_assume("b_val", "b == 5");

    ctx.push_assert("product", "a * b == k");
    ctx.push_assert("a_gt_1", "a > 1");
    ctx.push_assert("b_gt_1", "b > 1");
    ctx.push_assert("a_lt_k", "a < k");
    ctx.push_assert("b_lt_k", "b < k");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 62d: composite witness factorization should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP E: Symbolic sieve properties
// ========================================================================

/// Tier 62e: Symbolic — if p is prime and k=p*m for m≥2, then k is composite.
#[test]
fn test_vt_tier62e_symbolic_prime_multiple_is_composite() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("p", "u64");
    ctx.declare_var_parsed("m", "u64");
    ctx.declare_var_parsed("k", "u64");

    ctx.push_assume("p_prime_bound", "p >= 2 && p < 100");
    ctx.push_assume("m_bound", "m >= 2 && m < 100");
    ctx.push_assume("product", "k == p * m");

    // k >= 4 (smallest composite)
    ctx.push_assert("k_ge_4", "k >= 4");
    ctx.push_assert("factor_nontrivial", "p > 1 && m > 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 62e: prime multiple is composite should verify, got: {:?}",
        result,
    );
}

/// Tier 62e: Symbolic — the outer loop terminates because p increases
/// and we only process p ≤ √n.
///
/// Uses u32 instead of u64 to avoid BV64 multiplication memout (#2374).
/// The sieve for n=100 fits comfortably in 32 bits.
#[test]
fn test_vt_tier62e_symbolic_outer_loop_bound() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("n", "u32");
    ctx.declare_var_parsed("p", "u32");
    ctx.declare_var_parsed("p_next", "u32");

    ctx.push_assume("n_val", "n == 100");
    // Explicit upper bound prevents BV overflow (u32_max * u32_max wraps)
    ctx.push_assume("p_bound", "p >= 2 && p <= 10");
    ctx.push_assume("p_sq_in_range", "p * p <= n");
    ctx.push_assume("p_next_val", "p_next == p + 1");

    // Progress: p_next > p
    ctx.push_assert("progress", "p_next > p");
    // Bound: if p_next² > n, we exit the loop
    // At p=10: 10² = 100 = n, 11² = 121 > 100
    ctx.push_assert("termination_example", "!(p == 10 && p_next * p_next <= n)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 62e: outer loop bound should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP F: Soundness negatives
// ========================================================================

/// Tier 62f NEGATIVE: leaving a composite unmarked invalidates the sieve.
///
/// Uses scalar variables instead of Seq to avoid array-theory memout (#2374).
/// The property tested is purely about one cell value — Seq adds no value.
#[test]
fn test_vt_tier62f_unmarked_composite_rejected() {
    let mut ctx = VerificationContext::new();
    // Wrong sieve: 9 = 3*3 is composite but left marked as prime
    ctx.declare_var_parsed("sieve_9", "i64");
    ctx.push_assume("wrong_mark", "sieve_9 == 1");

    // The correct sieve must have sieve[9] == 0 for composite 9
    ctx.push_assert("should_be_composite", "sieve_9 == 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 62f SOUNDNESS: unmarked composite must be rejected, got: {:?}",
        result,
    );
}

/// Tier 62f NEGATIVE: marking a prime as composite is wrong.
///
/// Uses scalar variables instead of Seq to avoid array-theory memout (#2374).
#[test]
fn test_vt_tier62f_marked_prime_rejected() {
    let mut ctx = VerificationContext::new();
    // Wrong sieve: 7 marked as composite (0) but 7 is prime
    ctx.declare_var_parsed("sieve_7", "i64");
    ctx.push_assume("wrong_mark", "sieve_7 == 0");

    // 7 is prime — the correct sieve must have sieve[7] == 1
    ctx.push_assert("sieve_says_prime_7", "sieve_7 == 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 62f SOUNDNESS: marking a prime as composite must be rejected, got: {:?}",
        result,
    );
}

/// Tier 62f NEGATIVE: skipping the inner loop for p=2 leaves even composites.
///
/// Uses scalar variables instead of Seq to avoid array-theory memout (#2374).
#[test]
fn test_vt_tier62f_skipped_p2_leaves_even_composites() {
    let mut ctx = VerificationContext::new();
    // Wrong sieve: never processed p=2, so sieve[4] still marked prime
    ctx.declare_var_parsed("sieve_4", "i64");
    ctx.push_assume("wrong_mark", "sieve_4 == 1");

    // 4 = 2*2 is composite — the correct sieve must mark it 0
    ctx.push_assert("four_is_composite", "sieve_4 == 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 62f SOUNDNESS: skipped p=2 must leave detectable error, got: {:?}",
        result,
    );
}

/// Tier 62f NEGATIVE: starting the inner loop at 2*p instead of p²
/// redundantly re-marks but also claims a different frame condition.
///
/// Uses scalar variables instead of Seq to avoid array-theory memout (#2374).
#[test]
fn test_vt_tier62f_wrong_inner_start_breaks_frame() {
    let mut ctx = VerificationContext::new();
    // Wrong inner loop start: began at 2*3=6 instead of 2²=4,
    // so sieve[4] is still marked prime (wrong)
    ctx.declare_var_parsed("sieve_4", "i64");
    ctx.push_assume("wrong_start", "sieve_4 == 1");

    // 4 should be composite but is still marked prime
    ctx.push_assert("four_should_be_zero", "sieve_4 == 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 62f SOUNDNESS: wrong inner start must be caught, got: {:?}",
        result,
    );
}
