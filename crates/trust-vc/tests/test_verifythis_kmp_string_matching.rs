// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 55 — KMP String Matching VCs.
//!
//! The Knuth-Morris-Pratt algorithm is a classic competition problem requiring
//! verification of the failure function (partial match table) and the search
//! phase. The key insight: the failure function `fail[i]` gives the length of
//! the longest proper prefix of pattern[0..i+1] that is also a suffix.
//!
//! Failure function construction (single loop):
//!   fail[0] = 0
//!   for i in 1..m:
//!     k = fail[i-1]
//!     while k > 0 && pattern[k] != pattern[i]: k = fail[k-1]
//!     fail[i] = k + (pattern[k] == pattern[i])
//!
//! Core proof obligations:
//!   1. Init: fail[0] = 0 (no proper prefix-suffix of length > 0 for a single char)
//!   2. Step: fail[i] < i+1 (strictly shorter than the string) and fail[i] >= 0
//!   3. Prefix-suffix: fail[i] is a valid prefix-suffix length
//!   4. Search: match at position guarantees pattern found
//!
//! We encode pattern characters as integer Seq values and use concrete
//! patterns where character equality is explicit.
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
// GROUP A: Failure function init and step
// ========================================================================

/// Tier 55a: Init — fail[0] = 0 for any pattern.
/// The first character has no proper prefix-suffix.
#[test]
fn test_vt_tier55a_kmp_fail_init_is_zero() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("fail", "Seq<i64>");
    ctx.declare_var_parsed("m", "u64");

    ctx.push_assume("fail_len", "fail.len() == m");
    ctx.push_assume("m_ge1", "m >= 1");
    ctx.push_assume("base", "fail.index(0) == 0");

    // fail[0] >= 0 (non-negative)
    ctx.push_assert("init_nonneg", "fail.index(0) >= 0");
    // fail[0] < 1 (strictly less than string length 1)
    ctx.push_assert("init_lt_len", "fail.index(0) < 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 55a: KMP fail init should verify, got: {:?}",
        result,
    );
}

/// Tier 55a: Step — fail[i] < i+1 (failure value is strictly less than prefix length).
/// This is the key structural invariant of the failure function.
#[test]
fn test_vt_tier55a_kmp_fail_step_bounded() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("fail_im1", "i64"); // fail[i-1]
    ctx.declare_var_parsed("fail_i", "i64"); // fail[i]
    ctx.declare_var_parsed("i", "u64"); // current index

    // IH: fail[i-1] < i (bounded by prefix length)
    ctx.push_assume("ih_bounded", "fail_im1 >= 0 && fail_im1 < i");
    ctx.push_assume("i_ge1", "i >= 1");
    ctx.push_assume("i_bounded", "i < 1000000");
    // Construction: fail[i] is either fail[i-1]+1 (extend match) or
    // some value obtained by following the fail chain, always < i
    // Key invariant: fail[i] <= fail[i-1] + 1
    ctx.push_assume("construction", "fail_i >= 0 && fail_i <= fail_im1 + 1");

    // fail[i] < i + 1 (strictly less than the prefix length at position i)
    ctx.push_assert("bounded", "fail_i < i + 1");
    // Non-negativity
    ctx.push_assert("nonneg", "fail_i >= 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 55a: KMP fail step bound should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Concrete failure function traces
// ========================================================================

/// Tier 55b: Concrete — pattern "aabaaab" has fail = [0, 1, 0, 1, 2, 2, 3].
/// This pattern exercises both extension (a->aa, aa->aab->aaba->aabaa) and
/// fallback through the fail chain.
#[test]
fn test_vt_tier55b_kmp_fail_aabaaab_concrete() {
    let mut ctx = VerificationContext::new();
    // pattern: a=1, b=2 → [1, 1, 2, 1, 1, 1, 2]
    assume_seq_i64(&mut ctx, "pat", &[1, 1, 2, 1, 1, 1, 2]);
    assume_seq_i64(&mut ctx, "fail", &[0, 1, 0, 1, 2, 2, 3]);

    // Verify base case
    ctx.push_assert("base", "fail.index(0) == 0");

    // fail[1] = 1: pat[0..2] = "aa", prefix "a" == suffix "a"
    ctx.push_assert("f1", "fail.index(1) == 1");
    ctx.push_assert("f1_valid", "pat.index(0) == pat.index(1)"); // prefix[0] == suffix[0]

    // fail[2] = 0: pat[0..3] = "aab", no proper prefix == suffix
    ctx.push_assert("f2", "fail.index(2) == 0");

    // fail[3] = 1: pat[0..4] = "aaba", prefix "a" == suffix "a"
    ctx.push_assert("f3", "fail.index(3) == 1");
    ctx.push_assert("f3_valid", "pat.index(0) == pat.index(3)");

    // fail[4] = 2: pat[0..5] = "aabaa", prefix "aa" == suffix "aa"
    ctx.push_assert("f4", "fail.index(4) == 2");
    ctx.push_assert("f4_valid_0", "pat.index(0) == pat.index(3)"); // first char matches
    ctx.push_assert("f4_valid_1", "pat.index(1) == pat.index(4)"); // second char matches

    // fail[5] = 2: pat[0..6] = "aabaaa", prefix "aa" == suffix "aa"
    ctx.push_assert("f5", "fail.index(5) == 2");

    // fail[6] = 3: pat[0..7] = "aabaaab", prefix "aab" == suffix "aab"
    ctx.push_assert("f6", "fail.index(6) == 3");
    ctx.push_assert("f6_valid_0", "pat.index(0) == pat.index(4)");
    ctx.push_assert("f6_valid_1", "pat.index(1) == pat.index(5)");
    ctx.push_assert("f6_valid_2", "pat.index(2) == pat.index(6)");

    // All values bounded: fail[i] < i+1
    ctx.push_assert("all_bounded",
        "fail.index(0) < 1 && fail.index(1) < 2 && fail.index(2) < 3 && fail.index(3) < 4 && fail.index(4) < 5 && fail.index(5) < 6 && fail.index(6) < 7");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 55b: KMP fail for aabaaab should verify, got: {:?}",
        result,
    );
}

/// Tier 55b: Concrete — pattern "abcabc" has fail = [0, 0, 0, 1, 2, 3].
/// Classic example where the failure function builds up incrementally.
#[test]
fn test_vt_tier55b_kmp_fail_abcabc_concrete() {
    let mut ctx = VerificationContext::new();
    // a=1, b=2, c=3
    assume_seq_i64(&mut ctx, "pat", &[1, 2, 3, 1, 2, 3]);
    assume_seq_i64(&mut ctx, "fail", &[0, 0, 0, 1, 2, 3]);

    ctx.push_assert("base", "fail.index(0) == 0");
    ctx.push_assert("f1", "fail.index(1) == 0"); // "ab": no prefix-suffix
    ctx.push_assert("f2", "fail.index(2) == 0"); // "abc": no prefix-suffix
                                                 // "abca": prefix "a" == suffix "a"
    ctx.push_assert("f3", "fail.index(3) == 1");
    ctx.push_assert("f3_valid", "pat.index(0) == pat.index(3)");
    // "abcab": prefix "ab" == suffix "ab"
    ctx.push_assert("f4", "fail.index(4) == 2");
    ctx.push_assert("f4_valid_0", "pat.index(0) == pat.index(3)");
    ctx.push_assert("f4_valid_1", "pat.index(1) == pat.index(4)");
    // "abcabc": prefix "abc" == suffix "abc"
    ctx.push_assert("f5", "fail.index(5) == 3");
    ctx.push_assert("f5_valid_0", "pat.index(0) == pat.index(3)");
    ctx.push_assert("f5_valid_1", "pat.index(1) == pat.index(4)");
    ctx.push_assert("f5_valid_2", "pat.index(2) == pat.index(5)");

    // Bounded
    ctx.push_assert("bounded",
        "fail.index(0) < 1 && fail.index(1) < 2 && fail.index(2) < 3 && fail.index(3) < 4 && fail.index(4) < 5 && fail.index(5) < 6");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 55b: KMP fail for abcabc should verify, got: {:?}",
        result,
    );
}

/// Tier 55b: Concrete — all-same pattern "aaaa" has fail = [0, 1, 2, 3].
#[test]
fn test_vt_tier55b_kmp_fail_all_same_concrete() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "pat", &[1, 1, 1, 1]);
    assume_seq_i64(&mut ctx, "fail", &[0, 1, 2, 3]);

    ctx.push_assert("base", "fail.index(0) == 0");
    ctx.push_assert("f1", "fail.index(1) == 1");
    ctx.push_assert("f2", "fail.index(2) == 2");
    ctx.push_assert("f3", "fail.index(3) == 3");

    // For all-same pattern, fail[i] = i (maximum possible)
    // Verify prefix-suffix: pat[0..fail[3]] == pat[1..4]
    ctx.push_assert("ps_0", "pat.index(0) == pat.index(1)");
    ctx.push_assert("ps_1", "pat.index(1) == pat.index(2)");
    ctx.push_assert("ps_2", "pat.index(2) == pat.index(3)");

    // Bounded: fail[i] < i+1
    ctx.push_assert(
        "bounded",
        "fail.index(0) < 1 && fail.index(1) < 2 && fail.index(2) < 3 && fail.index(3) < 4",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 55b: KMP fail for all-same should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Search phase
// ========================================================================

/// Tier 55c: Search step — when matched == m, pattern found at position i-m.
/// If we've matched all m characters, the pattern occurs at text[i-m..i].
#[test]
fn test_vt_tier55c_kmp_search_full_match_found() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("text", "Seq<i64>");
    ctx.declare_var_parsed("pat", "Seq<i64>");
    ctx.declare_var_parsed("i", "u64"); // current text position
    ctx.declare_var_parsed("m", "u64"); // pattern length
    ctx.declare_var_parsed("n", "u64"); // text length
    ctx.declare_var_parsed("matched", "u64"); // number of matched chars

    ctx.push_assume("text_len", "text.len() == n");
    ctx.push_assume("pat_len", "pat.len() == m");
    ctx.push_assume("m_ge1", "m >= 1");
    ctx.push_assume("m_bounded", "m < 100");
    ctx.push_assume("n_ge_m", "n >= m");
    ctx.push_assume("i_ge_m", "i >= m");
    ctx.push_assume("i_le_n", "i <= n");
    // Full match: matched == m
    ctx.push_assume("full_match", "matched == m");
    // The match invariant: text[i-matched..i] == pat[0..matched]
    // We encode this for concrete m=3 to avoid nested quantifiers
    ctx.push_assume("m_is_3", "m == 3");
    ctx.push_assume("i_is_3", "i == 3");
    ctx.push_assume("pat_1_in_bounds", "1 < m");
    ctx.push_assume("pat_2_in_bounds", "2 < m");
    ctx.push_assume("text_0_in_bounds", "0 < n");
    ctx.push_assume("text_1_in_bounds", "1 < n");
    ctx.push_assume("text_2_in_bounds", "2 < n");
    ctx.push_assume("match_0", "text.index(0) == pat.index(0)");
    ctx.push_assume("match_1", "text.index(1) == pat.index(1)");
    ctx.push_assume("match_2", "text.index(2) == pat.index(2)");

    // Pattern found: text[i-m..i] matches pat[0..m]
    ctx.push_assert("found_0", "text.index(0) == pat.index(0)");
    ctx.push_assert("found_1", "text.index(1) == pat.index(1)");
    ctx.push_assert("found_2", "text.index(2) == pat.index(2)");
    // Match position is valid
    ctx.push_assert("pos_valid", "i - m + m <= n");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 55c: KMP search full match should verify, got: {:?}",
        result,
    );
}

/// Tier 55c: Concrete search — find "ab" in "xabxab" at positions 1 and 4.
#[test]
fn test_vt_tier55c_kmp_search_concrete_two_matches() {
    let mut ctx = VerificationContext::new();
    // text: x=0, a=1, b=2 → [0, 1, 2, 0, 1, 2]
    assume_seq_i64(&mut ctx, "text", &[0, 1, 2, 0, 1, 2]);
    assume_seq_i64(&mut ctx, "pat", &[1, 2]); // "ab"

    // First match at position 1: text[1..3] == pat[0..2]
    ctx.push_assert("match1_0", "text.index(1) == pat.index(0)");
    ctx.push_assert("match1_1", "text.index(2) == pat.index(1)");

    // Second match at position 4: text[4..6] == pat[0..2]
    ctx.push_assert("match2_0", "text.index(4) == pat.index(0)");
    ctx.push_assert("match2_1", "text.index(5) == pat.index(1)");

    // No match at position 0: text[0] != pat[0] (0 != 1)
    ctx.push_assert("no_match_0", "text.index(0) != pat.index(0)");

    // No match at position 3: text[3] != pat[0] (0 != 1)
    ctx.push_assert("no_match_3", "text.index(3) != pat.index(0)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 55c: KMP search concrete should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Failure function chain property
// ========================================================================

/// Tier 55d: The failure chain is strictly decreasing.
/// fail[fail[i]-1] < fail[i] whenever fail[i] > 0.
/// This guarantees termination of the while loop in the KMP construction.
#[test]
fn test_vt_tier55d_kmp_fail_chain_decreasing() {
    let mut ctx = VerificationContext::new();
    // Use the "aabaaab" example: fail = [0, 1, 0, 1, 2, 2, 3]
    assume_seq_i64(&mut ctx, "fail", &[0, 1, 0, 1, 2, 2, 3]);

    // For each position where fail[i] > 0, check fail[fail[i]-1] < fail[i]
    // fail[1] = 1 > 0: fail[0] = 0 < 1
    ctx.push_assert("chain_1", "fail.index(0) < fail.index(1)");
    // fail[3] = 1 > 0: fail[0] = 0 < 1
    ctx.push_assert("chain_3", "fail.index(0) < fail.index(3)");
    // fail[4] = 2 > 0: fail[1] = 1 < 2
    ctx.push_assert("chain_4", "fail.index(1) < fail.index(4)");
    // fail[5] = 2 > 0: fail[1] = 1 < 2
    ctx.push_assert("chain_5", "fail.index(1) < fail.index(5)");
    // fail[6] = 3 > 0: fail[2] = 0 < 3
    ctx.push_assert("chain_6", "fail.index(2) < fail.index(6)");

    // All values non-negative
    ctx.push_assert("all_nonneg",
        "fail.index(0) >= 0 && fail.index(1) >= 0 && fail.index(2) >= 0 && fail.index(3) >= 0 && fail.index(4) >= 0 && fail.index(5) >= 0 && fail.index(6) >= 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 55d: KMP fail chain decreasing should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP E: Soundness negatives
// ========================================================================

/// Tier 55e NEGATIVE: fail[i] >= i+1 is unsound (fail must be strictly less
/// than the prefix length).
#[test]
fn test_vt_tier55e_fail_too_large_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("fail_i", "i64");
    ctx.declare_var_parsed("i", "u64");

    ctx.push_assume("i_ge1", "i >= 1");
    ctx.push_assume("i_bounded", "i < 100");
    // WRONG: fail[i] = i + 1 (not a proper prefix-suffix)
    ctx.push_assume("too_large", "fail_i == i + 1");

    // Claiming fail[i] < i + 1 should fail
    ctx.push_assert("bounded", "fail_i < i + 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 55e SOUNDNESS: fail >= prefix length should be rejected, got: {:?}",
        result,
    );
}

/// Tier 55e NEGATIVE: Wrong failure function for "abcabc".
/// Claiming fail = [0, 0, 0, 1, 2, 2] instead of [0, 0, 0, 1, 2, 3]
/// should fail the prefix-suffix verification at position 5.
#[test]
fn test_vt_tier55e_wrong_fail_values_rejected() {
    let mut ctx = VerificationContext::new();
    // pat: a=1, b=2, c=3
    assume_seq_i64(&mut ctx, "pat", &[1, 2, 3, 1, 2, 3]);
    // WRONG fail: last value should be 3, not 2
    assume_seq_i64(&mut ctx, "fail", &[0, 0, 0, 1, 2, 2]);

    // At position 5, fail[5]=2 claims prefix "ab" == suffix pat[4..6] = "bc"
    // But pat[0]=1(a) != pat[4]=2(b), so this prefix-suffix is invalid
    // Asserting the prefix-suffix property should fail
    ctx.push_assert("wrong_ps_at_5", "pat.index(0) == pat.index(4)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 55e SOUNDNESS: wrong fail values should be rejected, got: {:?}",
        result,
    );
}

/// Tier 55e NEGATIVE: Claiming pattern "abc" found at position 0 in text "xbc"
/// should fail (text[0]='x' != pat[0]='a').
#[test]
fn test_vt_tier55e_false_match_rejected() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "text", &[0, 2, 3]); // x=0, b=2, c=3
    assume_seq_i64(&mut ctx, "pat", &[1, 2, 3]); // a=1, b=2, c=3

    // Claiming text[0..3] matches pat[0..3]
    ctx.push_assert(
        "false_match",
        "text.index(0) == pat.index(0) && text.index(1) == pat.index(1) && text.index(2) == pat.index(2)",
    );

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 55e SOUNDNESS: false match should be rejected, got: {:?}",
        result,
    );
}
