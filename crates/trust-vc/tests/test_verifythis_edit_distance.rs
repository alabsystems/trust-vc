// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 54 — Edit Distance (2D Dynamic Programming) VCs.
//!
//! Edit distance (Levenshtein distance) is the canonical 2D DP competition
//! problem. Given two strings a[0..m] and b[0..n], compute the minimum number
//! of insert/delete/replace operations to transform a into b.
//!
//! The 2D recurrence:
//!   dp[0][j] = j                                (insert j chars)
//!   dp[i][0] = i                                (delete i chars)
//!   dp[i][j] = dp[i-1][j-1]                    if a[i-1] == b[j-1]
//!            = 1 + min(dp[i-1][j],              (delete)
//!                      dp[i][j-1],              (insert)
//!                      dp[i-1][j-1])            (replace)
//!
//! We encode the 2D table as a flat Seq<i64> with row-major layout:
//!   dp[i][j] = dp_flat.index(i * (n+1) + j)
//!
//! Core proof obligations:
//!   1. Init: first row and column satisfy boundary definitions
//!   2. Step: recurrence preserves non-negativity and triangle bounds
//!   3. Exit: dp[m][n] is the edit distance with correct bounds
//!   4. Negatives: wrong recurrence or bounds are rejected
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
// GROUP A: Init — boundary row and column
// ========================================================================

/// Tier 54a: Init — first row dp[0][j] = j for j in 0..=n.
/// For a = "abc" (m=3), b = "xy" (n=2), the first row is [0, 1, 2].
#[test]
fn test_vt_tier54a_edit_distance_first_row_init() {
    let mut ctx = VerificationContext::new();
    // dp for a="abc"(m=3), b="xy"(n=2): dp is (m+1)*(n+1) = 4*3 = 12 entries
    // Row-major: dp[i][j] = dp_flat[i*3 + j]
    // First row: dp[0][0]=0, dp[0][1]=1, dp[0][2]=2
    ctx.declare_var_parsed("dp", "Seq<i64>");
    ctx.push_assume("dp_len", "dp.len() == 12");
    ctx.push_assume("dp_0_0", "dp.index(0) == 0"); // dp[0][0]
    ctx.push_assume("dp_0_1", "dp.index(1) == 1"); // dp[0][1]
    ctx.push_assume("dp_0_2", "dp.index(2) == 2"); // dp[0][2]

    // Non-negativity
    ctx.push_assert("row0_nonneg_0", "dp.index(0) >= 0");
    ctx.push_assert("row0_nonneg_1", "dp.index(1) >= 0");
    ctx.push_assert("row0_nonneg_2", "dp.index(2) >= 0");
    // Monotonicity: dp[0][j] <= dp[0][j+1]
    ctx.push_assert("row0_mono_01", "dp.index(0) <= dp.index(1)");
    ctx.push_assert("row0_mono_12", "dp.index(1) <= dp.index(2)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 54a: edit distance first row init should verify, got: {:?}",
        result,
    );
}

/// Tier 54a: Init — first column dp[i][0] = i for i in 0..=m.
#[test]
fn test_vt_tier54a_edit_distance_first_column_init() {
    let mut ctx = VerificationContext::new();
    // dp for m=3, n=2: dp[i][0] = dp_flat[i*3]
    ctx.declare_var_parsed("dp", "Seq<i64>");
    ctx.push_assume("dp_len", "dp.len() == 12");
    ctx.push_assume("dp_0_0", "dp.index(0) == 0"); // dp[0][0] = i*3+0 = 0
    ctx.push_assume("dp_1_0", "dp.index(3) == 1"); // dp[1][0] = 1*3+0 = 3
    ctx.push_assume("dp_2_0", "dp.index(6) == 2"); // dp[2][0] = 2*3+0 = 6
    ctx.push_assume("dp_3_0", "dp.index(9) == 3"); // dp[3][0] = 3*3+0 = 9

    // Monotonicity down the column
    ctx.push_assert("col0_mono_01", "dp.index(0) <= dp.index(3)");
    ctx.push_assert("col0_mono_12", "dp.index(3) <= dp.index(6)");
    ctx.push_assert("col0_mono_23", "dp.index(6) <= dp.index(9)");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 54a: edit distance first column init should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Step — inductive recurrence
// ========================================================================

/// Tier 54b: Step — matching characters: dp[i][j] = dp[i-1][j-1].
/// When a[i-1] == b[j-1], no operation is needed, so the cost is inherited.
/// The triangle IH: adjacent DP cells differ by at most 1.
#[test]
fn test_vt_tier54b_edit_distance_step_match() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("dp_diag", "i64"); // dp[i-1][j-1]
    ctx.declare_var_parsed("dp_up", "i64"); // dp[i-1][j]
    ctx.declare_var_parsed("dp_left", "i64"); // dp[i][j-1]
    ctx.declare_var_parsed("dp_ij", "i64"); // dp[i][j]

    // IH: all predecessors are non-negative and bounded
    ctx.push_assume("ih_diag_nonneg", "dp_diag >= 0");
    ctx.push_assume("ih_up_nonneg", "dp_up >= 0");
    ctx.push_assume("ih_left_nonneg", "dp_left >= 0");
    ctx.push_assume("ih_diag_bounded", "dp_diag < 1000000");
    ctx.push_assume("ih_up_bounded", "dp_up < 1000000");
    ctx.push_assume("ih_left_bounded", "dp_left < 1000000");
    // IH: adjacent cells differ by at most 1 (DP triangle invariant)
    // dp[i-1][j-1] <= dp[i-1][j] + 1  (diag <= up + 1)
    // dp[i-1][j-1] <= dp[i][j-1] + 1  (diag <= left + 1)
    ctx.push_assume("ih_triangle_diag_up", "dp_diag <= dp_up + 1");
    ctx.push_assume("ih_triangle_diag_left", "dp_diag <= dp_left + 1");
    // Match case: dp[i][j] = dp[i-1][j-1]
    ctx.push_assume("match_recurrence", "dp_ij == dp_diag");

    // dp[i][j] >= 0
    ctx.push_assert("nonneg", "dp_ij >= 0");
    // dp[i][j] <= dp[i-1][j] + 1 (triangle: match inherits diag, diag <= up+1)
    ctx.push_assert("triangle_up", "dp_ij <= dp_up + 1");
    // dp[i][j] <= dp[i][j-1] + 1 (triangle: match inherits diag, diag <= left+1)
    ctx.push_assert("triangle_left", "dp_ij <= dp_left + 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 54b: edit distance match step should verify, got: {:?}",
        result,
    );
}

/// Tier 54b: Step — mismatch case: dp[i][j] = 1 + min(dp[i-1][j], dp[i][j-1], dp[i-1][j-1]).
/// Encoded with if-else min to avoid disjunctive reasoning (BV-friendly).
/// Proves non-negativity and per-operation bounds.
#[test]
fn test_vt_tier54b_edit_distance_step_mismatch() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("dp_diag", "i64");
    ctx.declare_var_parsed("dp_up", "i64");
    ctx.declare_var_parsed("dp_left", "i64");
    ctx.declare_var_parsed("dp_ij", "i64");

    ctx.push_assume("ih_diag_nonneg", "dp_diag >= 0");
    ctx.push_assume("ih_up_nonneg", "dp_up >= 0");
    ctx.push_assume("ih_left_nonneg", "dp_left >= 0");
    ctx.push_assume("ih_diag_bounded", "dp_diag < 1000000");
    ctx.push_assume("ih_up_bounded", "dp_up < 1000000");
    ctx.push_assume("ih_left_bounded", "dp_left < 1000000");
    // Mismatch recurrence using nested if-else for BV-friendly min encoding:
    // min3 = min(dp_diag, dp_up, dp_left) via nested conditionals
    ctx.push_assume(
        "mismatch_recurrence",
        "dp_ij == 1 + if dp_diag <= dp_up && dp_diag <= dp_left { dp_diag } else { if dp_up <= dp_left { dp_up } else { dp_left } }",
    );

    // dp[i][j] >= 1 (at least one operation for mismatch)
    ctx.push_assert("ge_one", "dp_ij >= 1");
    // dp[i][j] <= dp[i-1][j-1] + 1 (replace bound)
    ctx.push_assert("replace_bound", "dp_ij <= dp_diag + 1");
    // dp[i][j] <= dp[i-1][j] + 1 (delete bound)
    ctx.push_assert("delete_bound", "dp_ij <= dp_up + 1");
    // dp[i][j] <= dp[i][j-1] + 1 (insert bound)
    ctx.push_assert("insert_bound", "dp_ij <= dp_left + 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 54b: edit distance mismatch step should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Concrete traces
// ========================================================================

/// Tier 54c: Concrete — edit_distance("kitten", "sitting") = 3.
/// Using 3-char prefixes: a = "kit", b = "sit" (m=3, n=3).
/// dp table (4x4, flat row-major):
///     ""  s  i  t
///  ""  0  1  2  3
///  k   1  1  2  3
///  i   2  2  1  2
///  t   3  3  2  1
/// edit_distance("kit", "sit") = dp[3][3] = 1 (replace k->s).
#[test]
fn test_vt_tier54c_edit_distance_kit_sit_concrete() {
    let mut ctx = VerificationContext::new();
    // Flat row-major: dp[i][j] = dp_flat[i*4 + j], (m+1)*(n+1) = 16
    #[rustfmt::skip]
    let dp_values: &[i64] = &[
        0, 1, 2, 3,  // row 0: "" -> {_, s, si, sit}
        1, 1, 2, 3,  // row 1: k  -> {k, ks, ki, kit}... wait
        2, 2, 1, 2,  // row 2: ki
        3, 3, 2, 1,  // row 3: kit
    ];
    assume_seq_i64(&mut ctx, "dp", dp_values);

    // a = "kit", b = "sit"
    // a[0]='k', a[1]='i', a[2]='t'
    // b[0]='s', b[1]='i', b[2]='t'
    // Encode char equality: a[i]==b[j] as boolean assumptions
    ctx.declare_var_parsed("match_00", "bool"); // a[0]==b[0]? k==s? no
    ctx.declare_var_parsed("match_01", "bool"); // a[0]==b[1]? k==i? no
    ctx.declare_var_parsed("match_02", "bool"); // a[0]==b[2]? k==t? no
    ctx.declare_var_parsed("match_10", "bool"); // a[1]==b[0]? i==s? no
    ctx.declare_var_parsed("match_11", "bool"); // a[1]==b[1]? i==i? yes
    ctx.declare_var_parsed("match_12", "bool"); // a[1]==b[2]? i==t? no
    ctx.declare_var_parsed("match_20", "bool"); // a[2]==b[0]? t==s? no
    ctx.declare_var_parsed("match_21", "bool"); // a[2]==b[1]? t==i? no
    ctx.declare_var_parsed("match_22", "bool"); // a[2]==b[2]? t==t? yes

    ctx.push_assume("m00", "match_00 == false");
    ctx.push_assume("m01", "match_01 == false");
    ctx.push_assume("m02", "match_02 == false");
    ctx.push_assume("m10", "match_10 == false");
    ctx.push_assume("m11", "match_11 == true");
    ctx.push_assume("m12", "match_12 == false");
    ctx.push_assume("m20", "match_20 == false");
    ctx.push_assume("m21", "match_21 == false");
    ctx.push_assume("m22", "match_22 == true");

    // First row: dp[0][j] = j
    ctx.push_assert(
        "row0",
        "dp.index(0) == 0 && dp.index(1) == 1 && dp.index(2) == 2 && dp.index(3) == 3",
    );
    // First column: dp[i][0] = i
    ctx.push_assert(
        "col0",
        "dp.index(0) == 0 && dp.index(4) == 1 && dp.index(8) == 2 && dp.index(12) == 3",
    );

    // dp[1][1]: a[0]!=b[0], dp[1][1] = 1 + min(dp[0][1], dp[1][0], dp[0][0]) = 1 + min(1,1,0) = 1
    ctx.push_assert("dp11", "dp.index(5) == 1");
    // dp[2][2]: a[1]==b[1], dp[2][2] = dp[1][1] = 1
    ctx.push_assert("dp22_match", "dp.index(10) == dp.index(5)");
    // dp[3][3]: a[2]==b[2], dp[3][3] = dp[2][2] = 1
    ctx.push_assert("dp33_match", "dp.index(15) == dp.index(10)");
    // Final answer
    ctx.push_assert("answer", "dp.index(15) == 1");
    // Bound: edit distance <= max(m, n)
    ctx.push_assert("upper_bound", "dp.index(15) <= 3");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 54c: edit distance kit->sit concrete should verify, got: {:?}",
        result,
    );
}

/// Tier 54c: Concrete — edit_distance("abc", "aec") = 1.
/// dp table (4x4):
///     ""  a  e  c
///  ""  0  1  2  3
///  a   1  0  1  2
///  b   2  1  1  2
///  c   3  2  2  1
#[test]
fn test_vt_tier54c_edit_distance_abc_aec_concrete() {
    let mut ctx = VerificationContext::new();
    #[rustfmt::skip]
    let dp_values: &[i64] = &[
        0, 1, 2, 3,
        1, 0, 1, 2,
        2, 1, 1, 2,
        3, 2, 2, 1,
    ];
    assume_seq_i64(&mut ctx, "dp", dp_values);

    // Verify recurrence at key cells:
    // dp[1][1]: a[0]==b[0] ('a'=='a'), dp[1][1] = dp[0][0] = 0
    ctx.push_assert("dp11_match", "dp.index(5) == dp.index(0)");
    // dp[2][2]: a[1]!=b[1] ('b'!='e'), dp[2][2] = 1 + min(dp[1][2], dp[2][1], dp[1][1]) = 1+min(1,1,0) = 1
    ctx.push_assert("dp22_mismatch", "dp.index(10) == 1");
    // dp[3][3]: a[2]==b[2] ('c'=='c'), dp[3][3] = dp[2][2] = 1
    ctx.push_assert("dp33_match", "dp.index(15) == dp.index(10)");
    // Final answer
    ctx.push_assert("answer", "dp.index(15) == 1");
    // Triangle inequality: |edit(a,b)| <= |a| + |b| (trivially)
    ctx.push_assert("trivial_bound", "dp.index(15) <= 6");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 54c: edit distance abc->aec concrete should verify, got: {:?}",
        result,
    );
}

/// Tier 54c: Concrete — identical strings: edit_distance("ab", "ab") = 0.
/// dp table (3x3):
///     ""  a  b
///  ""  0  1  2
///  a   1  0  1
///  b   2  1  0
#[test]
fn test_vt_tier54c_edit_distance_identical_strings() {
    let mut ctx = VerificationContext::new();
    #[rustfmt::skip]
    let dp_values: &[i64] = &[
        0, 1, 2,
        1, 0, 1,
        2, 1, 0,
    ];
    assume_seq_i64(&mut ctx, "dp", dp_values);

    // All diagonal matches: dp[i][i] = 0 for i in 0..=2
    ctx.push_assert("diag_00", "dp.index(0) == 0");
    ctx.push_assert("diag_11", "dp.index(4) == 0");
    ctx.push_assert("diag_22", "dp.index(8) == 0");
    // dp[i][j] >= |i - j| (lower bound on edit distance)
    // dp[1][0] >= 1, dp[0][1] >= 1, dp[2][0] >= 2, dp[0][2] >= 2
    ctx.push_assert("lb_10", "dp.index(3) >= 1");
    ctx.push_assert("lb_01", "dp.index(1) >= 1");
    ctx.push_assert("lb_20", "dp.index(6) >= 2");
    ctx.push_assert("lb_02", "dp.index(2) >= 2");
    // Final answer: 0 edits
    ctx.push_assert("answer_zero", "dp.index(8) == 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 54c: identical string edit distance should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Symbolic step properties
// ========================================================================

/// Tier 54d: Symbolic — edit distance is symmetric: ed(a,b) == ed(b,a).
/// For any row i,j: dp_ab[i][j] == dp_ba[j][i].
/// We verify this for a single cell under matching predecessor symmetry.
#[test]
fn test_vt_tier54d_edit_distance_symmetry_step() {
    let mut ctx = VerificationContext::new();
    // dp_ab is the table for (a,b), dp_ba is the table for (b,a)
    // At cell (i,j) in dp_ab vs (j,i) in dp_ba
    ctx.declare_var_parsed("dp_ab_diag", "i64"); // dp_ab[i-1][j-1]
    ctx.declare_var_parsed("dp_ab_up", "i64"); // dp_ab[i-1][j]
    ctx.declare_var_parsed("dp_ab_left", "i64"); // dp_ab[i][j-1]
    ctx.declare_var_parsed("dp_ab_ij", "i64"); // dp_ab[i][j]
    ctx.declare_var_parsed("dp_ba_diag", "i64"); // dp_ba[j-1][i-1] = dp_ab[i-1][j-1]
    ctx.declare_var_parsed("dp_ba_up", "i64"); // dp_ba[j-1][i] = dp_ab[i][j-1]
    ctx.declare_var_parsed("dp_ba_left", "i64"); // dp_ba[j][i-1] = dp_ab[i-1][j]
    ctx.declare_var_parsed("dp_ba_ji", "i64"); // dp_ba[j][i]

    // Symmetry IH: predecessors are symmetric
    ctx.push_assume("sym_diag", "dp_ab_diag == dp_ba_diag");
    ctx.push_assume("sym_cross1", "dp_ab_up == dp_ba_left"); // dp_ab[i-1][j] == dp_ba[j][i-1]
    ctx.push_assume("sym_cross2", "dp_ab_left == dp_ba_up"); // dp_ab[i][j-1] == dp_ba[j-1][i]

    // Non-negativity and bounds
    ctx.push_assume(
        "nonneg_all",
        "dp_ab_diag >= 0 && dp_ab_up >= 0 && dp_ab_left >= 0",
    );
    ctx.push_assume(
        "bounded_all",
        "dp_ab_diag < 1000000 && dp_ab_up < 1000000 && dp_ab_left < 1000000",
    );

    // Both compute min of same three values (just in different order)
    ctx.declare_var_parsed("min_val", "i64");
    ctx.push_assume("min_le_d", "min_val <= dp_ab_diag");
    ctx.push_assume("min_le_u", "min_val <= dp_ab_up");
    ctx.push_assume("min_le_l", "min_val <= dp_ab_left");
    ctx.push_assume(
        "min_is_one",
        "min_val == dp_ab_diag || min_val == dp_ab_up || min_val == dp_ab_left",
    );
    // Mismatch case: both tables use 1 + min(diag, up, left)
    ctx.push_assume("rec_ab", "dp_ab_ij == 1 + min_val");

    // dp_ba's min over (dp_ba_diag, dp_ba_up, dp_ba_left) =
    //   min(dp_ab_diag, dp_ab_left, dp_ab_up) = same min_val
    ctx.push_assume("rec_ba", "dp_ba_ji == 1 + min_val");

    // Symmetry: dp_ab[i][j] == dp_ba[j][i]
    ctx.push_assert("symmetric", "dp_ab_ij == dp_ba_ji");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 54d: edit distance symmetry should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP E: Soundness negatives
// ========================================================================

/// Tier 54e NEGATIVE: Wrong recurrence — using max instead of min.
/// dp[i][j] = 1 + max(del, ins, rep) gives the WORST alignment.
/// Claiming dp[i][j] <= dp[i-1][j-1] + 1 should fail.
#[test]
fn test_vt_tier54e_wrong_recurrence_max_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("dp_diag", "i64");
    ctx.declare_var_parsed("dp_up", "i64");
    ctx.declare_var_parsed("dp_left", "i64");
    ctx.declare_var_parsed("dp_ij", "i64");

    ctx.push_assume("ih_diag_nonneg", "dp_diag >= 0");
    ctx.push_assume("ih_up_nonneg", "dp_up >= 0");
    ctx.push_assume("ih_left_nonneg", "dp_left >= 0");
    // WRONG: using max instead of min
    ctx.declare_var_parsed("max_val", "i64");
    ctx.push_assume("max_ge_diag", "max_val >= dp_diag");
    ctx.push_assume("max_ge_up", "max_val >= dp_up");
    ctx.push_assume("max_ge_left", "max_val >= dp_left");
    ctx.push_assume(
        "max_is_one",
        "max_val == dp_diag || max_val == dp_up || max_val == dp_left",
    );
    ctx.push_assume("wrong_recurrence", "dp_ij == 1 + max_val");

    // This bound holds for min but NOT for max
    ctx.push_assert("wrong_replace_bound", "dp_ij <= dp_diag + 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 54e SOUNDNESS: max-recurrence should reject replace bound, got: {:?}",
        result,
    );
}

/// Tier 54e NEGATIVE: Claiming edit_distance("abc", "xyz") == 1
/// should fail (actual distance is 3: replace all three chars).
#[test]
fn test_vt_tier54e_wrong_distance_claim_rejected() {
    let mut ctx = VerificationContext::new();
    // dp for "abc" -> "xyz": dp[3][3] should be 3, not 1
    // Full table:
    //     ""  x  y  z
    //  ""  0  1  2  3
    //  a   1  1  2  3
    //  b   2  2  2  3
    //  c   3  3  3  3
    #[rustfmt::skip]
    let dp_values: &[i64] = &[
        0, 1, 2, 3,
        1, 1, 2, 3,
        2, 2, 2, 3,
        3, 3, 3, 3,
    ];
    assume_seq_i64(&mut ctx, "dp", dp_values);

    // Claiming the answer is 1 should fail (it's actually 3)
    ctx.push_assert("wrong_answer", "dp.index(15) == 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 54e SOUNDNESS: wrong distance claim should be rejected, got: {:?}",
        result,
    );
}

/// Tier 54e NEGATIVE: Claiming edit distance of completely different strings
/// of unequal length is less than the length difference.
/// edit_distance("a", "xyz") >= 2 (need at least 2 inserts). Claiming < 2 fails.
#[test]
fn test_vt_tier54e_length_lower_bound_negative() {
    let mut ctx = VerificationContext::new();
    // dp for "a" (m=1) -> "xyz" (n=3): dp is 2x4 = 8 entries
    //     ""  x  y  z
    //  ""  0  1  2  3
    //  a   1  1  2  3
    #[rustfmt::skip]
    let dp_values: &[i64] = &[
        0, 1, 2, 3,
        1, 1, 2, 3,
    ];
    assume_seq_i64(&mut ctx, "dp", dp_values);

    // Claiming dp[1][3] < 2 should fail (actual is 3)
    ctx.push_assert("wrong_lower_bound", "dp.index(7) < 2");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 54e SOUNDNESS: length lower bound violation should be rejected, got: {:?}",
        result,
    );
}
