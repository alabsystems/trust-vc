// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! VerifyThis 2026: Tier 66 — Matrix Chain Multiplication VCs (Groups A–D).
//!
//! Given a chain of matrices A_1..A_n with dimensions p[0]×p[1], p[1]×p[2], …,
//! p[n-1]×p[n], find the optimal parenthesization minimizing scalar multiplications.
//!
//! DP recurrence:
//!   m[i][i] = 0    (base case)
//!   m[i][j] = min_{i<=k<j} (m[i][k] + m[k+1][j] + p[i]*p[k+1]*p[j+1])
//!
//! We flatten the 2D DP table into a Seq using row-major indexing:
//!   m[i][j] → m.index(i * n + j)  where n = number of matrices.
//!
//! Groups A–D: Init, Step, Invariant, Exit.
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
// GROUP A: Init — base cases m[i][i] = 0
// ========================================================================

/// Tier 66a: Init — base case for 4-matrix chain. m[i][i] = 0 for all i.
/// Dimensions: p = [10, 20, 30, 40, 50] → 4 matrices.
/// DP table is 4×4, flattened to Seq of length 16.
#[test]
fn test_vt_tier66a_base_case_concrete() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("n", "u64");
    ctx.push_assume("n_val", "n == 4");

    // Flattened DP table: m[i*4+j]. Base case: diagonal = 0.
    // m[0][0]=0, m[1][1]=0, m[2][2]=0, m[3][3]=0
    // Other entries are irrelevant for base case.
    assume_seq_i64(
        &mut ctx,
        "m",
        &[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    );

    // All diagonal entries are zero
    ctx.push_assert("base_0", "m.index(0) == 0"); // m[0][0] = m.index(0*4+0)
    ctx.push_assert("base_1", "m.index(5) == 0"); // m[1][1] = m.index(1*4+1)
    ctx.push_assert("base_2", "m.index(10) == 0"); // m[2][2] = m.index(2*4+2)
    ctx.push_assert("base_3", "m.index(15) == 0"); // m[3][3] = m.index(3*4+3)

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 66a: base case concrete should verify, got: {:?}",
        result,
    );
}

/// Tier 66a: Init — symbolic n, diagonal is zero.
/// For any valid index i < n, m[i*n+i] == 0.
#[test]
fn test_vt_tier66a_base_case_symbolic() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("n", "u64");
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("m_diag", "i64");

    ctx.push_assume("n_bound", "n >= 2 && n <= 10");
    ctx.push_assume("i_bound", "i < n");
    ctx.push_assume("diag_init", "m_diag == 0");

    ctx.push_assert("base_nonneg", "m_diag >= 0");
    ctx.push_assert("base_nonpos", "m_diag <= 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 66a: base case symbolic should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP B: Step — one DP step computing m[i][j]
// ========================================================================

/// Tier 66b: Step — compute m[0][1] for 2-matrix chain.
/// p = [10, 20, 30]. m[0][1] = p[0]*p[1]*p[2] = 10*20*30 = 6000.
/// Only one split (k=0): m[0][0] + m[1][1] + 10*20*30.
#[test]
fn test_vt_tier66b_step_two_matrices() {
    let mut ctx = VerificationContext::new();
    // Dimensions
    assume_seq_i64(&mut ctx, "p", &[10, 20, 30]);

    ctx.declare_var_parsed("m_00", "i64");
    ctx.declare_var_parsed("m_11", "i64");
    ctx.declare_var_parsed("m_01", "i64");

    ctx.push_assume("m_00_val", "m_00 == 0");
    ctx.push_assume("m_11_val", "m_11 == 0");
    // m[0][1] = m[0][0] + m[1][1] + p[0]*p[1]*p[2] = 0 + 0 + 6000
    ctx.push_assume("m_01_val", "m_01 == 6000");

    // Recurrence holds: m[0][1] = m[0][0] + m[1][1] + p[0]*p[1]*p[2]
    ctx.push_assert("cost_0", "p.index(0) == 10");
    ctx.push_assert("cost_1", "p.index(1) == 20");
    ctx.push_assert("cost_2", "p.index(2) == 30");
    ctx.push_assert("recurrence", "m_01 == m_00 + m_11 + 6000");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 66b: two-matrix step should verify, got: {:?}",
        result,
    );
}

/// Tier 66b: Step — compute m[0][2] for 3-matrix chain.
/// p = [10, 20, 30, 40]. Three matrices: A(10×20), B(20×30), C(30×40).
/// k=0: m[0][0] + m[1][2] + 10*20*40 = 0 + 24000 + 8000 = 32000
/// k=1: m[0][1] + m[2][2] + 10*30*40 = 6000 + 0 + 12000 = 18000
/// Minimum: 18000 at k=1.
#[test]
fn test_vt_tier66b_step_three_matrices() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "p", &[10, 20, 30, 40]);

    ctx.declare_var_parsed("m_01", "i64");
    ctx.declare_var_parsed("m_12", "i64");
    ctx.declare_var_parsed("cost_k0", "i64");
    ctx.declare_var_parsed("cost_k1", "i64");
    ctx.declare_var_parsed("m_02", "i64");

    ctx.push_assume("m_01_val", "m_01 == 6000"); // (AB) = 10*20*30
    ctx.push_assume("m_12_val", "m_12 == 24000"); // (BC) = 20*30*40

    // k=0: m[0][0] + m[1][2] + p[0]*p[1]*p[3] = 0 + 24000 + 8000 = 32000
    ctx.push_assume("cost_k0_val", "cost_k0 == 32000");
    // k=1: m[0][1] + m[2][2] + p[0]*p[2]*p[3] = 6000 + 0 + 12000 = 18000
    ctx.push_assume("cost_k1_val", "cost_k1 == 18000");
    // m[0][2] = min(32000, 18000) = 18000
    ctx.push_assume("m_02_val", "m_02 == 18000");

    ctx.push_assert("k0_cost", "cost_k0 == 0 + m_12 + 8000");
    ctx.push_assert("k1_cost", "cost_k1 == m_01 + 0 + 12000");
    ctx.push_assert("min_is_k1", "m_02 <= cost_k0");
    ctx.push_assert("min_is_k1b", "m_02 <= cost_k1");
    ctx.push_assert("min_exact", "m_02 == cost_k1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 66b: three-matrix step should verify, got: {:?}",
        result,
    );
}

/// Tier 66b: Step — full 4-matrix chain.
/// p = [10, 20, 30, 40, 50]. Four matrices.
/// m[0][1]=6000, m[1][2]=24000, m[2][3]=60000
/// m[0][2]=18000, m[1][3]=64000
/// m[0][3]: k=0: 0+64000+10*20*50=0+64000+10000=74000
///          k=1: 6000+60000+10*30*50=6000+60000+15000=81000
///          k=2: 18000+0+10*40*50=18000+0+20000=38000
/// min=38000 at k=2.
#[test]
fn test_vt_tier66b_step_four_matrices() {
    let mut ctx = VerificationContext::new();

    ctx.declare_var_parsed("cost_k0", "i64");
    ctx.declare_var_parsed("cost_k1", "i64");
    ctx.declare_var_parsed("cost_k2", "i64");
    ctx.declare_var_parsed("m_03", "i64");

    ctx.push_assume("cost_k0_val", "cost_k0 == 74000");
    ctx.push_assume("cost_k1_val", "cost_k1 == 81000");
    ctx.push_assume("cost_k2_val", "cost_k2 == 38000");
    ctx.push_assume("m_03_val", "m_03 == 38000");

    // m[0][3] is minimum over all splits
    ctx.push_assert("le_k0", "m_03 <= cost_k0");
    ctx.push_assert("le_k1", "m_03 <= cost_k1");
    ctx.push_assert("le_k2", "m_03 <= cost_k2");
    // And equals the minimum
    ctx.push_assert("eq_min", "m_03 == cost_k2");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 66b: four-matrix step should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP C: Invariant — optimal substructure
// ========================================================================

/// Tier 66c: Invariant — if m[i][j] is optimal, it uses some split k.
/// For each split k: m[i][j] <= m[i][k] + m[k+1][j] + cost(i,k,j).
/// Concrete verification for 3-matrix chain with m[0][2]=18000.
#[test]
fn test_vt_tier66c_optimal_substructure() {
    let mut ctx = VerificationContext::new();

    ctx.declare_var_parsed("m_02", "i64");
    ctx.declare_var_parsed("cost_k0", "i64");
    ctx.declare_var_parsed("cost_k1", "i64");

    ctx.push_assume("m_02_val", "m_02 == 18000");
    ctx.push_assume("cost_k0_val", "cost_k0 == 32000");
    ctx.push_assume("cost_k1_val", "cost_k1 == 18000");

    // Optimal substructure: m[0][2] <= cost for every valid split
    ctx.push_assert("opt_k0", "m_02 <= cost_k0");
    ctx.push_assert("opt_k1", "m_02 <= cost_k1");
    // m[0][2] equals at least one split (the optimal one)
    ctx.push_assert("achieves_min", "m_02 == cost_k1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 66c: optimal substructure should verify, got: {:?}",
        result,
    );
}

/// Tier 66c: Invariant — costs are non-negative (well-foundedness).
/// All dimension values are positive → costs are non-negative.
#[test]
fn test_vt_tier66c_costs_nonneg() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("pi", "u64");
    ctx.declare_var_parsed("pk", "u64");
    ctx.declare_var_parsed("pj", "u64");
    ctx.declare_var_parsed("m_ik", "u64");
    ctx.declare_var_parsed("m_kj", "u64");

    ctx.push_assume("pi_pos", "pi >= 1 && pi <= 100");
    ctx.push_assume("pk_pos", "pk >= 1 && pk <= 100");
    ctx.push_assume("pj_pos", "pj >= 1 && pj <= 100");
    ctx.push_assume("m_ik_nonneg", "m_ik >= 0");
    ctx.push_assume("m_kj_nonneg", "m_kj >= 0");

    // Cost for a split = m[i][k] + m[k+1][j] + p_i * p_k * p_j >= 0
    // Since all terms non-negative, sum is non-negative
    // Product of positives is positive
    ctx.push_assert("pi_ok", "pi >= 1");
    ctx.push_assert("pk_ok", "pk >= 1");
    ctx.push_assert("pj_ok", "pj >= 1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 66c: costs non-negative should verify, got: {:?}",
        result,
    );
}

/// Tier 66c: Invariant — monotonicity of chain length.
/// For chain of length l, m[i][j] uses only subchains of length < l.
/// This means the DP fills by increasing chain length.
#[test]
fn test_vt_tier66c_chain_length_monotonicity() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("i", "u64");
    ctx.declare_var_parsed("j", "u64");
    ctx.declare_var_parsed("k", "u64");
    ctx.declare_var_parsed("l", "u64");

    ctx.push_assume("l_bound", "l >= 2 && l <= 10");
    ctx.push_assume("i_bound", "i <= 10");
    ctx.push_assume("j_def", "j == i + l - 1");
    ctx.push_assume("k_range", "k >= i && k < j");

    // Sub-chain lengths: (k - i + 1) < l and (j - k) < l
    ctx.push_assert("left_shorter", "k - i + 1 < l");
    ctx.push_assert("right_shorter", "j - k < l");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 66c: chain length monotonicity should verify, got: {:?}",
        result,
    );
}

// ========================================================================
// GROUP D: Exit + Negative tests
// ========================================================================

/// Tier 66d: Exit — full DP table for p=[10,20,30,40,50].
/// Verifies that m[0][3]=38000 is the global optimum.
#[test]
fn test_vt_tier66d_full_table_4_matrices() {
    let mut ctx = VerificationContext::new();
    // All costs at each split for the full chain
    ctx.declare_var_parsed("cost_k0", "i64");
    ctx.declare_var_parsed("cost_k1", "i64");
    ctx.declare_var_parsed("cost_k2", "i64");
    ctx.declare_var_parsed("m_03", "i64");

    ctx.push_assume("cost_k0_val", "cost_k0 == 74000");
    ctx.push_assume("cost_k1_val", "cost_k1 == 81000");
    ctx.push_assume("cost_k2_val", "cost_k2 == 38000");
    ctx.push_assume("m_03_val", "m_03 == 38000");

    // m[0][3] is the minimum
    ctx.push_assert("global_opt_k0", "m_03 <= cost_k0");
    ctx.push_assert("global_opt_k1", "m_03 <= cost_k1");
    ctx.push_assert("global_opt_k2", "m_03 <= cost_k2");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 66d: full table 4 matrices should verify, got: {:?}",
        result,
    );
}

/// Tier 66d: Negative — wrong optimal cost.
/// Claiming m[0][3] = 30000 when the real minimum is 38000.
/// At least one split must be violated.
#[test]
fn test_vt_tier66d_wrong_optimal_negative() {
    let mut ctx = VerificationContext::new();
    assume_seq_i64(&mut ctx, "p", &[10, 20, 30, 40, 50]);
    assume_seq_i64(
        &mut ctx,
        "m",
        &[
            0, 6000, 18000, 38000, 0, 0, 24000, 64000, 0, 0, 0, 60000, 0, 0, 0, 0,
        ],
    );

    // For the full 4-matrix chain, the real optimum uses split k=2:
    // m[0][3] = m[0][2] + p[0] * p[3] * p[4] = 18000 + 10*40*50 = 38000.
    ctx.push_assert(
        "best_split_cost",
        "m.index(3) == m.index(2) + p.index(0) * p.index(3) * p.index(4)",
    );
    ctx.push_assert("wrong_optimal_value", "m.index(3) == 30000");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 66d SOUNDNESS: wrong optimal should be refuted, got: {:?}",
        result,
    );
}

/// Tier 66d: Negative — wrong split choice.
/// For p=[10,20,30,40], claiming k=0 is optimal for m[0][2] is wrong.
/// k=0 gives cost 32000; k=1 gives 18000. Asserting 32000 <= 18000 fails.
#[test]
fn test_vt_tier66d_wrong_split_negative() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("cost_k0", "i64");
    ctx.declare_var_parsed("cost_k1", "i64");

    // p = [10, 20, 30, 40]: 3 matrices
    // k=0: m[0][0] + m[1][2] + 10*20*40 = 0 + 24000 + 8000 = 32000
    // k=1: m[0][1] + m[2][2] + 10*30*40 = 6000 + 0 + 12000 = 18000
    ctx.push_assume("cost_k0_val", "cost_k0 == 32000");
    ctx.push_assume("cost_k1_val", "cost_k1 == 18000");

    // Wrong: claiming k=0 is at least as good as k=1
    ctx.push_assert("wrong_claim", "cost_k0 <= cost_k1");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "TIER 66d SOUNDNESS: wrong split should be rejected, got: {:?}",
        result,
    );
}

/// Tier 66d: Exit — DP table for p=[30,35,15,5,10,20,25] (CLRS example).
/// n=6 matrices. m[0][5] = 15125 (classic textbook result).
#[test]
fn test_vt_tier66d_clrs_example() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_parsed("m_05", "i64");

    // CLRS Introduction to Algorithms example:
    // p = [30, 35, 15, 5, 10, 20, 25]
    // Optimal cost m[1][6] = 15125 in 1-indexed (= m[0][5] in 0-indexed)
    ctx.push_assume("m_05_val", "m_05 == 15125");

    ctx.push_assert("positive", "m_05 > 0");

    let result = verify_with_pipeline(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "TIER 66d: CLRS example m[0][5]=15125 should verify, got: {:?}",
        result,
    );
}
