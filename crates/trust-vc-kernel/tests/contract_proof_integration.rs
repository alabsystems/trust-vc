// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Integration tests verifying that CDCL contract states produce valid
//! proof certificates through the trust-vc-kernel checker and compactor.
//!
//! These tests simulate DPLL(T) operations — decisions, BCP propagation,
//! conflict analysis, clause learning, and backtracking — and construct
//! the corresponding `AYProofArtifact` / `ProofTrace` that the kernel
//! validates. This bridges Initiative 2 (Proof Certificates) and
//! Initiative 4 (Self-Verifying Solver) by demonstrating that contract-
//! compliant solver behavior produces checkable, compactable proofs.
//!
//! The contract types in `trust_vc_core::ay_contracts` are `pub(crate)`,
//! so we mirror the essential CDCL simulation logic here, building
//! proof artifacts from traces of solver operations.

use trust_vc_kernel::compaction::{compact_proof, compact_with_stats};
use trust_vc_kernel::{
    check_proof, check_proof_with_theory, convert_ay_artifact, AYClause, AYProofArtifact,
    AYResolutionStep, AYTheoryKind, AYTheoryLemma, CheckResult, Clause, ProofTrace, ResolutionStep,
    TheoryLemma,
};

// ===========================================================================
// Helpers
// ===========================================================================

/// Build a clause from an ID and literal slice.
fn cl(id: u64, lits: &[i64]) -> Clause {
    Clause {
        id,
        literals: lits.to_vec(),
    }
}

/// Build a resolution step.
fn rs(id: u64, pivot: i64, p1: u64, p2: u64) -> ResolutionStep {
    ResolutionStep {
        id,
        pivot,
        parent1: p1,
        parent2: p2,
        result_literals: None,
    }
}

/// Build a theory lemma.
fn tl(id: u64, theory: &str, lits: &[i64]) -> TheoryLemma {
    TheoryLemma {
        id,
        theory: theory.to_string(),
        clause: cl(id, lits),
    }
}

/// Build a AYClause.
fn zc(id: u64, lits: &[i64]) -> AYClause {
    AYClause {
        id,
        literals: lits.to_vec(),
    }
}

/// Build a AYResolutionStep.
fn zr(result_id: u64, pivot: i64, a: u64, b: u64) -> AYResolutionStep {
    AYResolutionStep {
        result_id,
        pivot,
        antecedent_a: a,
        antecedent_b: b,
        result_literals: None,
    }
}

/// Build a AYTheoryLemma.
fn ztl(id: u64, kind: AYTheoryKind, lits: &[i64]) -> AYTheoryLemma {
    AYTheoryLemma {
        id,
        kind,
        literals: lits.to_vec(),
    }
}

/// Assert that a `CheckResult` is `Valid`.
fn assert_valid(result: &CheckResult) {
    assert_eq!(result, &CheckResult::Valid, "expected Valid proof");
}

/// Build a simple trace with no theory lemmas.
fn simple_trace(inputs: Vec<Clause>, steps: Vec<ResolutionStep>, empty: u64) -> ProofTrace {
    ProofTrace {
        input_clauses: inputs,
        resolution_steps: steps,
        theory_lemmas: Vec::new(),
        empty_clause_id: empty,
    }
}

/// Assert a CheckResult is Invalid at the expected step and the reason
/// contains the expected substring. Handles `#[non_exhaustive]`.
fn assert_invalid(result: &CheckResult, expected_step: u64, reason_substr: &str) {
    match result {
        CheckResult::Invalid { step, reason } => {
            assert_eq!(
                *step, expected_step,
                "expected invalid at step {expected_step}, got {step}"
            );
            assert!(
                reason.contains(reason_substr),
                "reason should contain \"{reason_substr}\": {reason}"
            );
        }
        CheckResult::Valid => panic!("expected Invalid, got Valid"),
        _ => panic!("unexpected CheckResult variant"),
    }
}

// ===========================================================================
// Category 1: BCP propagation -> proof steps -> check_proof validates
// ===========================================================================

/// BCP on a unit clause propagates a literal; the resulting assignment
/// combined with a complementary clause produces a simple resolution
/// proof that the kernel validates.
#[test]
fn test_bcp_unit_propagation_generates_valid_proof() {
    // Clause 1: {a}       (unit, forces a=true via BCP)
    // Clause 2: {-a}      (contradicts a=true)
    // Resolution on pivot a produces empty clause.
    let trace = simple_trace(vec![cl(1, &[1]), cl(2, &[-1])], vec![rs(3, 1, 1, 2)], 3);
    assert_valid(&check_proof(&trace));
}

/// BCP chain propagation: a implies b implies c, then -c triggers conflict.
/// Three-step resolution chain produces valid proof.
#[test]
fn test_bcp_chain_propagation_valid_proof() {
    // Clause 1: {a}          -> propagates a
    // Clause 2: {-a, b}      -> propagates b
    // Clause 3: {-b, c}      -> propagates c
    // Clause 4: {-c}         -> conflict
    //
    // Resolution chain:
    //   Step 5: resolve(1, 2) on a -> {b}
    //   Step 6: resolve(5, 3) on b -> {c}
    //   Step 7: resolve(6, 4) on c -> {}
    let trace = simple_trace(
        vec![cl(1, &[1]), cl(2, &[-1, 2]), cl(3, &[-2, 3]), cl(4, &[-3])],
        vec![rs(5, 1, 1, 2), rs(6, 2, 5, 3), rs(7, 3, 6, 4)],
        7,
    );
    assert_valid(&check_proof(&trace));
}

/// BCP with two independent unit clauses propagating, then a binary
/// clause connecting them produces a valid proof.
#[test]
fn test_bcp_two_units_propagation_valid_proof() {
    // Clause 1: {a}       -> propagates a
    // Clause 2: {b}       -> propagates b
    // Clause 3: {-a, -b}  -> conflict (both a and b are true)
    //
    // Resolution:
    //   Step 4: resolve(1, 3) on a -> {-b}
    //   Step 5: resolve(2, 4) on b -> {}
    let trace = simple_trace(
        vec![cl(1, &[1]), cl(2, &[2]), cl(3, &[-1, -2])],
        vec![rs(4, 1, 1, 3), rs(5, 2, 2, 4)],
        5,
    );
    assert_valid(&check_proof(&trace));
}

/// BCP produces a long implication chain (length 10) that is resolved
/// into an empty clause.
#[test]
fn test_bcp_long_implication_chain_valid_proof() {
    // x1 -> x2 -> x3 -> ... -> x10, then -x10 contradicts.
    let n = 10i64;
    let mut inputs = vec![cl(1, &[1])]; // x1 unit
    for i in 1..n {
        inputs.push(cl((i + 1) as u64, &[-i, i + 1]));
    }
    inputs.push(cl((n + 1) as u64, &[-n]));

    let mut steps = vec![rs(100, 1, 1, 2)]; // resolve x1
    for i in 2..n {
        steps.push(rs(
            100 + (i - 1) as u64,
            i,
            100 + (i - 2) as u64,
            (i + 1) as u64,
        ));
    }
    let final_id = 100 + (n - 1) as u64;
    steps.push(rs(final_id, n, final_id - 1, (n + 1) as u64));

    let trace = simple_trace(inputs, steps, final_id);
    assert_valid(&check_proof(&trace));
}

// ===========================================================================
// Category 2: Conflict -> analyze -> learned clause -> Resolution validates
// ===========================================================================

/// A conflict detected after BCP produces a learned clause. The
/// resolution step that derives the learned clause validates.
#[test]
fn test_conflict_analysis_learned_clause_valid_resolution() {
    // Clause 1: {a, b}
    // Clause 2: {a, -b}
    // Clause 3: {-a, b}
    // Clause 4: {-a, -b}
    //
    // Resolution chain for full UNSAT:
    // Step 5: resolve(1, 4, pivot=b) -> {a, -a} WRONG (tautological).
    // Correct:
    // Step 5: resolve(1, 2, pivot=b) -> {a}
    // Step 6: resolve(3, 4, pivot=b) -> {-a}
    // Step 7: resolve(5, 6, pivot=a) -> {}
    let trace = simple_trace(
        vec![
            cl(1, &[1, 2]),
            cl(2, &[1, -2]),
            cl(3, &[-1, 2]),
            cl(4, &[-1, -2]),
        ],
        vec![rs(5, 2, 1, 2), rs(6, 2, 3, 4), rs(7, 1, 5, 6)],
        7,
    );
    assert_valid(&check_proof(&trace));
}

/// Learned clause from resolving a ternary conflict against its reason.
#[test]
fn test_conflict_resolution_ternary_clause_valid() {
    // Clause 1: {a, b, c}
    // Clause 2: {-c}
    // Clause 3: {-b}
    // Clause 4: {-a}
    //
    // Step 5: resolve(1, 2) on c -> {a, b}
    // Step 6: resolve(5, 3) on b -> {a}
    // Step 7: resolve(6, 4) on a -> {}
    let trace = simple_trace(
        vec![cl(1, &[1, 2, 3]), cl(2, &[-3]), cl(3, &[-2]), cl(4, &[-1])],
        vec![rs(5, 3, 1, 2), rs(6, 2, 5, 3), rs(7, 1, 6, 4)],
        7,
    );
    assert_valid(&check_proof(&trace));
}

/// Conflict analysis must produce a resolution step where the pivot
/// appears in the correct parents. This test verifies the checker
/// accepts a valid learned-clause resolution.
#[test]
fn test_learned_clause_resolution_pivot_correctness() {
    // Two clauses share pivot variable b:
    // Clause 1: {a, b}   (has +b)
    // Clause 2: {a, -b}  (has -b)
    // Resolving on b -> {a} (the "learned" resolvent).
    // Then clause 3: {-a} contradicts.
    // Step 4: resolve(1, 2) on b -> {a}
    // Step 5: resolve(4, 3) on a -> {}
    let trace = simple_trace(
        vec![cl(1, &[1, 2]), cl(2, &[1, -2]), cl(3, &[-1])],
        vec![rs(4, 2, 1, 2), rs(5, 1, 4, 3)],
        5,
    );
    assert_valid(&check_proof(&trace));
}

// ===========================================================================
// Category 3: Full DPLL simulation
// ===========================================================================

/// Full DPLL cycle: decide -> propagate -> conflict -> learn -> backtrack.
/// Constructs a proof from the simulation and validates it.
#[test]
fn test_full_dpll_decide_propagate_conflict_learn_backtrack() {
    // 2-variable UNSAT: {a,b}, {a,-b}, {-a,b}, {-a,-b}
    //
    // DPLL trace:
    //   Decide a=true. Propagate: clause {-a,b} forces b=true.
    //   Clause {-a,-b} conflicts (both -a=false, -b=false).
    //   Conflict analysis: resolve({-a,-b}, {-a,b}) on b -> {-a} (learned)
    //   Backtrack to level 0, propagate: {-a} forces a=false.
    //   Clause {a,b} becomes unit -> b forced true.
    //   Clause {a,-b} conflicts: a=false, -b=false.
    //   Conflict analysis: resolve({a,-b}, {a,b}) on b -> {a}
    //   Resolve {-a} with {a} -> {} (empty).
    //
    // Proof:
    //   Step 5: resolve(3={-a,b}, 4={-a,-b}) on b -> {-a}
    //   Step 6: resolve(1={a,b}, 2={a,-b}) on b -> {a}
    //   Step 7: resolve(5, 6) on a -> {}
    let trace = simple_trace(
        vec![
            cl(1, &[1, 2]),
            cl(2, &[1, -2]),
            cl(3, &[-1, 2]),
            cl(4, &[-1, -2]),
        ],
        vec![rs(5, 2, 3, 4), rs(6, 2, 1, 2), rs(7, 1, 5, 6)],
        7,
    );
    assert_valid(&check_proof(&trace));
}

/// DPLL simulation via AYProofArtifact -> convert -> check roundtrip.
#[test]
fn test_dpll_sim_two_variable_unsat() {
    let artifact = AYProofArtifact {
        input_clauses: vec![
            zc(1, &[1, 2]),
            zc(2, &[1, -2]),
            zc(3, &[-1, 2]),
            zc(4, &[-1, -2]),
        ],
        resolution_steps: vec![
            zr(5, 2, 1, 2), // resolve on b -> {a}
            zr(6, 2, 3, 4), // resolve on b -> {-a}
            zr(7, 1, 5, 6), // resolve on a -> {}
        ],
        theory_lemmas: Vec::new(),
        empty_clause_id: 7,
    };
    let trace = convert_ay_artifact(&artifact);
    assert_valid(&check_proof(&trace));
}

/// Full DPLL on a 3-variable complete UNSAT (all 8 clauses).
/// Variable elimination tree: eliminate c, then b, then a.
#[test]
fn test_dpll_three_variable_all_combinations_unsat() {
    let artifact = AYProofArtifact {
        input_clauses: vec![
            zc(1, &[1, 2, 3]),
            zc(2, &[1, 2, -3]),
            zc(3, &[1, -2, 3]),
            zc(4, &[1, -2, -3]),
            zc(5, &[-1, 2, 3]),
            zc(6, &[-1, 2, -3]),
            zc(7, &[-1, -2, 3]),
            zc(8, &[-1, -2, -3]),
        ],
        resolution_steps: vec![
            zr(9, 3, 1, 2),    // {a,b}
            zr(10, 3, 3, 4),   // {a,-b}
            zr(11, 3, 5, 6),   // {-a,b}
            zr(12, 3, 7, 8),   // {-a,-b}
            zr(13, 2, 9, 10),  // {a}
            zr(14, 2, 11, 12), // {-a}
            zr(15, 1, 13, 14), // {}
        ],
        theory_lemmas: Vec::new(),
        empty_clause_id: 15,
    };
    let trace = convert_ay_artifact(&artifact);
    assert_valid(&check_proof(&trace));
}

// ===========================================================================
// Category 4: Compacted proof still validates after dead branch removal
// ===========================================================================

/// Proof with dead resolution branches compacts to a valid smaller proof.
#[test]
fn test_compaction_removes_dead_branches_preserves_validity() {
    let artifact = AYProofArtifact {
        input_clauses: vec![zc(1, &[1]), zc(2, &[-1]), zc(3, &[2]), zc(4, &[-2])],
        resolution_steps: vec![
            zr(5, 2, 3, 4), // dead
            zr(6, 1, 1, 2), // live -> {}
        ],
        theory_lemmas: Vec::new(),
        empty_clause_id: 6,
    };

    // Original is valid.
    let trace = convert_ay_artifact(&artifact);
    assert_valid(&check_proof(&trace));

    // Compact and verify.
    let (compacted, stats) = compact_with_stats(&artifact);
    assert_eq!(stats.removed_steps, 1);
    assert_eq!(stats.dead_branch_count, 1);

    let compacted_trace = convert_ay_artifact(&compacted);
    assert_valid(&check_proof(&compacted_trace));
    assert_eq!(compacted.resolution_steps.len(), 1);
}

/// Compaction of a larger proof with multiple dead branches preserves validity.
#[test]
fn test_compaction_multiple_dead_branches_valid() {
    let artifact = AYProofArtifact {
        input_clauses: vec![
            zc(1, &[1]),
            zc(2, &[-1, 2]),
            zc(3, &[-2, 3]),
            zc(4, &[-3]),
            zc(10, &[10]),
            zc(11, &[-10]),
            zc(20, &[20]),
            zc(21, &[-20]),
        ],
        resolution_steps: vec![
            zr(5, 1, 1, 2),     // {x2}
            zr(6, 2, 5, 3),     // {x3}
            zr(7, 3, 6, 4),     // {} (live)
            zr(50, 10, 10, 11), // dead
            zr(60, 20, 20, 21), // dead
        ],
        theory_lemmas: Vec::new(),
        empty_clause_id: 7,
    };

    let (compacted, stats) = compact_with_stats(&artifact);
    assert_eq!(stats.removed_steps, 2);
    assert_eq!(stats.dead_branch_count, 2);
    assert_eq!(compacted.resolution_steps.len(), 3);

    let trace = convert_ay_artifact(&compacted);
    assert_valid(&check_proof(&trace));
}

/// Compacted proof with theory lemmas on the critical path preserves validity.
#[test]
fn test_compaction_preserves_theory_lemma_on_critical_path() {
    let artifact = AYProofArtifact {
        input_clauses: vec![zc(1, &[1]), zc(10, &[2]), zc(11, &[-2])],
        resolution_steps: vec![
            zr(3, 1, 1, 2),    // live: resolve {a} with {-a} -> {}
            zr(12, 2, 10, 11), // dead: resolve {b} with {-b}
        ],
        theory_lemmas: vec![ztl(2, AYTheoryKind::Euf, &[-1])],
        empty_clause_id: 3,
    };

    let (compacted, stats) = compact_with_stats(&artifact);
    assert_eq!(stats.removed_steps, 1);
    assert_eq!(compacted.theory_lemmas.len(), 1);

    let trace = convert_ay_artifact(&compacted);
    assert_valid(&check_proof(&trace));
}

/// Double compaction is idempotent: compacting an already-compact proof
/// yields the same result and remains valid.
#[test]
fn test_compaction_idempotent_proof_still_valid() {
    let artifact = AYProofArtifact {
        input_clauses: vec![zc(1, &[1]), zc(2, &[-1]), zc(10, &[5]), zc(11, &[-5])],
        resolution_steps: vec![zr(3, 1, 1, 2), zr(12, 5, 10, 11)],
        theory_lemmas: Vec::new(),
        empty_clause_id: 3,
    };
    let first = compact_proof(&artifact);
    let second = compact_proof(&first);
    assert_eq!(first, second);

    let trace = convert_ay_artifact(&second);
    assert_valid(&check_proof(&trace));
}

// ===========================================================================
// Category 5: Theory lemma steps from contract state -> kernel accepts
// ===========================================================================

/// An EUF theory lemma participates in a valid resolution chain.
#[test]
fn test_euf_theory_lemma_in_resolution_chain_valid() {
    // Input: {a}
    // EUF lemma: {-a, b} (a implies b via equality reasoning)
    // Input: {-b}
    // Step 4: resolve({a}, {-a,b}) on a -> {b}
    // Step 5: resolve({b}, {-b}) on b -> {}
    let trace = ProofTrace {
        input_clauses: vec![cl(1, &[1]), cl(3, &[-2])],
        resolution_steps: vec![rs(4, 1, 1, 2), rs(5, 2, 4, 3)],
        theory_lemmas: vec![tl(2, "EUF", &[-1, 2])],
        empty_clause_id: 5,
    };
    assert_valid(&check_proof(&trace));

    let result = check_proof_with_theory(&trace);
    assert_eq!(result.result, CheckResult::Valid);
    assert_eq!(result.theory_stats.verified_count, 1);
}

/// An LRA theory lemma contributes to a valid proof.
#[test]
fn test_lra_theory_lemma_valid_proof() {
    // LRA lemma with 2 literals (minimum for Farkas certificate):
    // Lemma: {-a, -b} (the conjunction a AND b is infeasible in LRA)
    // Input: {a}
    // Input: {b}
    // Step 4: resolve({a}, {-a, -b}) on a -> {-b}
    // Step 5: resolve({b}, {-b}) on b -> {}
    let trace = ProofTrace {
        input_clauses: vec![cl(1, &[1]), cl(2, &[2])],
        resolution_steps: vec![rs(4, 1, 1, 3), rs(5, 2, 2, 4)],
        theory_lemmas: vec![tl(3, "LRA", &[-1, -2])],
        empty_clause_id: 5,
    };
    assert_valid(&check_proof(&trace));

    let result = check_proof_with_theory(&trace);
    assert_eq!(result.result, CheckResult::Valid);
    assert_eq!(result.theory_stats.verified_count, 1);
}

/// A NIA (non-linear integer arithmetic) theory lemma is trusted but
/// the proof still validates.
#[test]
fn test_nia_theory_lemma_trusted_valid_proof() {
    let trace = ProofTrace {
        input_clauses: vec![cl(1, &[1]), cl(3, &[-2])],
        resolution_steps: vec![rs(4, 1, 1, 2), rs(5, 2, 4, 3)],
        theory_lemmas: vec![tl(2, "NIA", &[-1, 2])],
        empty_clause_id: 5,
    };

    let result = check_proof_with_theory(&trace);
    assert_eq!(result.result, CheckResult::Valid);
    assert_eq!(result.theory_stats.trusted_count, 1);
    assert_eq!(result.theory_stats.verified_count, 0);
}

/// Multiple theory lemmas from different theories in a single proof.
#[test]
fn test_mixed_theory_lemmas_valid_proof() {
    // EUF lemma: {-a, b}  (id=10)
    // LRA lemma: {-b, -c} (id=20)
    // Input: {a}   (id=1)
    // Input: {c}   (id=2)
    // Step 30: resolve(1, 10) on a -> {b}
    // Step 31: resolve(30, 20) on b -> {-c}
    // Step 32: resolve(2, 31) on c -> {}
    let trace = ProofTrace {
        input_clauses: vec![cl(1, &[1]), cl(2, &[3])],
        resolution_steps: vec![rs(30, 1, 1, 10), rs(31, 2, 30, 20), rs(32, 3, 2, 31)],
        theory_lemmas: vec![tl(10, "EUF", &[-1, 2]), tl(20, "LRA", &[-2, -3])],
        empty_clause_id: 32,
    };

    let result = check_proof_with_theory(&trace);
    assert_eq!(result.result, CheckResult::Valid);
    assert_eq!(result.theory_stats.verified_count, 2);
}

// ===========================================================================
// Category 6: Large DPLL trace (20+ decisions) -> valid compact proof
// ===========================================================================

/// A 20-variable chain problem produces a valid proof with 20 resolution
/// steps, and compaction leaves it intact (no dead branches).
#[test]
fn test_large_dpll_trace_20_variables_valid() {
    let n = 20i64;
    let mut inputs = vec![zc(1, &[1])];
    for i in 1..n {
        inputs.push(zc((i + 1) as u64, &[-i, i + 1]));
    }
    inputs.push(zc((n + 1) as u64, &[-n]));

    let base = 100u64;
    let mut steps = vec![zr(base, 1, 1, 2)];
    for i in 2..n {
        steps.push(zr(
            base + (i - 1) as u64,
            i,
            base + (i - 2) as u64,
            (i + 1) as u64,
        ));
    }
    let final_id = base + (n - 1) as u64;
    steps.push(zr(final_id, n, final_id - 1, (n + 1) as u64));

    let artifact = AYProofArtifact {
        input_clauses: inputs,
        resolution_steps: steps,
        theory_lemmas: Vec::new(),
        empty_clause_id: final_id,
    };

    let trace = convert_ay_artifact(&artifact);
    assert_valid(&check_proof(&trace));

    let (compacted, stats) = compact_with_stats(&artifact);
    assert_eq!(stats.removed_steps, 0);
    assert_eq!(stats.compacted_steps, n as usize);

    let compacted_trace = convert_ay_artifact(&compacted);
    assert_valid(&check_proof(&compacted_trace));
}

/// A 30-variable chain with 15 dead branches: compaction removes the dead
/// branches and the remaining proof validates.
#[test]
fn test_large_dpll_trace_30_vars_with_dead_branches() {
    let n = 30i64;
    let mut inputs = vec![zc(1, &[1])];
    for i in 1..n {
        inputs.push(zc((i + 1) as u64, &[-i, i + 1]));
    }
    inputs.push(zc((n + 1) as u64, &[-n]));

    let base = 200u64;
    let mut steps = vec![zr(base, 1, 1, 2)];
    for i in 2..n {
        steps.push(zr(
            base + (i - 1) as u64,
            i,
            base + (i - 2) as u64,
            (i + 1) as u64,
        ));
    }
    let final_id = base + (n - 1) as u64;
    steps.push(zr(final_id, n, final_id - 1, (n + 1) as u64));

    // Add 15 dead branches.
    let dead_base = 5000u64;
    for i in 0..15u64 {
        let a = dead_base + i * 3;
        let b = a + 1;
        let c = a + 2;
        inputs.push(zc(a, &[(100 + i as i64)]));
        inputs.push(zc(b, &[-(100 + i as i64)]));
        steps.push(zr(c, 100 + i as i64, a, b));
    }

    let artifact = AYProofArtifact {
        input_clauses: inputs,
        resolution_steps: steps,
        theory_lemmas: Vec::new(),
        empty_clause_id: final_id,
    };

    let trace = convert_ay_artifact(&artifact);
    assert_valid(&check_proof(&trace));

    let (compacted, stats) = compact_with_stats(&artifact);
    assert_eq!(stats.removed_steps, 15);
    assert_eq!(stats.dead_branch_count, 15);

    let compacted_trace = convert_ay_artifact(&compacted);
    assert_valid(&check_proof(&compacted_trace));
}

/// Full 2-variable UNSAT built through AYProofArtifact, simulating a
/// DPLL search with 2+ decisions (variable elimination).
#[test]
fn test_dpll_variable_elimination_through_artifact() {
    let artifact = AYProofArtifact {
        input_clauses: vec![
            zc(1, &[1, 2]),
            zc(2, &[1, -2]),
            zc(3, &[-1, 2]),
            zc(4, &[-1, -2]),
        ],
        resolution_steps: vec![
            zr(5, 2, 1, 2), // {a}
            zr(6, 2, 3, 4), // {-a}
            zr(7, 1, 5, 6), // {}
        ],
        theory_lemmas: Vec::new(),
        empty_clause_id: 7,
    };

    let trace = convert_ay_artifact(&artifact);
    assert_valid(&check_proof(&trace));
}

// ===========================================================================
// Category 7: Invalid learned clause -> proof checker rejects
// ===========================================================================

/// A "learned clause" that does not follow from resolution produces
/// an invalid proof. The checker rejects because the pivot is not
/// in the parent.
#[test]
fn test_invalid_learned_clause_wrong_pivot_rejected() {
    // Clause 1: {a, b}
    // Clause 2: {-a}
    // Step 3 claims to resolve on pivot b, but -b is not in clause 2.
    let trace = simple_trace(vec![cl(1, &[1, 2]), cl(2, &[-1])], vec![rs(3, 2, 1, 2)], 3);
    assert_invalid(&check_proof(&trace), 3, "pivot");
}

/// A learned clause referencing a nonexistent parent clause is rejected.
#[test]
fn test_invalid_learned_clause_missing_parent_rejected() {
    let trace = simple_trace(vec![cl(1, &[1]), cl(2, &[-1])], vec![rs(3, 1, 1, 99)], 3);
    assert_invalid(&check_proof(&trace), 3, "unknown clause");
}

/// The final clause is not empty (contains leftover literals) -> rejected.
#[test]
fn test_invalid_learned_clause_non_empty_final_rejected() {
    // resolve({a, b}, {-a, b}) on a -> {b}, but we claim it is the empty clause.
    let trace = simple_trace(
        vec![cl(1, &[1, 2]), cl(2, &[-1, 2])],
        vec![rs(3, 1, 1, 2)],
        3,
    );
    assert_invalid(&check_proof(&trace), 3, "designated as empty but contains");
}

/// Duplicate clause IDs cause rejection.
#[test]
fn test_invalid_duplicate_clause_id_rejected() {
    let trace = simple_trace(vec![cl(1, &[1]), cl(1, &[-1])], vec![rs(2, 1, 1, 1)], 2);
    assert_invalid(&check_proof(&trace), 1, "uplicate");
}

/// A resolution step produces a resolvent that contradicts what we
/// would get from a correctly learned clause. The pivot appears in
/// one parent but not the other.
#[test]
fn test_invalid_resolution_pivot_absent_from_parent() {
    // Clause 1: {a}
    // Clause 2: {b}
    // Step 3 claims pivot=a but clause 2 has no -a.
    let trace = simple_trace(vec![cl(1, &[1]), cl(2, &[2])], vec![rs(3, 1, 1, 2)], 3);
    assert_invalid(&check_proof(&trace), 3, "pivot");
}

// ===========================================================================
// Category 8: Decision at wrong level -> proof chain breaks
// ===========================================================================

/// When a decision introduces a literal at the wrong level, the resulting
/// conflict analysis produces a learned clause whose resolution chain
/// does not derive the empty clause. The proof checker rejects.
#[test]
fn test_wrong_level_decision_breaks_proof_chain() {
    // Clause 1: {a, c}
    // Clause 2: {-a}
    // Clause 3: {b}
    // Step 4 resolves (1, 2) on a -> {c}
    // Step 5 claims to resolve (4, 3) on c, but 3 has no -c.
    let trace = simple_trace(
        vec![cl(1, &[1, 3]), cl(2, &[-1]), cl(3, &[2])],
        vec![rs(4, 1, 1, 2), rs(5, 3, 4, 3)],
        5,
    );
    assert_invalid(&check_proof(&trace), 5, "pivot");
}

/// A proof that skips a necessary intermediate resolution step cannot
/// derive the empty clause.
#[test]
fn test_missing_intermediate_resolution_non_empty_final() {
    // Clause 1: {a, b}
    // Clause 2: {-a, b}
    // Clause 3: {-b}
    // Correct proof: resolve(1,2,a)->{b}, resolve({b},3,b)->{}
    // Bug: skip the first step and try resolve(1,3,b) -> {a}, not empty.
    let trace = simple_trace(
        vec![cl(1, &[1, 2]), cl(2, &[-1, 2]), cl(3, &[-2])],
        vec![rs(4, 2, 1, 3)],
        4,
    );
    assert_invalid(&check_proof(&trace), 4, "designated as empty but contains");
}

/// A bad decision ordering leads to an incorrect resolution that the
/// checker rejects (parents do not contain the claimed pivot).
#[test]
fn test_bad_decision_order_wrong_resolution_rejected() {
    // Clause 1: {a}
    // Clause 2: {-a, b}
    // Clause 3: {-b}
    // Step 4: resolve(2, 3) on b -> {-a}. Valid.
    // Step 5: resolve(1, 4) on b. INVALID: clause 1 has no b, resolvent 4 has no -b.
    let trace = simple_trace(
        vec![cl(1, &[1]), cl(2, &[-1, 2]), cl(3, &[-2])],
        vec![rs(4, 2, 2, 3), rs(5, 2, 1, 4)],
        5,
    );
    assert_invalid(&check_proof(&trace), 5, "pivot");
}

// ===========================================================================
// Additional integration tests
// ===========================================================================

/// An EUF theory lemma that fails structural validation (tautological)
/// is rejected by check_proof_with_theory even though the propositional
/// resolution would otherwise be valid.
#[test]
fn test_invalid_euf_theory_lemma_tautological_rejected() {
    let trace = ProofTrace {
        input_clauses: vec![cl(1, &[1])],
        resolution_steps: vec![rs(3, 1, 1, 2)],
        theory_lemmas: vec![tl(2, "EUF", &[1, -1])],
        empty_clause_id: 3,
    };

    let result = check_proof_with_theory(&trace);
    assert_invalid(&result.result, 2, "tautology");
    assert_eq!(result.theory_stats.invalid_count, 1);
}

/// An LRA theory lemma with only one literal fails validation (Farkas
/// certificates require at least 2 literals).
#[test]
fn test_invalid_lra_single_literal_rejected() {
    let trace = ProofTrace {
        input_clauses: vec![cl(1, &[1])],
        resolution_steps: vec![rs(3, 1, 1, 2)],
        theory_lemmas: vec![tl(2, "LRA", &[-1])],
        empty_clause_id: 3,
    };

    let result = check_proof_with_theory(&trace);
    assert_invalid(&result.result, 2, "Farkas");
    assert_eq!(result.theory_stats.invalid_count, 1);
}

/// AYProofArtifact -> convert -> check roundtrip: theory lemmas are
/// preserved through the bridge conversion.
#[test]
fn test_bridge_conversion_preserves_theory_lemmas() {
    let artifact = AYProofArtifact {
        input_clauses: vec![zc(1, &[1])],
        resolution_steps: vec![zr(3, 1, 1, 2)],
        theory_lemmas: vec![ztl(2, AYTheoryKind::Euf, &[-1])],
        empty_clause_id: 3,
    };

    let trace = convert_ay_artifact(&artifact);
    assert_eq!(trace.theory_lemmas.len(), 1);
    assert_eq!(trace.theory_lemmas[0].theory, "EUF");
    assert_eq!(trace.theory_lemmas[0].clause.literals, vec![-1]);
    assert_valid(&check_proof(&trace));
}

/// Diamond-shaped DAG proof: two resolution steps share a common input
/// clause, then a third step resolves the two intermediates.
#[test]
fn test_diamond_dag_proof_valid() {
    // Clause 1: {a}        shared by steps 4 and 5
    // Clause 2: {-a, b}
    // Clause 3: {-a, -b}
    // Step 4: resolve(1, 2) on a -> {b}
    // Step 5: resolve(1, 3) on a -> {-b}
    // Step 6: resolve(4, 5) on b -> {}
    let trace = simple_trace(
        vec![cl(1, &[1]), cl(2, &[-1, 2]), cl(3, &[-1, -2])],
        vec![rs(4, 1, 1, 2), rs(5, 1, 1, 3), rs(6, 2, 4, 5)],
        6,
    );
    assert_valid(&check_proof(&trace));
}

/// Proof where resolution steps and theory lemmas interleave: the
/// kernel checks theory lemmas before running the resolution checker.
#[test]
fn test_interleaved_theory_and_resolution_steps_valid() {
    let trace = ProofTrace {
        input_clauses: vec![cl(1, &[1]), cl(2, &[3])],
        resolution_steps: vec![rs(11, 1, 1, 10), rs(21, 2, 11, 20), rs(22, 3, 2, 21)],
        theory_lemmas: vec![tl(10, "EUF", &[-1, 2]), tl(20, "LRA", &[-2, -3])],
        empty_clause_id: 22,
    };

    let result = check_proof_with_theory(&trace);
    assert_eq!(result.result, CheckResult::Valid);
    assert_eq!(result.theory_stats.verified_count, 2);
    assert_eq!(result.theory_stats.invalid_count, 0);
}

/// Empty clause appearing directly as an input is valid without any
/// resolution steps.
#[test]
fn test_empty_input_clause_trivial_proof() {
    let trace = simple_trace(vec![cl(1, &[])], vec![], 1);
    assert_valid(&check_proof(&trace));
}

/// A 50-variable chain with 25 dead branches: stress test for compaction
/// + validation pipeline.
#[test]
fn test_stress_50_variable_chain_25_dead_branches() {
    let n = 50i64;
    let mut inputs = vec![zc(1, &[1])];
    for i in 1..n {
        inputs.push(zc((i + 1) as u64, &[-i, i + 1]));
    }
    inputs.push(zc((n + 1) as u64, &[-n]));

    let base = 500u64;
    let mut steps = vec![zr(base, 1, 1, 2)];
    for i in 2..n {
        steps.push(zr(
            base + (i - 1) as u64,
            i,
            base + (i - 2) as u64,
            (i + 1) as u64,
        ));
    }
    let final_id = base + (n - 1) as u64;
    steps.push(zr(final_id, n, final_id - 1, (n + 1) as u64));

    // 25 dead branches.
    let dead_base = 8000u64;
    for i in 0..25u64 {
        let a = dead_base + i * 3;
        let b = a + 1;
        let c = a + 2;
        inputs.push(zc(a, &[(200 + i as i64)]));
        inputs.push(zc(b, &[-(200 + i as i64)]));
        steps.push(zr(c, 200 + i as i64, a, b));
    }

    let artifact = AYProofArtifact {
        input_clauses: inputs,
        resolution_steps: steps,
        theory_lemmas: Vec::new(),
        empty_clause_id: final_id,
    };

    // Original validates.
    let trace = convert_ay_artifact(&artifact);
    assert_valid(&check_proof(&trace));

    // Compacted validates and removes all dead branches.
    let (compacted, stats) = compact_with_stats(&artifact);
    assert_eq!(stats.removed_steps, 25);
    assert_eq!(stats.dead_branch_count, 25);
    assert_eq!(compacted.resolution_steps.len(), n as usize);

    let compacted_trace = convert_ay_artifact(&compacted);
    assert_valid(&check_proof(&compacted_trace));
}
