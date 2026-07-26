// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Integration tests that validate complete proof chains from construction
//! through checking, exercising the public API of `trust_vc_kernel`.
//!
//! Tests cover propositional resolution chains (short and long), invalid
//! proofs (wrong pivot, missing assumptions, dangling references),
//! theory lemma integration (EUF/LRA valid and invalid), mixed chains,
//! edge cases (empty proof, single assumption, duplicate IDs),
//! DAG-shaped proofs, and large-scale performance.

use trust_vc_kernel::{
    check_proof, check_proof_with_theory, CheckResult, CheckResultWithStats, Clause, ProofTrace,
    ResolutionStep, TheoryLemma,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

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

/// Build a proof trace with no theory lemmas.
fn trace(inputs: Vec<Clause>, steps: Vec<ResolutionStep>, empty: u64) -> ProofTrace {
    ProofTrace {
        input_clauses: inputs,
        resolution_steps: steps,
        theory_lemmas: vec![],
        empty_clause_id: empty,
    }
}

/// Build a proof trace with theory lemmas.
fn trace_with_theories(
    inputs: Vec<Clause>,
    steps: Vec<ResolutionStep>,
    theories: Vec<TheoryLemma>,
    empty: u64,
) -> ProofTrace {
    ProofTrace {
        input_clauses: inputs,
        resolution_steps: steps,
        theory_lemmas: theories,
        empty_clause_id: empty,
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

/// Assert that a CheckResult is Invalid at the given step with a reason
/// containing the expected substring.
fn assert_invalid(result: &CheckResult, expected_step: u64, substr: &str) {
    match result {
        CheckResult::Invalid { step, reason } => {
            assert_eq!(
                *step, expected_step,
                "expected invalid at step {expected_step}, got step {step}"
            );
            assert!(
                reason.contains(substr),
                "expected reason to contain '{substr}', got: {reason}"
            );
        }
        CheckResult::Valid => panic!("expected Invalid, got Valid"),
        _ => panic!("unexpected CheckResult variant"),
    }
}

// ===========================================================================
// 1. Simple propositional resolution chains (2-5 clauses) -> valid
// ===========================================================================

#[test]
fn test_chain_two_clauses_resolve_to_empty() {
    // {p} and {-p} resolve on p to produce the empty clause.
    let t = trace(vec![cl(1, &[1]), cl(2, &[-1])], vec![rs(3, 1, 1, 2)], 3);
    assert_eq!(check_proof(&t), CheckResult::Valid);
}

#[test]
fn test_chain_three_clauses_unit_propagation() {
    // {p}, {-p, q}, {-q} -> resolve p to get {q}, then resolve q to get {}.
    let t = trace(
        vec![cl(1, &[1]), cl(2, &[-1, 2]), cl(3, &[-2])],
        vec![rs(10, 1, 1, 2), rs(11, 2, 10, 3)],
        11,
    );
    assert_eq!(check_proof(&t), CheckResult::Valid);
}

#[test]
fn test_chain_four_clauses_linear() {
    // {a}, {-a, b}, {-b, c}, {-c} -> chain resolves to empty.
    let t = trace(
        vec![cl(1, &[1]), cl(2, &[-1, 2]), cl(3, &[-2, 3]), cl(4, &[-3])],
        vec![rs(10, 1, 1, 2), rs(11, 2, 10, 3), rs(12, 3, 11, 4)],
        12,
    );
    assert_eq!(check_proof(&t), CheckResult::Valid);
}

#[test]
fn test_chain_five_clauses_linear() {
    // {a}, {-a,b}, {-b,c}, {-c,d}, {-d}
    let t = trace(
        vec![
            cl(1, &[1]),
            cl(2, &[-1, 2]),
            cl(3, &[-2, 3]),
            cl(4, &[-3, 4]),
            cl(5, &[-4]),
        ],
        vec![
            rs(10, 1, 1, 2),
            rs(11, 2, 10, 3),
            rs(12, 3, 11, 4),
            rs(13, 4, 12, 5),
        ],
        13,
    );
    assert_eq!(check_proof(&t), CheckResult::Valid);
}

#[test]
fn test_chain_three_clauses_with_extra_literals() {
    // {a, b}, {-a, c}, {-b, -c}
    // Resolve a between clause 1 and 2: {b, c}
    // Resolve b between {b, c} and clause with {-b, -c}: {c, -c}
    // That's not empty. Instead, build a proper proof:
    // {a, b}, {-a}, {-b}
    // Resolve a: {b}, then resolve b: {}
    let t = trace(
        vec![cl(1, &[1, 2]), cl(2, &[-1]), cl(3, &[-2])],
        vec![rs(10, 1, 1, 2), rs(11, 2, 10, 3)],
        11,
    );
    assert_eq!(check_proof(&t), CheckResult::Valid);
}

// ===========================================================================
// 2. Longer chains (10-20 steps) -> still validates correctly
// ===========================================================================

#[test]
fn test_chain_ten_step_linear() {
    // Build a chain of length 10: {1}, {-1,2}, {-2,3}, ..., {-10,11}, {-11}
    // Resolution steps eliminate variables 1 through 11 in sequence.
    let n = 10i64;
    let mut inputs = vec![cl(1, &[1])];
    for i in 1..=n {
        inputs.push(cl((i + 1) as u64, &[-i, i + 1]));
    }
    inputs.push(cl((n + 2) as u64, &[-(n + 1)]));

    let base = 100u64;
    let mut steps = vec![rs(base, 1, 1, 2)];
    for i in 2..=n {
        steps.push(rs(
            base + (i - 1) as u64,
            i,
            base + (i - 2) as u64,
            (i + 1) as u64,
        ));
    }
    let final_id = base + n as u64;
    steps.push(rs(final_id, n + 1, final_id - 1, (n + 2) as u64));

    let t = trace(inputs, steps, final_id);
    assert_eq!(check_proof(&t), CheckResult::Valid);
}

#[test]
fn test_chain_twenty_step_linear() {
    let n = 20i64;
    let mut inputs = vec![cl(1, &[1])];
    for i in 1..=n {
        inputs.push(cl((i + 1) as u64, &[-i, i + 1]));
    }
    inputs.push(cl((n + 2) as u64, &[-(n + 1)]));

    let base = 100u64;
    let mut steps = vec![rs(base, 1, 1, 2)];
    for i in 2..=n {
        steps.push(rs(
            base + (i - 1) as u64,
            i,
            base + (i - 2) as u64,
            (i + 1) as u64,
        ));
    }
    let final_id = base + n as u64;
    steps.push(rs(final_id, n + 1, final_id - 1, (n + 2) as u64));

    let t = trace(inputs, steps, final_id);
    assert_eq!(check_proof(&t), CheckResult::Valid);
}

#[test]
fn test_chain_fifteen_steps_with_branching() {
    // Build a proof with two independent sub-chains that merge.
    // Sub-chain A: {a}, {-a,x} => resolve a => {x}   (step 100)
    // Sub-chain B: {b}, {-b,-x} => resolve b => {-x}  (step 101)
    // Final: resolve x between {x} and {-x} => {}      (step 102)
    //
    // Extend with more intermediate variables for 15+ steps.
    // Chain A: v1, {-v1,v2}, ..., {-v6,v7}  (7 input clauses)
    // Chain B: v8, {-v8,v9}, ..., {-v13,-v7} (7 input clauses)
    // A resolves v1..v6 to get {v7}, B resolves v8..v13 to get {-v7},
    // then resolve v7.

    // Chain A inputs: clause 1={1}, clause 2={-1,2}, ..., clause 7={-6,7}
    let mut inputs = Vec::new();
    for i in 1..=7i64 {
        if i == 1 {
            inputs.push(cl(i as u64, &[i]));
        } else {
            inputs.push(cl(i as u64, &[-(i - 1), i]));
        }
    }

    // Chain B inputs: clause 8={8}, clause 9={-8,9}, ..., clause 13={-12,13},
    // clause 14={-13,-7}
    for i in 8..=13i64 {
        if i == 8 {
            inputs.push(cl(i as u64, &[i]));
        } else {
            inputs.push(cl(i as u64, &[-(i - 1), i]));
        }
    }
    inputs.push(cl(14, &[-13, -7]));

    // Chain A resolution: resolve variables 1 through 6
    // Step 100: resolve 1 between cl(1)={1} and cl(2)={-1,2} => {2}
    // Step 101: resolve 2 between {2} and cl(3)={-2,3} => {3}
    // ...
    // Step 105: resolve 6 between {6} and cl(7)={-6,7} => {7}
    let mut steps = Vec::new();
    steps.push(rs(100, 1, 1, 2));
    for i in 2..=6i64 {
        steps.push(rs((99 + i) as u64, i, (98 + i) as u64, (i + 1) as u64));
    }
    // After step 105, we have clause 105 = {7}

    // Chain B resolution: resolve variables 8 through 13
    // Step 200: resolve 8 between cl(8)={8} and cl(9)={-8,9} => {9}
    // ...
    // Step 205: resolve 13 between {13} and cl(14)={-13,-7} => {-7}
    steps.push(rs(200, 8, 8, 9));
    for i in 9..=13i64 {
        steps.push(rs(
            (192 + i) as u64,
            i,
            (191 + i) as u64,
            if i < 13 { (i + 1) as u64 } else { 14 },
        ));
    }
    // After step 205, we have clause 205 = {-7}

    // Final: resolve 7 between clause 105={7} and clause 205={-7} => {}
    steps.push(rs(300, 7, 105, 205));

    let t = trace(inputs, steps, 300);
    assert_eq!(check_proof(&t), CheckResult::Valid);
}

// ===========================================================================
// 3. Invalid resolution (wrong pivot) -> detected as invalid
// ===========================================================================

#[test]
fn test_invalid_wrong_pivot_variable() {
    // {a, b} and {-a} with pivot=b (b is not in parent2).
    let t = trace(vec![cl(1, &[1, 2]), cl(2, &[-1])], vec![rs(3, 2, 1, 2)], 3);
    assert_invalid(&check_proof(&t), 3, "pivot");
}

#[test]
fn test_invalid_pivot_absent_from_both_parents() {
    // {a} and {-b}, pivot=c (c appears nowhere).
    let t = trace(vec![cl(1, &[1]), cl(2, &[-2])], vec![rs(3, 3, 1, 2)], 3);
    assert_invalid(&check_proof(&t), 3, "pivot");
}

#[test]
fn test_invalid_pivot_same_polarity_in_both() {
    // {a} and {a}, pivot=a. Both have +a but neither has -a.
    let t = trace(vec![cl(1, &[1]), cl(2, &[1])], vec![rs(3, 1, 1, 2)], 3);
    assert_invalid(&check_proof(&t), 3, "pivot");
}

// ===========================================================================
// 4. Missing assumption -> detected
// ===========================================================================

#[test]
fn test_invalid_missing_parent_clause() {
    // Step references parent clause ID 99, which does not exist.
    let t = trace(vec![cl(1, &[1])], vec![rs(3, 1, 1, 99)], 3);
    assert_invalid(&check_proof(&t), 3, "unknown clause");
}

#[test]
fn test_invalid_missing_both_parents() {
    // Both parent IDs are bogus.
    let t = trace(vec![cl(1, &[1])], vec![rs(3, 1, 50, 51)], 3);
    assert_invalid(&check_proof(&t), 3, "unknown clause");
}

#[test]
fn test_invalid_empty_clause_id_not_derived() {
    // Valid resolution but empty_clause_id points to non-existent clause.
    let t = trace(vec![cl(1, &[1]), cl(2, &[-1])], vec![rs(3, 1, 1, 2)], 999);
    assert_invalid(&check_proof(&t), 999, "not found");
}

// ===========================================================================
// 5. Theory lemma steps with valid EUF justification -> accepted
// ===========================================================================

#[test]
fn test_euf_lemma_transitivity_in_proof() {
    // Input: {a} (clause 1)
    // EUF lemma: {-a} (clause 2) representing a!=a being contradictory
    // Resolution: resolve a => {}
    let t = trace_with_theories(
        vec![cl(1, &[1])],
        vec![rs(3, 1, 1, 2)],
        vec![tl(2, "EUF", &[-1])],
        3,
    );
    let result = check_proof_with_theory(&t);
    assert_eq!(result.result, CheckResult::Valid);
    assert_eq!(result.theory_stats.verified_count, 1);
    assert_eq!(result.theory_stats.invalid_count, 0);
}

#[test]
fn test_euf_lemma_congruence_pattern_valid() {
    // EUF lemma: (-1, -2, 3) meaning (a!=b) \/ (b!=c) \/ (a=c)
    // Use the lemma in a resolution proof.
    // Inputs: {1} (a=b), {2} (b=c), {-3} (a!=c)
    // EUF lemma ID 10: {-1, -2, 3}
    // Step 20: resolve 1 between {1} and {-1,-2,3} => {-2,3}
    // Step 21: resolve 2 between {2} and {-2,3} => {3}
    // Step 22: resolve 3 between {3} and {-3} => {}
    let t = trace_with_theories(
        vec![cl(1, &[1]), cl(2, &[2]), cl(3, &[-3])],
        vec![rs(20, 1, 1, 10), rs(21, 2, 2, 20), rs(22, 3, 21, 3)],
        vec![tl(10, "EUF", &[-1, -2, 3])],
        22,
    );
    let result = check_proof_with_theory(&t);
    assert_eq!(result.result, CheckResult::Valid);
    assert_eq!(result.theory_stats.verified_count, 1);
}

// ===========================================================================
// 6. Theory lemma steps with invalid justification -> rejected
// ===========================================================================

#[test]
fn test_euf_lemma_empty_clause_rejected() {
    // An EUF lemma with no literals is structurally invalid.
    let t = trace_with_theories(
        vec![cl(1, &[1])],
        vec![rs(3, 1, 1, 2)],
        vec![tl(2, "EUF", &[])],
        3,
    );
    let result = check_proof_with_theory(&t);
    assert!(matches!(result.result, CheckResult::Invalid { .. }));
    assert_eq!(result.theory_stats.invalid_count, 1);
}

#[test]
fn test_euf_lemma_multiple_positive_rejected() {
    // EUF lemma with 2 positive literals: invalid structurally.
    let t = trace_with_theories(
        vec![cl(1, &[-1]), cl(3, &[-2])],
        vec![rs(10, 1, 2, 1), rs(11, 2, 10, 3)],
        vec![tl(2, "EUF", &[1, 2])],
        11,
    );
    let result = check_proof_with_theory(&t);
    assert!(matches!(result.result, CheckResult::Invalid { .. }));
    assert_eq!(result.theory_stats.invalid_count, 1);
}

#[test]
fn test_lra_lemma_single_literal_rejected() {
    // LRA Farkas needs >= 2 literals.
    let t = trace_with_theories(
        vec![cl(1, &[1])],
        vec![rs(3, 1, 1, 2)],
        vec![tl(2, "LRA", &[-1])],
        3,
    );
    let result = check_proof_with_theory(&t);
    assert!(matches!(result.result, CheckResult::Invalid { .. }));
    assert_eq!(result.theory_stats.invalid_count, 1);
}

#[test]
fn test_euf_lemma_tautology_rejected() {
    // EUF lemma containing both literal 5 and -5 is a tautology.
    let t = trace_with_theories(vec![cl(1, &[1])], vec![], vec![tl(2, "EUF", &[5, -5])], 1);
    let result = check_proof_with_theory(&t);
    assert!(matches!(result.result, CheckResult::Invalid { .. }));
    assert_eq!(result.theory_stats.invalid_count, 1);
}

// ===========================================================================
// 7. Mixed resolution + theory lemma chains
// ===========================================================================

#[test]
fn test_mixed_euf_and_resolution_chain() {
    // Inputs: {a,b}=cl(1), {-b}=cl(2)
    // EUF lemma: {-a} = tl(10)
    // Step 20: resolve b between cl(1)={a,b} and cl(2)={-b} => {a}
    // Step 21: resolve a between {a} and tl(10)={-a} => {}
    let t = trace_with_theories(
        vec![cl(1, &[1, 2]), cl(2, &[-2])],
        vec![rs(20, 2, 1, 2), rs(21, 1, 20, 10)],
        vec![tl(10, "EUF", &[-1])],
        21,
    );
    let result = check_proof_with_theory(&t);
    assert_eq!(result.result, CheckResult::Valid);
    assert_eq!(result.theory_stats.verified_count, 1);
}

#[test]
fn test_mixed_lra_and_euf_lemmas_in_proof() {
    // Input: {a} = cl(1)
    // EUF lemma tl(10): {-a, b}  (at most 1 positive => valid)
    // LRA lemma tl(11): {-b, -c} (2 lits => valid Farkas)
    // Input: {c} = cl(2)
    // Step 20: resolve a between {a} and {-a,b} => {b}
    // Step 21: resolve b between {b} and {-b,-c} => {-c}
    // Step 22: resolve c between {-c} and {c} => {}
    let t = trace_with_theories(
        vec![cl(1, &[1]), cl(2, &[3])],
        vec![rs(20, 1, 1, 10), rs(21, 2, 20, 11), rs(22, 3, 21, 2)],
        vec![tl(10, "EUF", &[-1, 2]), tl(11, "LRA", &[-2, -3])],
        22,
    );
    let result = check_proof_with_theory(&t);
    assert_eq!(result.result, CheckResult::Valid);
    assert_eq!(result.theory_stats.verified_count, 2);
    assert_eq!(result.theory_stats.trusted_count, 0);
}

#[test]
fn test_mixed_trusted_and_verified_theory_lemmas() {
    // Include a BV (trusted) and an EUF (verified) lemma in one proof.
    // Input: {a} = cl(1)
    // BV lemma tl(10): {-a, b}   (trusted)
    // EUF lemma tl(11): {-b}     (verified: 1 negative literal)
    // Step 20: resolve a => {b}
    // Step 21: resolve b => {}
    let t = trace_with_theories(
        vec![cl(1, &[1])],
        vec![rs(20, 1, 1, 10), rs(21, 2, 20, 11)],
        vec![tl(10, "BV", &[-1, 2]), tl(11, "EUF", &[-2])],
        21,
    );
    let result = check_proof_with_theory(&t);
    assert_eq!(result.result, CheckResult::Valid);
    assert_eq!(result.theory_stats.verified_count, 1);
    assert_eq!(result.theory_stats.trusted_count, 1);
}

// ===========================================================================
// 8. Empty proof -> handled gracefully
// ===========================================================================

#[test]
fn test_empty_proof_no_clauses_no_steps() {
    // No input clauses, no steps, empty_clause_id points nowhere.
    let t = trace(vec![], vec![], 1);
    assert_invalid(&check_proof(&t), 1, "not found");
}

#[test]
fn test_empty_proof_with_theory_returns_stats() {
    // No clauses at all, check_proof_with_theory should handle gracefully.
    let t = trace_with_theories(vec![], vec![], vec![], 1);
    let result = check_proof_with_theory(&t);
    assert!(matches!(result.result, CheckResult::Invalid { .. }));
    assert_eq!(result.theory_stats.total(), 0);
}

// ===========================================================================
// 9. Single assumption proof -> validates
// ===========================================================================

#[test]
fn test_single_empty_input_clause_is_valid_proof() {
    // A single empty clause as input is already a proof of unsatisfiability.
    let t = trace(vec![cl(1, &[])], vec![], 1);
    assert_eq!(check_proof(&t), CheckResult::Valid);
}

#[test]
fn test_single_nonempty_clause_not_valid_as_empty() {
    // A single non-empty clause does not serve as the empty clause.
    let t = trace(vec![cl(1, &[42])], vec![], 1);
    assert_invalid(&check_proof(&t), 1, "contains");
}

// ===========================================================================
// 10. Diamond-shaped DAG resolution patterns
// ===========================================================================

#[test]
fn test_diamond_dag_shared_intermediate() {
    // Diamond: two resolution steps share a common parent (input clause),
    // then a third step resolves the two intermediates.
    //
    // Input clauses:
    //   cl(1) = {a, b}
    //   cl(2) = {-a, c}
    //   cl(3) = {-b, -c}
    //
    // Step 10: resolve a between cl(1)={a,b} and cl(2)={-a,c} => {b,c}
    // Step 11: resolve b between cl(1)={a,b} and cl(3)={-b,-c} => {a,-c}
    // Step 12: resolve c between step10={b,c} and step11={a,-c} => {a,b}
    // That doesn't lead to empty. Redesign:
    //
    // Diamond where two branches share an input clause and converge:
    //   cl(1) = {a, b}
    //   cl(2) = {-a}
    //   cl(3) = {-b}
    // Step 10: resolve a between cl(1) and cl(2) => {b}   (uses cl(1))
    // Step 11: resolve b between step10={b} and cl(3) => {}
    //
    // For a true diamond, we need a clause used twice:
    //   cl(1) = {a, b}
    //   cl(2) = {-a, c}
    //   cl(3) = {-b, -c}
    //   cl(4) = {-a, -c}
    //
    // Left branch:
    //   Step 10: resolve a between cl(1)={a,b} and cl(2)={-a,c} => {b,c}
    // Right branch:
    //   Step 11: resolve a between cl(1)={a,b} and cl(4)={-a,-c} => {b,-c}
    // Merge:
    //   Step 12: resolve c between step10={b,c} and step11={b,-c} => {b}
    //
    // Now we still need to eliminate b:
    //   cl(5) = {-b}
    //   Step 13: resolve b between step12={b} and cl(5)={-b} => {}
    let t = trace(
        vec![
            cl(1, &[1, 2]),
            cl(2, &[-1, 3]),
            cl(4, &[-1, -3]),
            cl(5, &[-2]),
        ],
        vec![
            rs(10, 1, 1, 2),   // resolve a: {a,b} + {-a,c} => {b,c}
            rs(11, 1, 1, 4),   // resolve a: {a,b} + {-a,-c} => {b,-c}
            rs(12, 3, 10, 11), // resolve c: {b,c} + {b,-c} => {b}
            rs(13, 2, 12, 5),  // resolve b: {b} + {-b} => {}
        ],
        13,
    );
    assert_eq!(check_proof(&t), CheckResult::Valid);
}

#[test]
fn test_diamond_dag_two_shared_parents() {
    // Both intermediate results share two common parents.
    //   cl(1) = {a, b}
    //   cl(2) = {-a, -b}
    // Step 10: resolve a between cl(1) and cl(2) => {b, -b}
    // That resolvent contains b and -b. We actually need a complementary structure.
    //
    // cl(1) = {a, b}
    // cl(2) = {a, -b}
    // cl(3) = {-a}
    // Step 10: resolve b between cl(1)={a,b} and cl(2)={a,-b} => {a}
    // Step 11: resolve a between step10={a} and cl(3)={-a} => {}
    let t = trace(
        vec![cl(1, &[1, 2]), cl(2, &[1, -2]), cl(3, &[-1])],
        vec![
            rs(10, 2, 1, 2),  // resolve b: {a,b} + {a,-b} => {a}
            rs(11, 1, 10, 3), // resolve a: {a} + {-a} => {}
        ],
        11,
    );
    assert_eq!(check_proof(&t), CheckResult::Valid);
}

// ===========================================================================
// 11. Proof with duplicate step IDs -> handled
// ===========================================================================

#[test]
fn test_duplicate_input_clause_ids_rejected() {
    // Two input clauses with the same ID.
    let t = trace(vec![cl(1, &[1]), cl(1, &[-1])], vec![rs(2, 1, 1, 1)], 2);
    assert_invalid(&check_proof(&t), 1, "duplicate");
}

#[test]
fn test_duplicate_resolution_step_id_with_input_rejected() {
    // Resolution step ID collides with input clause ID.
    let t = trace(
        vec![cl(1, &[1]), cl(2, &[-1])],
        vec![rs(1, 1, 1, 2)], // step ID 1 = same as input clause 1
        1,
    );
    assert_invalid(&check_proof(&t), 1, "duplicate");
}

#[test]
fn test_duplicate_theory_lemma_and_input_id_rejected() {
    // Theory lemma ID collides with input clause ID.
    let t = trace_with_theories(vec![cl(1, &[1])], vec![], vec![tl(1, "EUF", &[-1])], 1);
    assert_invalid(&check_proof(&t), 1, "duplicate");
}

#[test]
fn test_duplicate_resolution_step_ids_rejected() {
    // Two resolution steps with the same ID.
    // cl(1)={a,b}, cl(2)={-a}, cl(3)={-b}
    // Step 10: resolve a => {b}
    // Step 10 (duplicate): resolve b => {}
    let t = trace(
        vec![cl(1, &[1, 2]), cl(2, &[-1]), cl(3, &[-2])],
        vec![rs(10, 1, 1, 2), rs(10, 2, 10, 3)],
        10,
    );
    assert_invalid(&check_proof(&t), 10, "duplicate");
}

// ===========================================================================
// 12. Proof referencing non-existent steps -> rejected
// ===========================================================================

#[test]
fn test_reference_nonexistent_parent1() {
    let t = trace(vec![cl(1, &[1]), cl(2, &[-1])], vec![rs(3, 1, 999, 2)], 3);
    assert_invalid(&check_proof(&t), 3, "unknown clause");
}

#[test]
fn test_reference_nonexistent_parent2() {
    let t = trace(vec![cl(1, &[1]), cl(2, &[-1])], vec![rs(3, 1, 1, 888)], 3);
    assert_invalid(&check_proof(&t), 3, "unknown clause");
}

#[test]
fn test_reference_future_step_as_parent() {
    // Step 10 references step 11 as a parent, but step 11 hasn't been
    // processed yet. Steps are processed in order, so this should fail.
    let t = trace(
        vec![cl(1, &[1]), cl(2, &[-1, 2]), cl(3, &[-2])],
        vec![
            rs(10, 2, 11, 3), // references step 11 which comes AFTER
            rs(11, 1, 1, 2),
        ],
        10,
    );
    assert_invalid(&check_proof(&t), 10, "unknown clause");
}

// ===========================================================================
// 13. Large proof (100+ steps) -> performance acceptable
// ===========================================================================

#[test]
fn test_large_proof_100_steps() {
    let n = 100i64;
    let mut inputs = vec![cl(1, &[1])];
    for i in 1..=n {
        inputs.push(cl((i + 1) as u64, &[-i, i + 1]));
    }
    inputs.push(cl((n + 2) as u64, &[-(n + 1)]));

    let base = 1000u64;
    let mut steps = vec![rs(base, 1, 1, 2)];
    for i in 2..=n {
        steps.push(rs(
            base + (i - 1) as u64,
            i,
            base + (i - 2) as u64,
            (i + 1) as u64,
        ));
    }
    let final_id = base + n as u64;
    steps.push(rs(final_id, n + 1, final_id - 1, (n + 2) as u64));

    let t = trace(inputs, steps, final_id);
    assert_eq!(check_proof(&t), CheckResult::Valid);
}

#[test]
fn test_large_proof_500_steps() {
    let n = 500i64;
    let mut inputs = vec![cl(1, &[1])];
    for i in 1..=n {
        inputs.push(cl((i + 1) as u64, &[-i, i + 1]));
    }
    inputs.push(cl((n + 2) as u64, &[-(n + 1)]));

    let base = 10_000u64;
    let mut steps = vec![rs(base, 1, 1, 2)];
    for i in 2..=n {
        steps.push(rs(
            base + (i - 1) as u64,
            i,
            base + (i - 2) as u64,
            (i + 1) as u64,
        ));
    }
    let final_id = base + n as u64;
    steps.push(rs(final_id, n + 1, final_id - 1, (n + 2) as u64));

    let t = trace(inputs, steps, final_id);
    assert_eq!(check_proof(&t), CheckResult::Valid);
}

#[test]
fn test_large_proof_with_theory_lemmas() {
    // 100 resolution steps + 20 theory lemmas (10 EUF + 10 BV).
    // Structure: chain of 100 variables, with EUF and BV lemmas providing
    // some of the intermediate clauses.
    let mut inputs = Vec::new();
    let mut theories = Vec::new();
    let mut steps = Vec::new();

    // Start with {1}
    inputs.push(cl(1, &[1]));

    // Build 120 link clauses: some as inputs, some as EUF lemmas, some as BV.
    // Even-numbered links (2,4,...,20) come from EUF lemmas (IDs 5000+).
    // Links 22,24,...,40 come from BV lemmas (IDs 6000+).
    // All other links are regular input clauses.
    for i in 1..=100i64 {
        let link_id = (i + 1) as u64;
        let link_lits = vec![-i, i + 1];

        if i <= 20 && i % 2 == 0 {
            // EUF lemma (at most 1 positive literal: i+1 is positive)
            let tid = 5000 + (i / 2) as u64;
            theories.push(tl(tid, "EUF", &link_lits));
        } else if i > 20 && i <= 40 && i % 2 == 0 {
            // BV lemma (trusted)
            let tid = 6000 + ((i - 20) / 2) as u64;
            theories.push(tl(tid, "BV", &link_lits));
        } else {
            inputs.push(cl(link_id, &link_lits));
        }
    }

    // Final clause: {-(n+1)}
    inputs.push(cl(200, &[-101]));

    // Resolution steps: chain variables 1..101
    let base = 10_000u64;
    // First step resolves variable 1
    let first_parent2 = 2u64; // cl(2) = {-1, 2}
    steps.push(rs(base, 1, 1, first_parent2));

    for i in 2..=100i64 {
        // Figure out where the link clause for variable i lives.
        let link_clause_id = if i <= 20 && i % 2 == 0 {
            5000 + (i / 2) as u64 // EUF lemma
        } else if i > 20 && i <= 40 && i % 2 == 0 {
            6000 + ((i - 20) / 2) as u64 // BV lemma
        } else {
            (i + 1) as u64 // input clause
        };

        steps.push(rs(
            base + (i - 1) as u64,
            i,
            base + (i - 2) as u64,
            link_clause_id,
        ));
    }

    // Final step: resolve variable 101
    let final_id = base + 100;
    steps.push(rs(final_id, 101, final_id - 1, 200));

    let t = trace_with_theories(inputs, steps, theories, final_id);
    let result = check_proof_with_theory(&t);
    assert_eq!(result.result, CheckResult::Valid);

    // 10 EUF lemmas should be verified, 10 BV lemmas should be trusted.
    assert_eq!(result.theory_stats.verified_count, 10);
    assert_eq!(result.theory_stats.trusted_count, 10);
    assert_eq!(result.theory_stats.invalid_count, 0);
}

// ===========================================================================
// Additional coverage: reversed polarity, non-linear DAGs, etc.
// ===========================================================================

#[test]
fn test_reversed_polarity_pivot_accepted() {
    // Parent1 has -pivot and parent2 has +pivot (reversed from typical).
    // {-a} and {a} with pivot=a should still resolve to {}.
    let t = trace(vec![cl(1, &[-1]), cl(2, &[1])], vec![rs(3, 1, 1, 2)], 3);
    assert_eq!(check_proof(&t), CheckResult::Valid);
}

#[test]
fn test_final_clause_not_empty_detected() {
    // Resolution produces a non-empty clause, but we claim it's the empty clause.
    // {a, b} and {-a, c} => resolve a => {b, c} (not empty)
    let t = trace(
        vec![cl(1, &[1, 2]), cl(2, &[-1, 3])],
        vec![rs(3, 1, 1, 2)],
        3,
    );
    assert_invalid(&check_proof(&t), 3, "contains");
}

#[test]
fn test_check_proof_with_theory_propagates_resolution_errors() {
    // Even when theory lemmas are valid, resolution errors are still caught.
    let t = trace_with_theories(
        vec![cl(1, &[1])],
        vec![rs(3, 1, 1, 999)], // parent 999 missing
        vec![tl(2, "EUF", &[-1])],
        3,
    );
    let result = check_proof_with_theory(&t);
    assert!(matches!(result.result, CheckResult::Invalid { .. }));
    // Theory lemma was fine, resolution failed
    assert_eq!(result.theory_stats.verified_count, 1);
}

#[test]
fn test_multiple_theory_lemmas_first_invalid_reported() {
    // Two EUF lemmas: first valid, second invalid (empty clause).
    // check_proof_with_theory reports the first invalid.
    let t = trace_with_theories(
        vec![cl(1, &[1])],
        vec![],
        vec![
            tl(10, "EUF", &[-1]),
            tl(11, "EUF", &[]),   // invalid: empty
            tl(12, "LRA", &[-5]), // invalid: single literal
        ],
        1,
    );
    let result = check_proof_with_theory(&t);
    match &result.result {
        CheckResult::Invalid { step, reason } => {
            assert_eq!(*step, 11, "first invalid should be lemma 11");
            assert!(reason.contains("11"), "reason should mention lemma ID");
        }
        CheckResult::Valid => panic!("expected invalid due to empty EUF lemma"),
        _ => panic!("unexpected CheckResult variant"),
    }
}

#[test]
fn test_wide_clause_resolution() {
    // Clauses with many literals, resolving one at a time.
    // cl(1) = {1, 2, 3, 4, 5}
    // cl(2) = {-1, 6, 7}
    // Resolve on 1: {2, 3, 4, 5, 6, 7}
    // cl(3) = {-2, -3, -4, -5, -6, -7}
    // Resolve on 2: {3, 4, 5, 6, 7, -3, -4, -5, -6, -7}
    // Actually, {3} and {-3} are both in the resolvent. BTreeSet will have
    // both. The checker doesn't factor tautologies out — it computes the
    // set union minus the pivot. So the resolvent will have {3, -3, 4, -4, ...}.
    // Let's use a simpler wide scenario:
    // cl(1) = {1, 2, 3, 4, 5}
    // cl(2) = {-1, -2, -3, -4, -5}
    // Resolve on 1: {2, 3, 4, 5, -2, -3, -4, -5} -- non-empty
    // Still not empty. For a real wide proof:
    // cl(1) = {1, 2, 3}
    // cl(2) = {-1}
    // cl(3) = {-2}
    // cl(4) = {-3}
    // Step 10: resolve 1 => {2,3}
    // Step 11: resolve 2 between {2,3} and {-2} => {3}
    // Step 12: resolve 3 between {3} and {-3} => {}
    let t = trace(
        vec![cl(1, &[1, 2, 3]), cl(2, &[-1]), cl(3, &[-2]), cl(4, &[-3])],
        vec![rs(10, 1, 1, 2), rs(11, 2, 10, 3), rs(12, 3, 11, 4)],
        12,
    );
    assert_eq!(check_proof(&t), CheckResult::Valid);
}

#[test]
fn test_check_result_with_stats_fields() {
    // Verify the CheckResultWithStats struct is populated correctly.
    let t = trace_with_theories(
        vec![cl(1, &[1]), cl(2, &[-1])],
        vec![rs(3, 1, 1, 2)],
        vec![],
        3,
    );
    let result: CheckResultWithStats = check_proof_with_theory(&t);
    assert_eq!(result.result, CheckResult::Valid);
    assert_eq!(result.theory_stats.verified_count, 0);
    assert_eq!(result.theory_stats.trusted_count, 0);
    assert_eq!(result.theory_stats.invalid_count, 0);
    assert_eq!(result.theory_stats.total(), 0);
}
