// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::checker::check_proof;
use crate::test_utils::{cl, rs, trace};
use crate::types::{CheckResult, ProofTrace, ResolutionStep, TheoryLemma};

fn assert_invalid(result: &CheckResult, expected_step: u64, substr: &str) {
    match result {
        CheckResult::Invalid { step, reason } => {
            assert_eq!(*step, expected_step);
            assert!(reason.contains(substr), "expected '{substr}' in: {reason}");
        }
        CheckResult::Valid => panic!("expected invalid, got valid"),
    }
}

#[test]
fn test_checker_simple_two_clause_proof_valid() {
    let t = trace(vec![cl(1, &[1]), cl(2, &[-1])], vec![rs(3, 1, 1, 2)], 3);
    assert_eq!(check_proof(&t), CheckResult::Valid);
}

#[test]
fn test_checker_three_step_chain_valid() {
    let t = trace(
        vec![cl(1, &[1]), cl(2, &[-1, 2]), cl(3, &[-2])],
        vec![rs(4, 1, 1, 2), rs(5, 2, 4, 3)],
        5,
    );
    assert_eq!(check_proof(&t), CheckResult::Valid);
}

#[test]
fn test_checker_missing_parent_clause_invalid() {
    let t = trace(vec![cl(1, &[1])], vec![rs(3, 1, 1, 99)], 3);
    assert_invalid(&check_proof(&t), 3, "unknown clause");
}

#[test]
fn test_checker_wrong_resolvent_invalid() {
    // pivot=2 but parent2 has neither 2 nor -2
    let t = trace(
        vec![cl(1, &[1, 2]), cl(2, &[-1, 3])],
        vec![rs(3, 2, 1, 2)],
        3,
    );
    assert_invalid(&check_proof(&t), 3, "pivot");
}

#[test]
fn test_checker_final_clause_not_empty_invalid() {
    let t = trace(
        vec![cl(1, &[1, 2]), cl(2, &[-1, 3])],
        vec![rs(3, 1, 1, 2)],
        3,
    );
    assert_invalid(&check_proof(&t), 3, "contains");
}

#[test]
fn test_checker_pivot_not_in_parents_invalid() {
    let t = trace(vec![cl(1, &[1]), cl(2, &[-2])], vec![rs(3, 3, 1, 2)], 3);
    assert_invalid(&check_proof(&t), 3, "pivot");
}

#[test]
fn test_checker_empty_input_clause_valid() {
    let t = trace(vec![cl(1, &[])], vec![], 1);
    assert_eq!(check_proof(&t), CheckResult::Valid);
}

#[test]
fn test_checker_theory_lemma_used_correctly_valid() {
    let t = ProofTrace {
        input_clauses: vec![cl(1, &[1])],
        resolution_steps: vec![rs(3, 1, 1, 2)],
        theory_lemmas: vec![TheoryLemma {
            id: 2,
            theory: "EUF".into(),
            clause: cl(2, &[-1]),
        }],
        empty_clause_id: 3,
    };
    assert_eq!(check_proof(&t), CheckResult::Valid);
}

#[test]
fn test_checker_large_proof_chain_valid() {
    let n: i64 = 50;
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
fn test_checker_duplicate_clause_ids_invalid() {
    let t = trace(vec![cl(1, &[1]), cl(1, &[-1])], vec![rs(2, 1, 1, 1)], 2);
    assert_invalid(&check_proof(&t), 1, "duplicate");
}

#[test]
fn test_checker_empty_clause_id_not_found_invalid() {
    let t = trace(vec![cl(1, &[1]), cl(2, &[-1])], vec![rs(3, 1, 1, 2)], 999);
    assert_invalid(&check_proof(&t), 999, "not found");
}

#[test]
fn test_checker_duplicate_id_across_sources_invalid() {
    let t = ProofTrace {
        input_clauses: vec![cl(1, &[1])],
        resolution_steps: vec![],
        theory_lemmas: vec![TheoryLemma {
            id: 1,
            theory: "LRA".into(),
            clause: cl(1, &[-1]),
        }],
        empty_clause_id: 1,
    };
    assert_invalid(&check_proof(&t), 1, "duplicate");
}

#[test]
fn test_checker_reversed_polarity_valid() {
    let t = trace(vec![cl(1, &[-1]), cl(2, &[1])], vec![rs(3, 1, 1, 2)], 3);
    assert_eq!(check_proof(&t), CheckResult::Valid);
}

#[test]
fn test_checker_declared_resolvent_mismatch_invalid() {
    let t = ProofTrace {
        input_clauses: vec![cl(1, &[1]), cl(2, &[-1])],
        resolution_steps: vec![ResolutionStep {
            id: 3,
            pivot: 1,
            parent1: 1,
            parent2: 2,
            result_literals: Some(vec![2]),
        }],
        theory_lemmas: vec![],
        empty_clause_id: 3,
    };
    assert_invalid(&check_proof(&t), 3, "declared resolvent");
}
