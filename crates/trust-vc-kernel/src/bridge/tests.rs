// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for the ay-dpll proof artifact bridge.

use crate::checker::check_proof;
use crate::types::CheckResult;

use super::{
    convert_ay_artifact, AYClause, AYProofArtifact, AYResolutionStep, AYTheoryKind, AYTheoryLemma,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn aycl(id: u64, lits: &[i64]) -> AYClause {
    AYClause {
        id,
        literals: lits.to_vec(),
    }
}

fn ayrs(result_id: u64, pivot: i64, a: u64, b: u64) -> AYResolutionStep {
    AYResolutionStep {
        result_id,
        pivot,
        antecedent_a: a,
        antecedent_b: b,
        result_literals: None,
    }
}

fn aytl(id: u64, kind: AYTheoryKind, lits: &[i64]) -> AYTheoryLemma {
    AYTheoryLemma {
        id,
        kind,
        literals: lits.to_vec(),
    }
}

// ---------------------------------------------------------------------------
// Roundtrip: build AYProofArtifact -> convert -> check_proof -> Valid
// ---------------------------------------------------------------------------

#[test]
fn test_bridge_simple_two_clause_roundtrip() {
    // {1} and {-1} resolve to empty clause on pivot 1
    let artifact = AYProofArtifact {
        input_clauses: vec![aycl(1, &[1]), aycl(2, &[-1])],
        resolution_steps: vec![ayrs(3, 1, 1, 2)],
        theory_lemmas: vec![],
        empty_clause_id: 3,
    };

    let trace = convert_ay_artifact(&artifact);
    assert_eq!(check_proof(&trace), CheckResult::Valid);
}

#[test]
fn test_bridge_three_step_chain_roundtrip() {
    // Chain: {1}, {-1, 2}, {-2} -> resolve(1,1,2)={2} -> resolve(2,{2},{-2})={}
    let artifact = AYProofArtifact {
        input_clauses: vec![aycl(1, &[1]), aycl(2, &[-1, 2]), aycl(3, &[-2])],
        resolution_steps: vec![ayrs(4, 1, 1, 2), ayrs(5, 2, 4, 3)],
        theory_lemmas: vec![],
        empty_clause_id: 5,
    };

    let trace = convert_ay_artifact(&artifact);
    assert_eq!(check_proof(&trace), CheckResult::Valid);
}

#[test]
fn test_bridge_theory_lemma_roundtrip() {
    // Input: {1}, Theory lemma (EUF): {-1}, resolve to empty
    let artifact = AYProofArtifact {
        input_clauses: vec![aycl(1, &[1])],
        resolution_steps: vec![ayrs(3, 1, 1, 2)],
        theory_lemmas: vec![aytl(2, AYTheoryKind::Euf, &[-1])],
        empty_clause_id: 3,
    };

    let trace = convert_ay_artifact(&artifact);

    // Verify the theory lemma was mapped correctly
    assert_eq!(trace.theory_lemmas.len(), 1);
    assert_eq!(trace.theory_lemmas[0].theory, "EUF");
    assert_eq!(trace.theory_lemmas[0].clause.literals, vec![-1]);

    assert_eq!(check_proof(&trace), CheckResult::Valid);
}

#[test]
fn test_bridge_multiple_theory_kinds() {
    // Use theory lemmas from different solvers, all resolving in a chain
    // Input: {1, 2}, LRA: {-1}, BV: {-2}
    // Step 1: resolve {1, 2} with {-1} on pivot 1 -> {2}
    // Step 2: resolve {2} with {-2} on pivot 2 -> {}
    let artifact = AYProofArtifact {
        input_clauses: vec![aycl(1, &[1, 2])],
        resolution_steps: vec![ayrs(10, 1, 1, 2), ayrs(11, 2, 10, 3)],
        theory_lemmas: vec![
            aytl(2, AYTheoryKind::Lra, &[-1]),
            aytl(3, AYTheoryKind::BitVector, &[-2]),
        ],
        empty_clause_id: 11,
    };

    let trace = convert_ay_artifact(&artifact);
    assert_eq!(trace.theory_lemmas.len(), 2);
    assert_eq!(trace.theory_lemmas[0].theory, "LRA");
    assert_eq!(trace.theory_lemmas[1].theory, "BV");
    assert_eq!(check_proof(&trace), CheckResult::Valid);
}

#[test]
fn test_bridge_empty_input_clause() {
    // An input clause that is already empty is an immediate UNSAT witness
    let artifact = AYProofArtifact {
        input_clauses: vec![aycl(1, &[])],
        resolution_steps: vec![],
        theory_lemmas: vec![],
        empty_clause_id: 1,
    };

    let trace = convert_ay_artifact(&artifact);
    assert_eq!(check_proof(&trace), CheckResult::Valid);
}

#[test]
fn test_bridge_long_resolution_chain() {
    // Build a 50-step chain: {1}, {-1,2}, {-2,3}, ..., {-50,51}, {-51}
    let n: i64 = 50;
    let mut inputs = vec![aycl(1, &[1])];
    for i in 1..=n {
        inputs.push(aycl((i + 1) as u64, &[-i, i + 1]));
    }
    inputs.push(aycl((n + 2) as u64, &[-(n + 1)]));

    let base = 100u64;
    let mut steps = vec![ayrs(base, 1, 1, 2)];
    for i in 2..=n {
        steps.push(ayrs(
            base + (i - 1) as u64,
            i,
            base + (i - 2) as u64,
            (i + 1) as u64,
        ));
    }
    let final_id = base + n as u64;
    steps.push(ayrs(final_id, n + 1, final_id - 1, (n + 2) as u64));

    let artifact = AYProofArtifact {
        input_clauses: inputs,
        resolution_steps: steps,
        theory_lemmas: vec![],
        empty_clause_id: final_id,
    };

    let trace = convert_ay_artifact(&artifact);
    assert_eq!(check_proof(&trace), CheckResult::Valid);
}

#[test]
fn test_bridge_reversed_polarity_roundtrip() {
    // Pivot present in reverse polarity: {-1} and {1} -> empty
    let artifact = AYProofArtifact {
        input_clauses: vec![aycl(1, &[-1]), aycl(2, &[1])],
        resolution_steps: vec![ayrs(3, 1, 1, 2)],
        theory_lemmas: vec![],
        empty_clause_id: 3,
    };

    let trace = convert_ay_artifact(&artifact);
    assert_eq!(check_proof(&trace), CheckResult::Valid);
}

#[test]
fn test_bridge_invalid_missing_parent_detected() {
    // Resolution step references a non-existent clause
    let artifact = AYProofArtifact {
        input_clauses: vec![aycl(1, &[1])],
        resolution_steps: vec![ayrs(3, 1, 1, 99)],
        theory_lemmas: vec![],
        empty_clause_id: 3,
    };

    let trace = convert_ay_artifact(&artifact);
    match check_proof(&trace) {
        CheckResult::Invalid { step, reason } => {
            assert_eq!(step, 3);
            assert!(
                reason.contains("unknown clause"),
                "expected 'unknown clause' in: {reason}"
            );
        }
        CheckResult::Valid => panic!("expected invalid proof, got valid"),
    }
}

#[test]
fn test_bridge_invalid_nonempty_final_clause_detected() {
    // Resolution produces a non-empty clause but claims it is the empty clause
    // {1, 2} and {-1, 3} resolve on pivot 1 -> {2, 3} (not empty)
    let artifact = AYProofArtifact {
        input_clauses: vec![aycl(1, &[1, 2]), aycl(2, &[-1, 3])],
        resolution_steps: vec![ayrs(3, 1, 1, 2)],
        theory_lemmas: vec![],
        empty_clause_id: 3,
    };

    let trace = convert_ay_artifact(&artifact);
    match check_proof(&trace) {
        CheckResult::Invalid { step, reason } => {
            assert_eq!(step, 3);
            assert!(
                reason.contains("contains"),
                "expected 'contains' in: {reason}"
            );
        }
        CheckResult::Valid => panic!("expected invalid proof, got valid"),
    }
}

#[test]
fn test_bridge_preserves_clause_id_mapping() {
    // Verify that clause IDs map 1:1 from artifact to trace
    let artifact = AYProofArtifact {
        input_clauses: vec![aycl(42, &[1]), aycl(43, &[-1])],
        resolution_steps: vec![ayrs(100, 1, 42, 43)],
        theory_lemmas: vec![],
        empty_clause_id: 100,
    };

    let trace = convert_ay_artifact(&artifact);

    assert_eq!(trace.input_clauses[0].id, 42);
    assert_eq!(trace.input_clauses[1].id, 43);
    assert_eq!(trace.resolution_steps[0].id, 100);
    assert_eq!(trace.resolution_steps[0].parent1, 42);
    assert_eq!(trace.resolution_steps[0].parent2, 43);
    assert_eq!(trace.empty_clause_id, 100);
    assert_eq!(check_proof(&trace), CheckResult::Valid);
}

#[test]
fn test_bridge_preserves_resolution_result_literals() {
    let artifact = AYProofArtifact {
        input_clauses: vec![aycl(1, &[1]), aycl(2, &[-1, 2])],
        resolution_steps: vec![AYResolutionStep {
            result_id: 3,
            pivot: 1,
            antecedent_a: 1,
            antecedent_b: 2,
            result_literals: Some(vec![2]),
        }],
        theory_lemmas: vec![],
        empty_clause_id: 3,
    };

    let trace = convert_ay_artifact(&artifact);
    assert_eq!(trace.resolution_steps[0].result_literals, Some(vec![2]));
    assert_eq!(
        check_proof(&trace),
        CheckResult::Invalid {
            step: 3,
            reason: "clause 3 designated as empty but contains 1 literal(s)".to_string()
        }
    );
}

#[test]
fn test_bridge_preserves_literal_values() {
    // Verify literal values are preserved exactly through conversion
    let artifact = AYProofArtifact {
        input_clauses: vec![aycl(1, &[100, -200, 300]), aycl(2, &[-100])],
        resolution_steps: vec![],
        theory_lemmas: vec![],
        empty_clause_id: 1, // not actually valid but we test structure, not proof
    };

    let trace = convert_ay_artifact(&artifact);
    assert_eq!(trace.input_clauses[0].literals, vec![100, -200, 300]);
    assert_eq!(trace.input_clauses[1].literals, vec![-100]);
}

#[test]
fn test_bridge_all_theory_kinds_label_correctly() {
    let kinds = [
        (AYTheoryKind::Euf, "EUF"),
        (AYTheoryKind::Lra, "LRA"),
        (AYTheoryKind::Nia, "NIA"),
        (AYTheoryKind::BitVector, "BV"),
        (AYTheoryKind::Array, "Array"),
        (AYTheoryKind::Sequence, "Seq"),
        (AYTheoryKind::Other, "Other"),
    ];

    for (i, (kind, expected_label)) in kinds.iter().enumerate() {
        let artifact = AYProofArtifact {
            input_clauses: vec![],
            resolution_steps: vec![],
            theory_lemmas: vec![aytl(i as u64 + 1, *kind, &[1])],
            empty_clause_id: 0,
        };

        let trace = convert_ay_artifact(&artifact);
        assert_eq!(
            trace.theory_lemmas[0].theory, *expected_label,
            "AYTheoryKind::{kind:?} should map to {expected_label}"
        );
    }
}

#[test]
fn test_bridge_mixed_input_theory_resolution_roundtrip() {
    // Complex proof: input + theory lemmas + multi-step resolution -> empty clause
    //
    // Inputs: {1, 2}, {3}
    // Theory (Array): {-1}
    // Theory (NIA): {-3, -2}
    //
    // Step 1: resolve {1, 2} with {-1} on pivot 1 -> {2}      (id=10)
    // Step 2: resolve {3} with {-3, -2} on pivot 3 -> {-2}    (id=11)
    // Step 3: resolve {2} with {-2} on pivot 2 -> {}           (id=12)
    let artifact = AYProofArtifact {
        input_clauses: vec![aycl(1, &[1, 2]), aycl(2, &[3])],
        resolution_steps: vec![ayrs(10, 1, 1, 3), ayrs(11, 3, 2, 4), ayrs(12, 2, 10, 11)],
        theory_lemmas: vec![
            aytl(3, AYTheoryKind::Array, &[-1]),
            aytl(4, AYTheoryKind::Nia, &[-3, -2]),
        ],
        empty_clause_id: 12,
    };

    let trace = convert_ay_artifact(&artifact);
    assert_eq!(trace.input_clauses.len(), 2);
    assert_eq!(trace.theory_lemmas.len(), 2);
    assert_eq!(trace.resolution_steps.len(), 3);
    assert_eq!(check_proof(&trace), CheckResult::Valid);
}
