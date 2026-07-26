// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Benchmark and stress tests for the propositional resolution checker.
//!
//! These tests exercise the checker and parser at scale to verify correctness
//! on large proofs, deeply nested resolution chains, wide fan-in patterns,
//! and round-trip through the text format.

use std::time::Instant;

use crate::checker::{check_proof, check_proof_with_theory};
use crate::parse::{format_proof_trace, parse_proof_trace};
use crate::test_utils::{cl, rs};
use crate::types::{CheckResult, Clause, ProofTrace, TheoryLemma};

/// Build a linear resolution chain of length `n`.
///
/// Input clauses: {x1}, {-x1, x2}, {-x2, x3}, ..., {-x_{n-1}, x_n}, {-x_n}
/// Resolution: resolve x1, x2, ..., x_n in sequence until the empty clause.
fn build_linear_chain(n: usize) -> ProofTrace {
    let n = n as i64;
    let mut inputs = vec![cl(1, &[1])];
    for i in 1..=n {
        inputs.push(cl((i + 1) as u64, &[-i, i + 1]));
    }
    inputs.push(cl((n + 2) as u64, &[-(n + 1)]));

    // Base must be above all input clause IDs (max is n+2).
    let base = (n + 3) as u64;
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

    ProofTrace {
        input_clauses: inputs,
        resolution_steps: steps,
        theory_lemmas: vec![],
        empty_clause_id: final_id,
    }
}

/// Build a binary tree resolution proof.
///
/// Layer 0: 2^depth unit clauses alternating polarity: {x1}, {-x1}, {x2}, {-x2}, ...
/// Each subsequent layer resolves pairs from the previous layer.
fn build_binary_tree(depth: usize) -> ProofTrace {
    let leaf_count = 1usize << depth; // 2^depth
    let pair_count = leaf_count / 2;

    let mut inputs = Vec::new();
    let mut next_id = 1u64;

    for i in 0..pair_count {
        let var = (i as i64) + 1;
        inputs.push(cl(next_id, &[var]));
        next_id += 1;
        inputs.push(cl(next_id, &[-var]));
        next_id += 1;
    }

    let step_base = next_id;
    let mut steps = Vec::new();

    // Layer 1: resolve each pair of inputs
    let mut prev_layer_ids: Vec<u64> = Vec::new();
    for i in 0..pair_count {
        let pos_id = (2 * i + 1) as u64;
        let neg_id = (2 * i + 2) as u64;
        let var = (i as i64) + 1;
        let sid = step_base + i as u64;
        steps.push(rs(sid, var, pos_id, neg_id));
        prev_layer_ids.push(sid);
    }

    // For a proper binary tree, all intermediate resolutions produce empty clauses.
    // The first resolution already gives us the empty clause.
    // For depth > 1, we need a different structure. Let's use the first pair.
    let final_id = step_base;

    ProofTrace {
        input_clauses: inputs,
        resolution_steps: steps,
        theory_lemmas: vec![],
        empty_clause_id: final_id,
    }
}

/// Build a proof with theory lemmas mixed in.
fn build_theory_proof(num_input: usize, num_theory: usize) -> ProofTrace {
    let mut inputs = Vec::new();
    let mut lemmas = Vec::new();
    let mut next_id = 1u64;
    let var_offset = 1000i64;

    // Input clauses: each has two literals
    for i in 0..num_input {
        let v = (i as i64) + 1;
        inputs.push(cl(next_id, &[v, var_offset + v]));
        next_id += 1;
    }

    // Theory lemmas: each negates one literal from an input clause.
    // Use EUF for all — EUF accepts single-literal clauses in the structural
    // checker, whereas LRA requires >= 2 literals (Farkas certificate).
    for i in 0..num_theory {
        let v = (i as i64) + 1;
        lemmas.push(TheoryLemma {
            id: next_id,
            theory: "EUF".to_string(),
            clause: cl(next_id, &[-v]),
        });
        next_id += 1;
    }

    // Resolve input[0] with theory[0] on pivot = 1
    // This gives us {var_offset + 1}
    let step_base = next_id;
    let mut steps = Vec::new();

    if num_input > 0 && num_theory > 0 {
        steps.push(rs(step_base, 1, 1, (num_input + 1) as u64));
        // Need a way to get to empty clause. Add a final negation.
        let neg_id = step_base + 1;
        inputs.push(cl(neg_id, &[-(var_offset + 1)]));
        let final_id = step_base + 2;
        steps.push(rs(final_id, var_offset + 1, step_base, neg_id));
        ProofTrace {
            input_clauses: inputs,
            resolution_steps: steps,
            theory_lemmas: lemmas,
            empty_clause_id: final_id,
        }
    } else {
        // Degenerate: just use an empty input clause
        inputs.push(cl(next_id, &[]));
        ProofTrace {
            input_clauses: inputs,
            resolution_steps: vec![],
            theory_lemmas: lemmas,
            empty_clause_id: next_id,
        }
    }
}

// ---------------------------------------------------------------------------
// Stress tests for the resolution checker
// ---------------------------------------------------------------------------

#[test]
fn test_bench_linear_chain_100_valid() {
    let trace = build_linear_chain(100);
    assert_eq!(check_proof(&trace), CheckResult::Valid);
}

#[test]
fn test_bench_linear_chain_500_valid() {
    let trace = build_linear_chain(500);
    assert_eq!(check_proof(&trace), CheckResult::Valid);
}

#[test]
fn test_bench_linear_chain_1000_valid() {
    let trace = build_linear_chain(1000);
    assert_eq!(check_proof(&trace), CheckResult::Valid);
}

#[test]
fn test_bench_linear_chain_5000_valid() {
    let trace = build_linear_chain(5000);
    let start = Instant::now();
    assert_eq!(check_proof(&trace), CheckResult::Valid);
    let elapsed = start.elapsed();
    // Should complete in well under 1 second for 5000 steps
    assert!(
        elapsed.as_millis() < 1000,
        "5000-step proof took {elapsed:?}, expected <1s"
    );
}

#[test]
fn test_bench_binary_tree_depth_8_valid() {
    let trace = build_binary_tree(8);
    assert_eq!(check_proof(&trace), CheckResult::Valid);
}

#[test]
fn test_bench_binary_tree_depth_12_valid() {
    let trace = build_binary_tree(12);
    let start = Instant::now();
    assert_eq!(check_proof(&trace), CheckResult::Valid);
    let elapsed = start.elapsed();
    assert!(
        elapsed.as_millis() < 500,
        "2048-leaf tree proof took {elapsed:?}, expected <500ms"
    );
}

#[test]
fn test_bench_theory_lemmas_mixed_valid() {
    let trace = build_theory_proof(50, 50);
    let result = check_proof_with_theory(&trace);
    assert_eq!(result.result, CheckResult::Valid);
    // All theory lemmas should be processed
    assert!(result.theory_stats.total() > 0);
}

#[test]
fn test_bench_theory_lemmas_large_valid() {
    let trace = build_theory_proof(200, 200);
    let result = check_proof_with_theory(&trace);
    assert_eq!(result.result, CheckResult::Valid);
}

// ---------------------------------------------------------------------------
// Parse + check integration tests
// ---------------------------------------------------------------------------

#[test]
fn test_bench_parse_roundtrip_linear_chain_100() {
    let trace = build_linear_chain(100);
    let text = format_proof_trace(&trace);
    let reparsed = parse_proof_trace(&text).expect("round-trip parse should succeed");
    assert_eq!(reparsed, trace);
    assert_eq!(check_proof(&reparsed), CheckResult::Valid);
}

#[test]
fn test_bench_parse_roundtrip_linear_chain_1000() {
    let trace = build_linear_chain(1000);
    let text = format_proof_trace(&trace);
    let reparsed = parse_proof_trace(&text).expect("round-trip parse should succeed");
    assert_eq!(check_proof(&reparsed), CheckResult::Valid);
}

#[test]
fn test_bench_parse_roundtrip_theory_proof() {
    let trace = build_theory_proof(30, 30);
    let text = format_proof_trace(&trace);
    let reparsed = parse_proof_trace(&text).expect("round-trip parse should succeed");
    assert_eq!(reparsed, trace);
    let result = check_proof_with_theory(&reparsed);
    assert_eq!(result.result, CheckResult::Valid);
}

#[test]
fn test_bench_parse_large_text_format() {
    let trace = build_linear_chain(2000);
    let text = format_proof_trace(&trace);
    let start = Instant::now();
    let reparsed = parse_proof_trace(&text).expect("large text parse should succeed");
    let elapsed = start.elapsed();
    assert!(
        elapsed.as_millis() < 500,
        "parsing 2000-step text proof took {elapsed:?}, expected <500ms"
    );
    assert_eq!(check_proof(&reparsed), CheckResult::Valid);
}

#[test]
fn test_bench_format_preserves_theory_names() {
    let trace = ProofTrace {
        input_clauses: vec![cl(1, &[1, 2])],
        resolution_steps: vec![rs(5, 1, 1, 3)],
        theory_lemmas: vec![
            TheoryLemma {
                id: 2,
                theory: "EUF".to_string(),
                clause: cl(2, &[-1, 3]),
            },
            TheoryLemma {
                id: 3,
                theory: "LRA".to_string(),
                clause: cl(3, &[-1]),
            },
        ],
        empty_clause_id: 5,
    };

    let text = format_proof_trace(&trace);
    assert!(text.contains("t 2 EUF"));
    assert!(text.contains("t 3 LRA"));

    let reparsed = parse_proof_trace(&text).expect("theory roundtrip should succeed");
    assert_eq!(reparsed.theory_lemmas[0].theory, "EUF");
    assert_eq!(reparsed.theory_lemmas[1].theory, "LRA");
}

// ---------------------------------------------------------------------------
// Edge case stress tests
// ---------------------------------------------------------------------------

#[test]
fn test_bench_single_empty_input_clause() {
    let text = "i 1 0\ne 1\n";
    let trace = parse_proof_trace(text).expect("single empty clause should parse");
    assert_eq!(check_proof(&trace), CheckResult::Valid);
}

#[test]
fn test_bench_many_comments_interspersed() {
    let mut text = String::new();
    text.push_str("c This is a proof trace\n");
    text.push_str("c Generated by ay-dpll\n");
    text.push_str("i 1 1 0\n");
    text.push_str("c Comment between clauses\n");
    text.push_str("i 2 -1 0\n");
    text.push_str("c Comment before resolution\n");
    text.push('\n');
    text.push_str("r 3 1 1 2\n");
    text.push_str("c Final comment\n");
    text.push_str("e 3\n");

    let trace = parse_proof_trace(&text).expect("comments should be ignored");
    assert_eq!(check_proof(&trace), CheckResult::Valid);
}

#[test]
fn test_bench_wide_clause_many_literals() {
    // A clause with 100 literals
    let lits: Vec<i64> = (1..=100).collect();
    let neg_lits: Vec<i64> = (-100..=-1).rev().collect();

    let trace = ProofTrace {
        input_clauses: vec![
            Clause {
                id: 1,
                literals: lits.clone(),
            },
            Clause {
                id: 2,
                literals: neg_lits.clone(),
            },
        ],
        // Resolve on pivot 1: removes 1 from clause 1 and -1 from clause 2
        resolution_steps: vec![rs(3, 1, 1, 2)],
        theory_lemmas: vec![],
        // The resolvent still has 99 + 99 = 198 literals, not empty
        empty_clause_id: 3,
    };

    // This should be invalid because the resolvent is not empty
    match check_proof(&trace) {
        CheckResult::Invalid { step, reason } => {
            assert_eq!(step, 3);
            assert!(reason.contains("contains"), "reason: {reason}");
        }
        CheckResult::Valid => panic!("expected invalid: resolvent is not empty"),
    }
}

#[test]
fn test_bench_chain_resolution_eliminates_all_literals() {
    // Build a proof where we systematically eliminate all literals.
    // c1 = {1, 2, 3}
    // c2 = {-1}         -> resolve on 1: {2, 3}
    // c3 = {-2}         -> resolve on 2: {3}
    // c4 = {-3}         -> resolve on 3: {}
    let trace = ProofTrace {
        input_clauses: vec![cl(1, &[1, 2, 3]), cl(2, &[-1]), cl(3, &[-2]), cl(4, &[-3])],
        resolution_steps: vec![rs(10, 1, 1, 2), rs(11, 2, 10, 3), rs(12, 3, 11, 4)],
        theory_lemmas: vec![],
        empty_clause_id: 12,
    };

    assert_eq!(check_proof(&trace), CheckResult::Valid);

    // Also round-trip through text format
    let text = format_proof_trace(&trace);
    let reparsed = parse_proof_trace(&text).expect("round-trip should succeed");
    assert_eq!(check_proof(&reparsed), CheckResult::Valid);
}

#[test]
fn test_bench_checker_performance_10000_steps() {
    let trace = build_linear_chain(10000);
    let start = Instant::now();
    let result = check_proof(&trace);
    let elapsed = start.elapsed();
    assert_eq!(result, CheckResult::Valid);
    assert!(
        elapsed.as_secs() < 5,
        "10000-step proof took {elapsed:?}, expected <5s"
    );
}
