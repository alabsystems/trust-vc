// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for theory lemma verification.

use crate::types::{Clause, TheoryCheckResult, TheoryLemma, TheoryStats};

use super::{check_all_theory_lemmas, check_euf_lemma, check_lra_lemma, check_theory_lemma};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn euf_lemma(id: u64, lits: &[i64]) -> TheoryLemma {
    TheoryLemma {
        id,
        theory: "EUF".to_string(),
        clause: Clause {
            id,
            literals: lits.to_vec(),
        },
    }
}

fn lra_lemma(id: u64, lits: &[i64]) -> TheoryLemma {
    TheoryLemma {
        id,
        theory: "LRA".to_string(),
        clause: Clause {
            id,
            literals: lits.to_vec(),
        },
    }
}

fn theory_lemma(id: u64, theory: &str, lits: &[i64]) -> TheoryLemma {
    TheoryLemma {
        id,
        theory: theory.to_string(),
        clause: Clause {
            id,
            literals: lits.to_vec(),
        },
    }
}

// ---------------------------------------------------------------------------
// EUF: Valid cases
// ---------------------------------------------------------------------------

#[test]
fn test_euf_transitivity_two_negatives_one_positive() {
    // a=b, b=c => a=c encoded as: (-1, -2, 3)
    // meaning: (a!=b) \/ (b!=c) \/ (a=c)
    let result = check_euf_lemma(&[-1, -2, 3]);
    assert_eq!(result, TheoryCheckResult::Verified);
}

#[test]
fn test_euf_congruence_single_premise() {
    // a=b => f(a)=f(b) encoded as: (-1, 2)
    // meaning: (a!=b) \/ (f(a)=f(b))
    let result = check_euf_lemma(&[-1, 2]);
    assert_eq!(result, TheoryCheckResult::Verified);
}

#[test]
fn test_euf_pure_disequality_clause() {
    // All negative: conflict clause stating these equalities are incompatible
    // (a!=b) \/ (c!=d) \/ (e!=f)
    let result = check_euf_lemma(&[-1, -2, -3]);
    assert_eq!(result, TheoryCheckResult::Verified);
}

#[test]
fn test_euf_single_negative_literal() {
    // Single disequality: a!=b (trivially valid EUF lemma)
    let result = check_euf_lemma(&[-5]);
    assert_eq!(result, TheoryCheckResult::Verified);
}

#[test]
fn test_euf_single_positive_literal() {
    // Single equality: a=b (valid, though unusual)
    let result = check_euf_lemma(&[7]);
    assert_eq!(result, TheoryCheckResult::Verified);
}

#[test]
fn test_euf_long_transitivity_chain() {
    // a=b, b=c, c=d, d=e => a=e
    // (-1, -2, -3, -4, 5)
    let result = check_euf_lemma(&[-1, -2, -3, -4, 5]);
    assert_eq!(result, TheoryCheckResult::Verified);
}

// ---------------------------------------------------------------------------
// EUF: Invalid cases
// ---------------------------------------------------------------------------

#[test]
fn test_euf_empty_clause_invalid() {
    let result = check_euf_lemma(&[]);
    assert!(matches!(result, TheoryCheckResult::Invalid { .. }));
    if let TheoryCheckResult::Invalid { reason } = result {
        assert!(reason.contains("no literals"));
    }
}

#[test]
fn test_euf_duplicate_literal_invalid() {
    let result = check_euf_lemma(&[-1, -2, -1, 3]);
    assert!(matches!(result, TheoryCheckResult::Invalid { .. }));
    if let TheoryCheckResult::Invalid { reason } = result {
        assert!(reason.contains("duplicate"));
    }
}

#[test]
fn test_euf_tautology_invalid() {
    // Contains both 2 and -2
    let result = check_euf_lemma(&[-1, 2, -2, 3]);
    assert!(matches!(result, TheoryCheckResult::Invalid { .. }));
    if let TheoryCheckResult::Invalid { reason } = result {
        assert!(reason.contains("tautology"));
    }
}

#[test]
fn test_euf_multiple_positive_literals_invalid() {
    // Two positive literals: (a=b) \/ (c=d) -- not a valid EUF conclusion
    let result = check_euf_lemma(&[1, 2]);
    assert!(matches!(result, TheoryCheckResult::Invalid { .. }));
    if let TheoryCheckResult::Invalid { reason } = result {
        assert!(reason.contains("positive literals"));
    }
}

#[test]
fn test_euf_three_positive_literals_invalid() {
    let result = check_euf_lemma(&[1, 2, 3]);
    assert!(matches!(result, TheoryCheckResult::Invalid { .. }));
    if let TheoryCheckResult::Invalid { reason } = result {
        assert!(reason.contains("3 positive literals"));
    }
}

// ---------------------------------------------------------------------------
// LRA: Valid cases
// ---------------------------------------------------------------------------

#[test]
fn test_lra_farkas_two_literals() {
    // Minimal Farkas certificate: two constraints are contradictory
    // e.g., x>=0 AND x<0 encoded as (-1, -2)
    let result = check_lra_lemma(&[-1, -2]);
    assert_eq!(result, TheoryCheckResult::Verified);
}

#[test]
fn test_lra_farkas_three_literals() {
    // x>=0, y>=0, x+y<0 is contradictory: (-1, -2, -3)
    let result = check_lra_lemma(&[-1, -2, -3]);
    assert_eq!(result, TheoryCheckResult::Verified);
}

#[test]
fn test_lra_mixed_polarity() {
    // Valid LRA lemma with mixed positive/negative literals
    let result = check_lra_lemma(&[1, -2, 3, -4]);
    assert_eq!(result, TheoryCheckResult::Verified);
}

#[test]
fn test_lra_large_clause() {
    // Large Farkas certificate with many constraints
    let lits: Vec<i64> = (1..=20).map(|i| if i % 2 == 0 { i } else { -i }).collect();
    let result = check_lra_lemma(&lits);
    assert_eq!(result, TheoryCheckResult::Verified);
}

// ---------------------------------------------------------------------------
// LRA: Invalid cases
// ---------------------------------------------------------------------------

#[test]
fn test_lra_empty_clause_invalid() {
    let result = check_lra_lemma(&[]);
    assert!(matches!(result, TheoryCheckResult::Invalid { .. }));
    if let TheoryCheckResult::Invalid { reason } = result {
        assert!(reason.contains("no literals"));
    }
}

#[test]
fn test_lra_single_literal_invalid() {
    // Farkas needs at least 2 constraints
    let result = check_lra_lemma(&[-1]);
    assert!(matches!(result, TheoryCheckResult::Invalid { .. }));
    if let TheoryCheckResult::Invalid { reason } = result {
        assert!(reason.contains("at least 2"));
    }
}

#[test]
fn test_lra_duplicate_literal_invalid() {
    let result = check_lra_lemma(&[-1, -2, -1]);
    assert!(matches!(result, TheoryCheckResult::Invalid { .. }));
    if let TheoryCheckResult::Invalid { reason } = result {
        assert!(reason.contains("duplicate"));
    }
}

#[test]
fn test_lra_tautology_invalid() {
    let result = check_lra_lemma(&[-1, 1, -3]);
    assert!(matches!(result, TheoryCheckResult::Invalid { .. }));
    if let TheoryCheckResult::Invalid { reason } = result {
        assert!(reason.contains("tautology"));
    }
}

// ---------------------------------------------------------------------------
// Trusted fallback for unknown theories
// ---------------------------------------------------------------------------

#[test]
fn test_nia_returns_trusted() {
    let lemma = theory_lemma(1, "NIA", &[-1, -2, 3]);
    assert_eq!(check_theory_lemma(&lemma), TheoryCheckResult::Trusted);
}

#[test]
fn test_bv_returns_trusted() {
    let lemma = theory_lemma(1, "BV", &[-1, 2]);
    assert_eq!(check_theory_lemma(&lemma), TheoryCheckResult::Trusted);
}

#[test]
fn test_array_returns_trusted() {
    let lemma = theory_lemma(1, "Array", &[-1, -2]);
    assert_eq!(check_theory_lemma(&lemma), TheoryCheckResult::Trusted);
}

#[test]
fn test_seq_returns_trusted() {
    let lemma = theory_lemma(1, "Seq", &[-1, 2, -3]);
    assert_eq!(check_theory_lemma(&lemma), TheoryCheckResult::Trusted);
}

#[test]
fn test_other_returns_trusted() {
    let lemma = theory_lemma(1, "Other", &[1]);
    assert_eq!(check_theory_lemma(&lemma), TheoryCheckResult::Trusted);
}

#[test]
fn test_unknown_theory_returns_trusted() {
    let lemma = theory_lemma(1, "CustomTheory", &[1, -2]);
    assert_eq!(check_theory_lemma(&lemma), TheoryCheckResult::Trusted);
}

// ---------------------------------------------------------------------------
// Dispatcher integration
// ---------------------------------------------------------------------------

#[test]
fn test_dispatcher_routes_euf_correctly() {
    let lemma = euf_lemma(1, &[-1, -2, 3]);
    assert_eq!(check_theory_lemma(&lemma), TheoryCheckResult::Verified);
}

#[test]
fn test_dispatcher_routes_lra_correctly() {
    let lemma = lra_lemma(1, &[-1, -2]);
    assert_eq!(check_theory_lemma(&lemma), TheoryCheckResult::Verified);
}

#[test]
fn test_dispatcher_detects_invalid_euf() {
    let lemma = euf_lemma(1, &[]);
    assert!(matches!(
        check_theory_lemma(&lemma),
        TheoryCheckResult::Invalid { .. }
    ));
}

#[test]
fn test_dispatcher_detects_invalid_lra() {
    let lemma = lra_lemma(1, &[-1]);
    assert!(matches!(
        check_theory_lemma(&lemma),
        TheoryCheckResult::Invalid { .. }
    ));
}

// ---------------------------------------------------------------------------
// Batch checking (check_all_theory_lemmas)
// ---------------------------------------------------------------------------

#[test]
fn test_batch_all_verified() {
    let lemmas = vec![euf_lemma(1, &[-1, -2, 3]), euf_lemma(2, &[-4, 5])];
    let (stats, first_invalid) = check_all_theory_lemmas(&lemmas);
    assert_eq!(stats.verified_count, 2);
    assert_eq!(stats.trusted_count, 0);
    assert_eq!(stats.invalid_count, 0);
    assert!(first_invalid.is_none());
}

#[test]
fn test_batch_all_trusted() {
    let lemmas = vec![
        theory_lemma(1, "NIA", &[-1, 2]),
        theory_lemma(2, "BV", &[3, -4]),
        theory_lemma(3, "Array", &[-5]),
    ];
    let (stats, first_invalid) = check_all_theory_lemmas(&lemmas);
    assert_eq!(stats.verified_count, 0);
    assert_eq!(stats.trusted_count, 3);
    assert_eq!(stats.invalid_count, 0);
    assert!(first_invalid.is_none());
}

#[test]
fn test_batch_mixed_results() {
    let lemmas = vec![
        euf_lemma(1, &[-1, -2, 3]),       // Verified
        theory_lemma(2, "NIA", &[-1, 2]), // Trusted
        lra_lemma(3, &[-1, -2]),          // Verified
        theory_lemma(4, "BV", &[1]),      // Trusted
    ];
    let (stats, first_invalid) = check_all_theory_lemmas(&lemmas);
    assert_eq!(stats.verified_count, 2);
    assert_eq!(stats.trusted_count, 2);
    assert_eq!(stats.invalid_count, 0);
    assert!(first_invalid.is_none());
}

#[test]
fn test_batch_with_invalid_captures_first() {
    let lemmas = vec![
        euf_lemma(10, &[-1, -2, 3]), // Verified
        euf_lemma(20, &[]),          // Invalid (empty)
        lra_lemma(30, &[-1]),        // Invalid (single lit)
    ];
    let (stats, first_invalid) = check_all_theory_lemmas(&lemmas);
    assert_eq!(stats.verified_count, 1);
    assert_eq!(stats.trusted_count, 0);
    assert_eq!(stats.invalid_count, 2);
    // First invalid should be lemma 20
    let (id, result) = first_invalid.expect("should have an invalid result");
    assert_eq!(id, 20);
    assert!(matches!(result, TheoryCheckResult::Invalid { .. }));
}

#[test]
fn test_batch_empty_lemma_list() {
    let (stats, first_invalid) = check_all_theory_lemmas(&[]);
    assert_eq!(stats, TheoryStats::default());
    assert!(first_invalid.is_none());
}

// ---------------------------------------------------------------------------
// TheoryStats
// ---------------------------------------------------------------------------

#[test]
fn test_theory_stats_total() {
    let stats = TheoryStats {
        verified_count: 5,
        trusted_count: 3,
        invalid_count: 1,
    };
    assert_eq!(stats.total(), 9);
}

#[test]
fn test_theory_stats_default_all_zeros() {
    let stats = TheoryStats::default();
    assert_eq!(stats.verified_count, 0);
    assert_eq!(stats.trusted_count, 0);
    assert_eq!(stats.invalid_count, 0);
    assert_eq!(stats.total(), 0);
}

// ---------------------------------------------------------------------------
// Integration: check_proof_with_theory
// ---------------------------------------------------------------------------

#[test]
fn test_check_proof_with_theory_valid_euf_lemma() {
    use crate::checker::check_proof_with_theory;
    use crate::types::{CheckResult, Clause, ProofTrace, ResolutionStep};

    let trace = ProofTrace {
        input_clauses: vec![Clause {
            id: 1,
            literals: vec![1],
        }],
        resolution_steps: vec![ResolutionStep {
            id: 3,
            pivot: 1,
            parent1: 1,
            parent2: 2,
            result_literals: None,
        }],
        theory_lemmas: vec![TheoryLemma {
            id: 2,
            theory: "EUF".to_string(),
            clause: Clause {
                id: 2,
                literals: vec![-1],
            },
        }],
        empty_clause_id: 3,
    };

    let result = check_proof_with_theory(&trace);
    assert_eq!(result.result, CheckResult::Valid);
    assert_eq!(result.theory_stats.verified_count, 1);
    assert_eq!(result.theory_stats.trusted_count, 0);
    assert_eq!(result.theory_stats.invalid_count, 0);
}

#[test]
fn test_check_proof_with_theory_invalid_euf_lemma() {
    use crate::checker::check_proof_with_theory;
    use crate::types::{CheckResult, Clause, ProofTrace, ResolutionStep};

    let trace = ProofTrace {
        input_clauses: vec![Clause {
            id: 1,
            literals: vec![1],
        }],
        resolution_steps: vec![ResolutionStep {
            id: 3,
            pivot: 1,
            parent1: 1,
            parent2: 2,
            result_literals: None,
        }],
        // Empty EUF lemma: structurally invalid
        theory_lemmas: vec![TheoryLemma {
            id: 2,
            theory: "EUF".to_string(),
            clause: Clause {
                id: 2,
                literals: vec![],
            },
        }],
        empty_clause_id: 3,
    };

    let result = check_proof_with_theory(&trace);
    assert!(matches!(result.result, CheckResult::Invalid { .. }));
    assert_eq!(result.theory_stats.invalid_count, 1);
}

#[test]
fn test_check_proof_with_theory_trusted_lemma_stats() {
    use crate::checker::check_proof_with_theory;
    use crate::types::{CheckResult, Clause, ProofTrace, ResolutionStep};

    let trace = ProofTrace {
        input_clauses: vec![Clause {
            id: 1,
            literals: vec![1],
        }],
        resolution_steps: vec![ResolutionStep {
            id: 3,
            pivot: 1,
            parent1: 1,
            parent2: 2,
            result_literals: None,
        }],
        theory_lemmas: vec![TheoryLemma {
            id: 2,
            theory: "BV".to_string(),
            clause: Clause {
                id: 2,
                literals: vec![-1],
            },
        }],
        empty_clause_id: 3,
    };

    let result = check_proof_with_theory(&trace);
    assert_eq!(result.result, CheckResult::Valid);
    assert_eq!(result.theory_stats.verified_count, 0);
    assert_eq!(result.theory_stats.trusted_count, 1);
    assert_eq!(result.theory_stats.invalid_count, 0);
}

#[test]
fn test_check_proof_with_theory_no_lemmas() {
    use crate::checker::check_proof_with_theory;
    use crate::types::{CheckResult, Clause, ProofTrace, ResolutionStep};

    let trace = ProofTrace {
        input_clauses: vec![
            Clause {
                id: 1,
                literals: vec![1],
            },
            Clause {
                id: 2,
                literals: vec![-1],
            },
        ],
        resolution_steps: vec![ResolutionStep {
            id: 3,
            pivot: 1,
            parent1: 1,
            parent2: 2,
            result_literals: None,
        }],
        theory_lemmas: vec![],
        empty_clause_id: 3,
    };

    let result = check_proof_with_theory(&trace);
    assert_eq!(result.result, CheckResult::Valid);
    assert_eq!(result.theory_stats.total(), 0);
}

// ---------------------------------------------------------------------------
// EUF: Extended structural validation
// ---------------------------------------------------------------------------

#[test]
fn test_euf_congruence_multi_arg_conclusion() {
    // Multi-argument congruence: a=b, c=d => f(a,c)=f(b,d)
    // Encoded as: (a!=b) \/ (c!=d) \/ (f(a,c)=f(b,d))
    // Two negative premises, one positive conclusion -- valid EUF lemma.
    let result = check_euf_lemma(&[-10, -20, 30]);
    assert_eq!(result, TheoryCheckResult::Verified);
}

#[test]
fn test_euf_tautology_at_clause_boundaries() {
    // Complementary pair at first and last positions in the clause.
    // The checker must scan all pairs, not just adjacent ones.
    let result = check_euf_lemma(&[5, -3, -5]);
    assert!(matches!(result, TheoryCheckResult::Invalid { .. }));
    if let TheoryCheckResult::Invalid { reason } = result {
        assert!(
            reason.contains("tautology"),
            "Expected tautology error, got: {reason}"
        );
    }
}

#[test]
fn test_euf_exactly_one_positive_among_many_negatives() {
    // Boundary for Rule 4: exactly 1 positive literal among 9 negatives.
    // This is the maximum-negative-count form of a valid EUF transitivity chain.
    let result = check_euf_lemma(&[-1, -2, -3, -4, -5, -6, -7, -8, -9, 10]);
    assert_eq!(result, TheoryCheckResult::Verified);
}

// ---------------------------------------------------------------------------
// LRA: Extended structural validation
// ---------------------------------------------------------------------------

#[test]
fn test_lra_single_positive_literal_invalid() {
    // A single positive literal is still only 1 literal -- Farkas needs >= 2.
    let result = check_lra_lemma(&[42]);
    assert!(matches!(result, TheoryCheckResult::Invalid { .. }));
    if let TheoryCheckResult::Invalid { reason } = result {
        assert!(
            reason.contains("at least 2"),
            "Expected 'at least 2' in reason, got: {reason}"
        );
    }
}

#[test]
fn test_lra_duplicate_positive_literal_invalid() {
    // Duplicate detection works for positive literals too, not just negative.
    let result = check_lra_lemma(&[3, -4, 3]);
    assert!(matches!(result, TheoryCheckResult::Invalid { .. }));
    if let TheoryCheckResult::Invalid { reason } = result {
        assert!(
            reason.contains("duplicate"),
            "Expected duplicate error, got: {reason}"
        );
    }
}

// ---------------------------------------------------------------------------
// Dispatcher: case sensitivity and boundary behavior
// ---------------------------------------------------------------------------

#[test]
fn test_dispatcher_theory_name_is_case_sensitive() {
    // "euf" (lowercase) should NOT be dispatched to the EUF checker.
    // It should fall through to the Trusted path because theory dispatch
    // matches on the exact string "EUF".
    let lemma = theory_lemma(1, "euf", &[1, 2, 3]);
    // [1, 2, 3] has 3 positive literals which would be Invalid under EUF.
    // But since "euf" != "EUF", the dispatcher should return Trusted.
    assert_eq!(check_theory_lemma(&lemma), TheoryCheckResult::Trusted);
}

#[test]
fn test_dispatcher_lra_case_sensitive_fallthrough() {
    // "lra" (lowercase) should NOT route to the LRA checker.
    // A single-literal clause would be Invalid under LRA but Trusted here.
    let lemma = theory_lemma(1, "lra", &[1]);
    assert_eq!(check_theory_lemma(&lemma), TheoryCheckResult::Trusted);
}

// ---------------------------------------------------------------------------
// Batch: all-invalid and ordering guarantees
// ---------------------------------------------------------------------------

#[test]
fn test_batch_all_invalid_captures_first_by_order() {
    // When every lemma is invalid, check_all_theory_lemmas should capture
    // the ID of the *first* invalid lemma in iteration order.
    let lemmas = vec![
        euf_lemma(100, &[]),        // Invalid: empty clause
        lra_lemma(200, &[-5]),      // Invalid: single literal
        euf_lemma(300, &[1, 2, 3]), // Invalid: 3 positive literals
    ];
    let (stats, first_invalid) = check_all_theory_lemmas(&lemmas);
    assert_eq!(stats.verified_count, 0);
    assert_eq!(stats.trusted_count, 0);
    assert_eq!(stats.invalid_count, 3);
    let (id, result) = first_invalid.expect("should have an invalid result");
    assert_eq!(
        id, 100,
        "first invalid should be lemma 100 (first in order)"
    );
    assert!(matches!(result, TheoryCheckResult::Invalid { .. }));
}
