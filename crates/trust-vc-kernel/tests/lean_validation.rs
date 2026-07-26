// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Integration tests for Lean5 export and offline syntax validation.
//!
//! These tests exercise the `export_lean5` -> `validate_lean_syntax` pipeline
//! across a variety of proof trace shapes: simple resolution, chains, theory
//! lemmas, mixed proofs, edge cases, and large traces.

use trust_vc_kernel::{
    export_lean5, is_valid_lean_ident, validate_lean_syntax, Clause, LeanExportError, ProofTrace,
    ResolutionStep, SyntaxError, TheoryLemma,
};

// ---------------------------------------------------------------------------
// Test helpers
// ---------------------------------------------------------------------------

fn cl(id: u64, lits: &[i64]) -> Clause {
    Clause {
        id,
        literals: lits.to_vec(),
    }
}

fn rs(id: u64, pivot: i64, p1: u64, p2: u64) -> ResolutionStep {
    ResolutionStep {
        id,
        pivot,
        parent1: p1,
        parent2: p2,
        result_literals: None,
    }
}

fn trace(inputs: Vec<Clause>, steps: Vec<ResolutionStep>, empty: u64) -> ProofTrace {
    ProofTrace {
        input_clauses: inputs,
        resolution_steps: steps,
        theory_lemmas: vec![],
        empty_clause_id: empty,
    }
}

/// Export and validate in one step, panicking on any error.
fn export_and_validate(t: &ProofTrace) -> String {
    let lean = export_lean5(t).expect("export_lean5 should succeed");
    if let Err(errs) = validate_lean_syntax(&lean) {
        let msgs: Vec<String> = errs.iter().map(|e| e.to_string()).collect();
        panic!(
            "validate_lean_syntax found {} error(s):\n{}",
            msgs.len(),
            msgs.join("\n")
        );
    }
    lean
}

// ---------------------------------------------------------------------------
// 1. Simple 2-clause resolution
// ---------------------------------------------------------------------------

#[test]
fn test_lean_validation_simple_two_clause_resolution() {
    let t = trace(vec![cl(1, &[1]), cl(2, &[-1])], vec![rs(3, 1, 1, 2)], 3);
    let lean = export_and_validate(&t);

    assert!(lean.contains("def clause_1 : Clause"));
    assert!(lean.contains("def clause_2 : Clause"));
    assert!(lean.contains("theorem resolution_step_1"));
    assert!(lean.contains("theorem proof_valid"));
}

// ---------------------------------------------------------------------------
// 2. Chain resolution (3+ steps)
// ---------------------------------------------------------------------------

#[test]
fn test_lean_validation_chain_resolution_three_steps() {
    let t = trace(
        vec![cl(1, &[1]), cl(2, &[-1, 2]), cl(3, &[-2, 3]), cl(4, &[-3])],
        vec![rs(5, 1, 1, 2), rs(6, 2, 5, 3), rs(7, 3, 6, 4)],
        7,
    );
    let lean = export_and_validate(&t);

    assert!(lean.contains("resolution_step_1"));
    assert!(lean.contains("resolution_step_2"));
    assert!(lean.contains("resolution_step_3"));
    assert!(lean.contains("Clause.isEmpty clause_7"));
}

#[test]
fn test_lean_validation_chain_resolution_five_steps() {
    let t = trace(
        vec![
            cl(1, &[1]),
            cl(2, &[-1, 2]),
            cl(3, &[-2, 3]),
            cl(4, &[-3, 4]),
            cl(5, &[-4, 5]),
            cl(6, &[-5]),
        ],
        vec![
            rs(10, 1, 1, 2),
            rs(11, 2, 10, 3),
            rs(12, 3, 11, 4),
            rs(13, 4, 12, 5),
            rs(14, 5, 13, 6),
        ],
        14,
    );
    let lean = export_and_validate(&t);

    for i in 1..=5 {
        assert!(
            lean.contains(&format!("resolution_step_{i}")),
            "missing resolution_step_{i}"
        );
    }
}

// ---------------------------------------------------------------------------
// 3. Theory lemma (axiom) handling
// ---------------------------------------------------------------------------

#[test]
fn test_lean_validation_theory_lemma_euf() {
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
    let lean = export_and_validate(&t);

    assert!(lean.contains("axiom theory_lemma_2_valid : True"));
    assert!(lean.contains("-- Theory: EUF (trusted)"));
    assert!(lean.contains("def clause_2 : Clause"));
}

#[test]
fn test_lean_validation_multiple_theory_kinds() {
    let t = ProofTrace {
        input_clauses: vec![cl(1, &[1, 2, 3])],
        resolution_steps: vec![],
        theory_lemmas: vec![
            TheoryLemma {
                id: 10,
                theory: "EUF".into(),
                clause: cl(10, &[-1]),
            },
            TheoryLemma {
                id: 11,
                theory: "LRA".into(),
                clause: cl(11, &[-2]),
            },
            TheoryLemma {
                id: 12,
                theory: "BV".into(),
                clause: cl(12, &[-3]),
            },
        ],
        empty_clause_id: 1,
    };
    let lean = export_and_validate(&t);

    assert!(lean.contains("axiom theory_lemma_10_valid"));
    assert!(lean.contains("axiom theory_lemma_11_valid"));
    assert!(lean.contains("axiom theory_lemma_12_valid"));
    assert!(lean.contains("-- Theory: EUF"));
    assert!(lean.contains("-- Theory: LRA"));
    assert!(lean.contains("-- Theory: BV"));
}

// ---------------------------------------------------------------------------
// 4. Mixed resolution + theory lemma proofs
// ---------------------------------------------------------------------------

#[test]
fn test_lean_validation_mixed_input_theory_resolution() {
    let t = ProofTrace {
        input_clauses: vec![cl(1, &[1, 2])],
        resolution_steps: vec![rs(4, 1, 1, 2), rs(5, 2, 4, 3)],
        theory_lemmas: vec![
            TheoryLemma {
                id: 2,
                theory: "EUF".into(),
                clause: cl(2, &[-1]),
            },
            TheoryLemma {
                id: 3,
                theory: "LRA".into(),
                clause: cl(3, &[-2]),
            },
        ],
        empty_clause_id: 5,
    };
    let lean = export_and_validate(&t);

    assert!(lean.contains("def clause_1"));
    assert!(lean.contains("def clause_2"));
    assert!(lean.contains("def clause_3"));
    assert!(lean.contains("axiom theory_lemma_2_valid"));
    assert!(lean.contains("axiom theory_lemma_3_valid"));
    assert!(lean.contains("resolution_step_1"));
    assert!(lean.contains("resolution_step_2"));
    assert!(lean.contains("Clause.isEmpty clause_5"));
}

// ---------------------------------------------------------------------------
// 5. Empty input clause handling
// ---------------------------------------------------------------------------

#[test]
fn test_lean_validation_empty_input_clause_is_proof() {
    let t = trace(vec![cl(1, &[])], vec![], 1);
    let lean = export_and_validate(&t);

    assert!(lean.contains("def clause_1 : Clause"));
    assert!(lean.contains("Clause.isEmpty clause_1"));
    assert!(!lean.contains("resolution_step_"));
}

#[test]
fn test_lean_validation_only_theory_lemma_empty() {
    let t = ProofTrace {
        input_clauses: vec![],
        resolution_steps: vec![],
        theory_lemmas: vec![TheoryLemma {
            id: 1,
            theory: "EUF".into(),
            clause: cl(1, &[]),
        }],
        empty_clause_id: 1,
    };
    let lean = export_and_validate(&t);

    assert!(lean.contains("axiom theory_lemma_1_valid"));
    assert!(lean.contains("Clause.isEmpty clause_1"));
}

// ---------------------------------------------------------------------------
// 6. Large proof (50+ steps)
// ---------------------------------------------------------------------------

#[test]
fn test_lean_validation_large_proof_50_steps() {
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
    let lean = export_and_validate(&t);

    assert!(lean.contains("resolution_step_51"));
    assert!(lean.contains(&format!("Clause.isEmpty clause_{final_id}")));
}

#[test]
fn test_lean_validation_large_proof_100_steps() {
    let n: i64 = 100;
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
    let lean = export_and_validate(&t);

    assert!(lean.contains("resolution_step_101"));
    assert!(lean.contains(&format!("Clause.isEmpty clause_{final_id}")));
}

// ---------------------------------------------------------------------------
// 7. Header and structural validation
// ---------------------------------------------------------------------------

#[test]
fn test_lean_validation_header_present() {
    let t = trace(vec![cl(1, &[1]), cl(2, &[-1])], vec![rs(3, 1, 1, 2)], 3);
    let lean = export_and_validate(&t);

    assert!(lean.starts_with("-- Auto-generated by trust-vc-kernel\n"));
    assert!(lean.contains("trust_vc version: 1.0.0"));
    assert!(lean.contains("generator: trust-vc-kernel::lean_export"));
}

#[test]
fn test_lean_validation_prelude_structure() {
    let t = trace(vec![cl(1, &[1]), cl(2, &[-1])], vec![rs(3, 1, 1, 2)], 3);
    let lean = export_and_validate(&t);

    assert!(lean.contains("abbrev Literal := Int"));
    assert!(lean.contains("structure Clause where"));
    assert!(lean.contains("lits : List Literal"));
    assert!(lean.contains("deriving Repr, DecidableEq"));
    assert!(lean.contains("def negLit"));
    assert!(lean.contains("def Clause.isEmpty"));
    assert!(lean.contains("def resolves"));
}

// ---------------------------------------------------------------------------
// 8. Negative literal formatting
// ---------------------------------------------------------------------------

#[test]
fn test_lean_validation_negative_literals_parenthesized() {
    let t = trace(vec![cl(1, &[-42, 7, -100])], vec![], 1);
    let lean = export_and_validate(&t);

    assert!(lean.contains("(-42)"));
    assert!(lean.contains("7"));
    assert!(lean.contains("(-100)"));
}

// ---------------------------------------------------------------------------
// 9. Error cases: export_lean5 rejects bad input
// ---------------------------------------------------------------------------

#[test]
fn test_lean_validation_export_rejects_empty_trace() {
    let t = ProofTrace {
        input_clauses: vec![],
        resolution_steps: vec![],
        theory_lemmas: vec![],
        empty_clause_id: 0,
    };
    let err = export_lean5(&t).expect_err("empty trace should fail");
    assert!(matches!(err, LeanExportError::EmptyTrace));
}

#[test]
fn test_lean_validation_export_rejects_missing_empty_clause() {
    let t = trace(vec![cl(1, &[1]), cl(2, &[-1])], vec![rs(3, 1, 1, 2)], 999);
    let err = export_lean5(&t).expect_err("missing empty clause should fail");
    assert!(matches!(err, LeanExportError::EmptyClauseNotFound(999)));
}

// ---------------------------------------------------------------------------
// 10. Syntax checker: identifier validation
// ---------------------------------------------------------------------------

#[test]
fn test_lean_validation_ident_checker() {
    assert!(is_valid_lean_ident("x"));
    assert!(is_valid_lean_ident("clause_1"));
    assert!(is_valid_lean_ident("resolution_step_42"));
    assert!(is_valid_lean_ident("_hidden"));
    assert!(is_valid_lean_ident("x'"));
    assert!(is_valid_lean_ident("Clause"));

    assert!(!is_valid_lean_ident(""));
    assert!(!is_valid_lean_ident("123abc"));
    assert!(!is_valid_lean_ident("a b"));
    assert!(!is_valid_lean_ident("+"));
    assert!(is_valid_lean_ident("a.b")); // qualified name
}

// ---------------------------------------------------------------------------
// 11. Syntax checker: detects dangling references
// ---------------------------------------------------------------------------

#[test]
fn test_lean_validation_syntax_checker_detects_dangling_clause() {
    let bad_source = concat!(
        "-- Auto-generated by trust-vc-kernel\n",
        "abbrev Literal := Int\n",
        "structure Clause where\n",
        "  lits : List Literal\n",
        "deriving Repr, DecidableEq\n",
        "def negLit (l : Literal) : Literal := -l\n",
        "def Clause.isEmpty (c : Clause) : Prop := c.lits = []\n",
        "instance : Decidable (Clause.isEmpty c) := inferInstanceAs (Decidable (c.lits = []))\n",
        "def resolves (a b : Clause) (p : Literal) (r : Clause) : Prop :=\n",
        "  r.lits = (a.lits.filter (\u{b7} != p)) ++ (b.lits.filter (\u{b7} != negLit p))\n",
        "instance : Decidable (resolves a b p r) := inferInstanceAs (Decidable (_ = _))\n",
        "def clause_1 : Clause := \u{27e8}[1]\u{27e9}\n",
        "theorem resolution_step_1 : resolves clause_1 clause_99 1 clause_3 := by\n",
        "  decide\n",
        "theorem proof_valid : Clause.isEmpty clause_3 := by\n",
        "  decide\n",
    );
    let errs = validate_lean_syntax(bad_source).expect_err("should detect dangling refs");
    let dangling: Vec<&SyntaxError> = errs
        .iter()
        .filter(|e| e.message.contains("dangling"))
        .collect();
    assert!(
        !dangling.is_empty(),
        "should detect at least one dangling clause reference"
    );
}

// ---------------------------------------------------------------------------
// 12. Syntax checker: detects missing proof_valid
// ---------------------------------------------------------------------------

#[test]
fn test_lean_validation_syntax_checker_detects_missing_proof_valid() {
    let bad_source = concat!(
        "-- Auto-generated by trust-vc-kernel\n",
        "abbrev Literal := Int\n",
        "def clause_1 : Clause := \u{27e8}[1]\u{27e9}\n",
    );
    let errs = validate_lean_syntax(bad_source).expect_err("should detect missing proof_valid");
    let missing: Vec<&SyntaxError> = errs
        .iter()
        .filter(|e| e.message.contains("proof_valid"))
        .collect();
    assert!(
        !missing.is_empty(),
        "should detect missing proof_valid theorem"
    );
}

// ---------------------------------------------------------------------------
// 13. Syntax checker: detects unbalanced delimiters
// ---------------------------------------------------------------------------

#[test]
fn test_lean_validation_syntax_checker_detects_unbalanced_parens() {
    let bad_source = concat!(
        "-- Auto-generated by trust-vc-kernel\n",
        "def clause_1 : Clause := \u{27e8}[1, (2]\u{27e9}\n",
        "theorem proof_valid : Clause.isEmpty clause_1 := by\n",
        "  decide\n",
    );
    let errs = validate_lean_syntax(bad_source).expect_err("should detect unbalanced parens");
    let delim_errs: Vec<&SyntaxError> = errs
        .iter()
        .filter(|e| e.message.contains("mismatched") || e.message.contains("unclosed"))
        .collect();
    assert!(!delim_errs.is_empty(), "should detect delimiter mismatch");
}

// ---------------------------------------------------------------------------
// 14. Property-based: random proof traces never panic
// ---------------------------------------------------------------------------

#[test]
fn test_lean_validation_random_traces_no_panic() {
    for n in 0..20u64 {
        let inputs: Vec<Clause> = (1..=n)
            .map(|i| cl(i, &[i as i64, -(i as i64 + 1)]))
            .collect();

        let empty_id = if inputs.is_empty() { 0 } else { 1 };
        let t = ProofTrace {
            input_clauses: inputs,
            resolution_steps: vec![],
            theory_lemmas: vec![],
            empty_clause_id: empty_id,
        };
        // Should not panic -- may return Err for n==0 (empty trace)
        let _ = export_lean5(&t);
    }
}

#[test]
fn test_lean_validation_random_chain_traces_validate() {
    for chain_len in 1..=15i64 {
        let n = chain_len;
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
        let lean = export_lean5(&t)
            .unwrap_or_else(|e| panic!("export_lean5 failed for chain_len={chain_len}: {e}"));
        if let Err(errs) = validate_lean_syntax(&lean) {
            let msgs: Vec<String> = errs.iter().map(|e| e.to_string()).collect();
            panic!(
                "validate_lean_syntax failed for chain_len={chain_len}:\n{}",
                msgs.join("\n")
            );
        }
    }
}

// ---------------------------------------------------------------------------
// 15. Cross-validation: every resolution step references defined clauses
// ---------------------------------------------------------------------------

#[test]
fn test_lean_validation_all_clause_refs_defined() {
    let t = ProofTrace {
        input_clauses: vec![cl(1, &[1, 2, 3]), cl(2, &[-1])],
        resolution_steps: vec![rs(5, 1, 1, 2), rs(6, 2, 5, 3), rs(7, 3, 6, 4)],
        theory_lemmas: vec![
            TheoryLemma {
                id: 3,
                theory: "LRA".into(),
                clause: cl(3, &[-2]),
            },
            TheoryLemma {
                id: 4,
                theory: "BV".into(),
                clause: cl(4, &[-3]),
            },
        ],
        empty_clause_id: 7,
    };
    export_and_validate(&t);
}

// ---------------------------------------------------------------------------
// 16. by/decide pairing validated
// ---------------------------------------------------------------------------

#[test]
fn test_lean_validation_by_decide_pairing() {
    let t = trace(
        vec![cl(1, &[1]), cl(2, &[-1, 2]), cl(3, &[-2])],
        vec![rs(4, 1, 1, 2), rs(5, 2, 4, 3)],
        5,
    );
    let lean = export_and_validate(&t);

    let by_count = lean.lines().filter(|l| l.trim().ends_with(":= by")).count();
    let decide_count = lean.lines().filter(|l| l.trim() == "decide").count();
    assert_eq!(
        by_count, decide_count,
        ":= by count ({by_count}) should equal decide count ({decide_count})"
    );
}

// ---------------------------------------------------------------------------
// 17. Theory-only proof (no input clauses, no resolution)
// ---------------------------------------------------------------------------

#[test]
fn test_lean_validation_theory_only_no_input_no_resolution() {
    let t = ProofTrace {
        input_clauses: vec![],
        resolution_steps: vec![],
        theory_lemmas: vec![TheoryLemma {
            id: 42,
            theory: "NIA".into(),
            clause: cl(42, &[]),
        }],
        empty_clause_id: 42,
    };
    let lean = export_and_validate(&t);

    assert!(!lean.contains("-- Input clauses"));
    assert!(!lean.contains("-- Resolution steps"));
    assert!(lean.contains("axiom theory_lemma_42_valid"));
}

// ---------------------------------------------------------------------------
// 18. Syntax checker on valid generated output
// ---------------------------------------------------------------------------

#[test]
fn test_lean_validation_syntax_checker_passes_all_valid_exports() {
    let traces = [
        trace(vec![cl(1, &[])], vec![], 1),
        trace(vec![cl(1, &[1]), cl(2, &[-1])], vec![rs(3, 1, 1, 2)], 3),
        trace(
            vec![cl(1, &[1]), cl(2, &[-1, 2]), cl(3, &[-2])],
            vec![rs(4, 1, 1, 2), rs(5, 2, 4, 3)],
            5,
        ),
        trace(
            vec![
                cl(1, &[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]),
                cl(2, &[-1, -2, -3, -4, -5, -6, -7, -8, -9, -10]),
            ],
            vec![],
            1,
        ),
    ];

    for (i, t) in traces.iter().enumerate() {
        let lean =
            export_lean5(t).unwrap_or_else(|e| panic!("trace {i}: export_lean5 failed: {e}"));
        if let Err(errs) = validate_lean_syntax(&lean) {
            let msgs: Vec<String> = errs.iter().map(|e| e.to_string()).collect();
            panic!(
                "trace {i}: validate_lean_syntax failed:\n{}",
                msgs.join("\n")
            );
        }
    }
}

// ---------------------------------------------------------------------------
// 19. Lean-validate feature: run lean binary (only with feature flag)
// ---------------------------------------------------------------------------

#[cfg(feature = "lean-validate")]
#[test]
fn test_lean_validation_lean_binary_typechecks_simple() {
    use std::io::Write as _;
    use std::process::Command;

    let lean_bin = std::path::PathBuf::from(std::env::var("LEAN_BIN").unwrap_or_else(|_| {
        let home = std::env::var("HOME").expect("HOME not set");
        format!("{home}/lean5/bin/lean")
    }));

    if !lean_bin.exists() {
        panic!(
            "lean binary not found at {}: set LEAN_BIN env var or install lean5 at ~/lean5/",
            lean_bin.display()
        );
    }

    let t = trace(vec![cl(1, &[1]), cl(2, &[-1])], vec![rs(3, 1, 1, 2)], 3);
    let lean = export_lean5(&t).expect("export should succeed");

    let dir = std::env::temp_dir().join("trust_vc_lean_validate");
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let path = dir.join("test_simple.lean");
    {
        let mut f = std::fs::File::create(&path).expect("create temp file");
        f.write_all(lean.as_bytes()).expect("write lean source");
    }

    let output = Command::new(&lean_bin)
        .arg(&path)
        .output()
        .expect("run lean");

    assert!(
        output.status.success(),
        "lean type-checking failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );

    let _ = std::fs::remove_file(&path);
}

// ---------------------------------------------------------------------------
// 20. Angle bracket balance across all generated output
// ---------------------------------------------------------------------------

#[test]
fn test_lean_validation_angle_bracket_balance() {
    let t = ProofTrace {
        input_clauses: vec![cl(1, &[1, -2, 3]), cl(2, &[-1, 2])],
        resolution_steps: vec![rs(4, 1, 1, 2)],
        theory_lemmas: vec![TheoryLemma {
            id: 3,
            theory: "EUF".into(),
            clause: cl(3, &[-3]),
        }],
        empty_clause_id: 4,
    };
    let lean = export_and_validate(&t);

    let open_count = lean.chars().filter(|&c| c == '\u{27e8}').count();
    let close_count = lean.chars().filter(|&c| c == '\u{27e9}').count();
    assert_eq!(
        open_count, close_count,
        "angle brackets unbalanced: {open_count} open vs {close_count} close"
    );
}

// ---------------------------------------------------------------------------
// 21. No triple newlines in output
// ---------------------------------------------------------------------------

#[test]
fn test_lean_validation_no_triple_newlines() {
    let t = trace(
        vec![cl(1, &[1, 2]), cl(2, &[-1]), cl(3, &[-2])],
        vec![rs(4, 1, 1, 2), rs(5, 2, 4, 3)],
        5,
    );
    let lean = export_and_validate(&t);
    assert!(
        !lean.contains("\n\n\n"),
        "output should not contain triple newlines"
    );
}
