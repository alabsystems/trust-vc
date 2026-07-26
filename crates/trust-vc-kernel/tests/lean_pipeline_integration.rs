// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Integration tests for the full proof certificate -> Lean5 export pipeline.
//!
//! These tests exercise the complete flow: construct a `TrustVcProofCertificate`
//! in wire format (via JSON deserialization to avoid `#[non_exhaustive]`
//! struct-expression restrictions), run proof checking and theory validation,
//! export to multiple formats (JSON, binary, human-readable, SMT-LIB2),
//! convert to internal `ProofTrace` for Lean5 export, and validate the
//! generated Lean5 syntax.

use trust_vc_kernel::export::{export_certificate, ExportFormat};
use trust_vc_kernel::format::{TrustVcProofCertificate, CERTIFICATE_VERSION};
use trust_vc_kernel::{
    check_proof, check_proof_with_theory, check_theory_lemma, export_lean5, is_valid_lean_ident,
    validate_lean_syntax, CheckResult, Clause, ProofTrace, ResolutionStep, TheoryCheckResult,
    TheoryLemma,
};

// ---------------------------------------------------------------------------
// Helper functions — internal types (no #[non_exhaustive] restriction)
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

/// Build a theory lemma.
fn tl(id: u64, theory: &str, lits: &[i64]) -> TheoryLemma {
    TheoryLemma {
        id,
        theory: theory.to_string(),
        clause: cl(id, lits),
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

/// Create a simple valid proof trace: 3 input clauses, 2 resolution steps.
///
///   Input clause 1: {1}
///   Input clause 2: {-1, 2}
///   Input clause 3: {-2}
///   Step 10: resolve(1, 2) on pivot 1 -> {2}
///   Step 11: resolve(10, 3) on pivot 2 -> {} (empty clause)
fn make_simple_trace() -> ProofTrace {
    trace(
        vec![cl(1, &[1]), cl(2, &[-1, 2]), cl(3, &[-2])],
        vec![rs(10, 1, 1, 2), rs(11, 2, 10, 3)],
        11,
    )
}

/// Create a proof trace with a theory lemma (EUF or LRA).
///
///   Input clause 1: {1}
///   Theory lemma 10: {-1, 2} (specified theory)
///   Input clause 3: {-2}
///   Step 20: resolve(1, 10) on pivot 1 -> {2}
///   Step 21: resolve(20, 3) on pivot 2 -> {}
fn make_trace_with_theory(theory: &str) -> ProofTrace {
    trace_with_theories(
        vec![cl(1, &[1]), cl(3, &[-2])],
        vec![rs(20, 1, 1, 10), rs(21, 2, 20, 3)],
        vec![tl(10, theory, &[-1, 2])],
        21,
    )
}

/// Create a large chain proof trace for performance testing.
///
/// Chain: clause 1 = {1}, clause i+1 = {-i, i+1}, clause n+2 = {-(n+1)}.
/// Resolution chain eliminates variables 1 through n+1 in sequence.
fn make_large_trace(n_steps: usize) -> ProofTrace {
    let n = n_steps as i64;
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

    trace(inputs, steps, final_id)
}

// ---------------------------------------------------------------------------
// Helper functions — wire-format certificates via JSON
// ---------------------------------------------------------------------------

/// Build a simple valid wire-format certificate via JSON deserialization.
fn make_simple_certificate() -> TrustVcProofCertificate {
    let json = serde_json::json!({
        "version": CERTIFICATE_VERSION,
        "source_hash": vec![0xABu8; 32],
        "vc_hash": vec![0xCDu8; 32],
        "input_clauses": [
            { "id": 1, "literals": [1] },
            { "id": 2, "literals": [-1, 2] },
            { "id": 3, "literals": [-2] }
        ],
        "resolution_steps": [
            {
                "result_id": 10,
                "antecedent_a": 1,
                "antecedent_b": 2,
                "pivot": 1,
                "result_literals": [2]
            },
            {
                "result_id": 11,
                "antecedent_a": 10,
                "antecedent_b": 3,
                "pivot": 2,
                "result_literals": []
            }
        ],
        "theory_lemmas": [],
        "empty_clause_id": 11,
        "metadata": {
            "timestamp": "2026-03-28T12:00:00Z",
            "trust_vc_version": "1.0.0",
            "solver_version": "ay-dpll 0.1.0"
        }
    });
    serde_json::from_value(json).expect("simple certificate JSON should parse")
}

/// Build a wire-format certificate with theory lemmas via JSON.
fn make_certificate_with_theory(kind: &str) -> TrustVcProofCertificate {
    let json = serde_json::json!({
        "version": CERTIFICATE_VERSION,
        "source_hash": vec![0x11u8; 32],
        "vc_hash": vec![0x22u8; 32],
        "input_clauses": [
            { "id": 1, "literals": [1] },
            { "id": 3, "literals": [-2] }
        ],
        "resolution_steps": [
            {
                "result_id": 20,
                "antecedent_a": 1,
                "antecedent_b": 10,
                "pivot": 1,
                "result_literals": [2]
            },
            {
                "result_id": 21,
                "antecedent_a": 20,
                "antecedent_b": 3,
                "pivot": 2,
                "result_literals": []
            }
        ],
        "theory_lemmas": [
            {
                "id": 10,
                "kind": kind,
                "literals": [-1, 2],
                "justification": format!("{kind} justification")
            }
        ],
        "empty_clause_id": 21,
        "metadata": {
            "timestamp": "2026-03-28T12:00:00Z",
            "trust_vc_version": "1.0.0",
            "solver_version": "ay-dpll 0.1.0"
        }
    });
    serde_json::from_value(json).expect("theory certificate JSON should parse")
}

/// Build a large wire-format certificate via JSON.
fn make_large_certificate(n_steps: usize) -> TrustVcProofCertificate {
    let n = n_steps;
    let mut input_clauses = vec![serde_json::json!({ "id": 1, "literals": [1] })];
    for i in 1..=n {
        input_clauses.push(serde_json::json!({
            "id": (i + 1) as u64,
            "literals": [-(i as i64), (i + 1) as i64]
        }));
    }
    input_clauses.push(serde_json::json!({
        "id": (n + 2) as u64,
        "literals": [-((n + 1) as i64)]
    }));

    let base = (n + 10) as u64;
    let mut resolution_steps = vec![serde_json::json!({
        "result_id": base,
        "antecedent_a": 1u64,
        "antecedent_b": 2u64,
        "pivot": 1i64,
        "result_literals": [2i64]
    })];
    for i in 2..=n {
        resolution_steps.push(serde_json::json!({
            "result_id": base + (i - 1) as u64,
            "antecedent_a": base + (i - 2) as u64,
            "antecedent_b": (i + 1) as u64,
            "pivot": i as i64,
            "result_literals": [(i + 1) as i64]
        }));
    }
    let final_id = base + n as u64;
    resolution_steps.push(serde_json::json!({
        "result_id": final_id,
        "antecedent_a": final_id - 1,
        "antecedent_b": (n + 2) as u64,
        "pivot": (n + 1) as i64,
        "result_literals": []
    }));

    let json = serde_json::json!({
        "version": CERTIFICATE_VERSION,
        "source_hash": vec![0x33u8; 32],
        "vc_hash": vec![0x44u8; 32],
        "input_clauses": input_clauses,
        "resolution_steps": resolution_steps,
        "theory_lemmas": [],
        "empty_clause_id": final_id,
        "metadata": {
            "timestamp": "2026-03-28T12:00:00Z",
            "trust_vc_version": "1.0.0",
            "solver_version": "ay-dpll 0.1.0"
        }
    });
    serde_json::from_value(json).expect("large certificate JSON should parse")
}

/// Export Lean5 and validate syntax in one step.
fn export_and_validate_lean5(t: &ProofTrace) -> String {
    let lean = export_lean5(t).expect("Lean5 export should succeed");
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

// ===========================================================================
// 1. Simple certificate passes proof check
// ===========================================================================

#[test]
fn test_simple_certificate_passes_proof_check() {
    let t = make_simple_trace();
    assert_eq!(check_proof(&t), CheckResult::Valid);
}

// ===========================================================================
// 2. Simple certificate exports JSON
// ===========================================================================

#[test]
fn test_simple_certificate_exports_json() {
    let cert = make_simple_certificate();
    let bytes = export_certificate(&cert, ExportFormat::Json).expect("JSON export should succeed");
    let json = std::str::from_utf8(&bytes).expect("JSON should be valid UTF-8");
    assert!(json.contains("\"version\""));
    assert!(json.contains("\"input_clauses\""));
    assert!(json.contains("\"resolution_steps\""));
    assert!(json.contains("\"empty_clause_id\""));
}

// ===========================================================================
// 3. Simple certificate exports human-readable
// ===========================================================================

#[test]
fn test_simple_certificate_exports_human_readable() {
    let cert = make_simple_certificate();
    let bytes = export_certificate(&cert, ExportFormat::HumanReadable)
        .expect("human-readable export should succeed");
    let text = std::str::from_utf8(&bytes).expect("output should be valid UTF-8");
    assert!(
        text.contains("TrustVc Proof Certificate"),
        "should contain header"
    );
    assert!(
        text.contains("[resolve]"),
        "should contain resolution steps"
    );
    assert!(text.contains("[assume]"), "should contain assumptions");
}

// ===========================================================================
// 4. Simple certificate exports Lean5
// ===========================================================================

#[test]
fn test_simple_certificate_exports_lean5() {
    let t = make_simple_trace();
    let lean = export_lean5(&t).expect("Lean5 export should succeed");
    assert!(lean.contains("Auto-generated by trust-vc-kernel"));
    assert!(lean.contains("abbrev Literal := Int"));
    assert!(lean.contains("def clause_1"));
    assert!(lean.contains("def clause_2"));
    assert!(lean.contains("def clause_3"));
    assert!(lean.contains("theorem resolution_step_1"));
    assert!(lean.contains("theorem resolution_step_2"));
    assert!(lean.contains("theorem proof_valid"));
}

// ===========================================================================
// 5. Lean5 export validates syntax
// ===========================================================================

#[test]
fn test_lean5_export_validates_syntax() {
    let t = make_simple_trace();
    let lean = export_lean5(&t).expect("Lean5 export should succeed");
    validate_lean_syntax(&lean).expect("generated Lean5 should pass syntax validation");
}

// ===========================================================================
// 6. EUF theory lemma passes theory check
// ===========================================================================

#[test]
fn test_euf_theory_lemma_passes_theory_check() {
    let t = make_trace_with_theory("EUF");
    let result = check_proof_with_theory(&t);
    assert_eq!(result.result, CheckResult::Valid);
    // EUF lemma {-1, 2} has at most 1 positive literal (2) -> verified.
    assert_eq!(result.theory_stats.verified_count, 1);
    assert_eq!(result.theory_stats.invalid_count, 0);
}

// ===========================================================================
// 7. LRA theory lemma passes theory check
// ===========================================================================

#[test]
fn test_lra_theory_lemma_passes_theory_check() {
    let t = make_trace_with_theory("LRA");
    let result = check_proof_with_theory(&t);
    assert_eq!(result.result, CheckResult::Valid);
    // LRA lemma {-1, 2} has 2 literals (Farkas minimum) -> verified.
    assert_eq!(result.theory_stats.verified_count, 1);
    assert_eq!(result.theory_stats.invalid_count, 0);
}

// ===========================================================================
// 8. Certificate JSON roundtrip (serialize -> deserialize -> re-check)
// ===========================================================================

#[test]
fn test_certificate_json_roundtrip() {
    let cert = make_simple_certificate();
    let json = cert.to_json().expect("serialization should succeed");
    let recovered =
        TrustVcProofCertificate::from_json(&json).expect("deserialization should succeed");
    assert_eq!(cert, recovered);

    // The proof trace derived from the roundtripped certificate should still be valid.
    let t = make_simple_trace();
    assert_eq!(check_proof(&t), CheckResult::Valid);
}

// ===========================================================================
// 9. Empty certificate rejected
// ===========================================================================

#[test]
fn test_empty_certificate_rejected() {
    let t = ProofTrace {
        input_clauses: vec![],
        resolution_steps: vec![],
        theory_lemmas: vec![],
        empty_clause_id: 0,
    };
    match check_proof(&t) {
        CheckResult::Invalid { step, reason } => {
            assert_eq!(step, 0);
            assert!(reason.contains("not found"), "reason: {reason}");
        }
        CheckResult::Valid => panic!("empty certificate should not be valid"),
        _ => panic!("unexpected CheckResult variant"),
    }
}

// ===========================================================================
// 10. Wrong version rejected
// ===========================================================================

#[test]
fn test_wrong_version_rejected() {
    let cert = make_simple_certificate();
    let mut json_val: serde_json::Value =
        serde_json::from_str(&cert.to_json().expect("serialize")).expect("parse as Value");
    json_val["version"] = serde_json::json!(CERTIFICATE_VERSION + 99);
    let raw_json = serde_json::to_string_pretty(&json_val).expect("reserialize");
    let err = TrustVcProofCertificate::from_json(&raw_json)
        .expect_err("future version should be rejected");
    let msg = format!("{err}");
    assert!(
        msg.contains("unsupported"),
        "error should mention unsupported version: {msg}"
    );
}

// ===========================================================================
// 11. Invalid proof rejected (pivot not in parent)
// ===========================================================================

#[test]
fn test_invalid_proof_rejected() {
    // Pivot=3 but 3 is not in either parent.
    let t = trace(vec![cl(1, &[1, 2]), cl(2, &[-1])], vec![rs(3, 3, 1, 2)], 3);
    match check_proof(&t) {
        CheckResult::Invalid { step, reason } => {
            assert_eq!(step, 3);
            assert!(reason.contains("pivot"), "reason: {reason}");
        }
        CheckResult::Valid => panic!("invalid pivot should be rejected"),
        _ => panic!("unexpected CheckResult variant"),
    }
}

// ===========================================================================
// 12. Dangling clause reference rejected
// ===========================================================================

#[test]
fn test_dangling_clause_reference_rejected() {
    let t = trace(
        vec![cl(1, &[1])],
        vec![rs(3, 1, 1, 999)], // parent 999 does not exist
        3,
    );
    match check_proof(&t) {
        CheckResult::Invalid { step, reason } => {
            assert_eq!(step, 3);
            assert!(
                reason.contains("unknown clause"),
                "reason should mention missing clause: {reason}"
            );
        }
        CheckResult::Valid => panic!("dangling reference should be rejected"),
        _ => panic!("unexpected CheckResult variant"),
    }
}

// ===========================================================================
// 13. Large certificate proof check (100 steps)
// ===========================================================================

#[test]
fn test_large_certificate_proof_check() {
    let t = make_large_trace(100);
    assert_eq!(check_proof(&t), CheckResult::Valid);
}

// ===========================================================================
// 14. Large certificate export JSON
// ===========================================================================

#[test]
fn test_large_certificate_export_json() {
    let cert = make_large_certificate(100);
    let bytes =
        export_certificate(&cert, ExportFormat::Json).expect("large certificate JSON export");
    let json = std::str::from_utf8(&bytes).expect("should be valid UTF-8");
    // Verify JSON is parseable and roundtrips.
    let recovered: TrustVcProofCertificate =
        serde_json::from_str(json).expect("exported JSON should parse back");
    assert_eq!(
        cert.resolution_steps.len(),
        recovered.resolution_steps.len()
    );
}

// ===========================================================================
// 15. Certificate metadata preserved
// ===========================================================================

#[test]
fn test_certificate_metadata_preserved() {
    let cert = make_simple_certificate();
    let json = cert.to_json().expect("serialization should succeed");
    let recovered =
        TrustVcProofCertificate::from_json(&json).expect("deserialization should succeed");
    assert_eq!(cert.metadata.timestamp, recovered.metadata.timestamp);
    assert_eq!(
        cert.metadata.trust_vc_version,
        recovered.metadata.trust_vc_version
    );
    assert_eq!(
        cert.metadata.solver_version,
        recovered.metadata.solver_version
    );
    assert_eq!(cert.source_hash, recovered.source_hash);
    assert_eq!(cert.vc_hash, recovered.vc_hash);
}

// ===========================================================================
// 16. Lean5 identifiers valid
// ===========================================================================

#[test]
fn test_lean5_identifiers_valid() {
    let t = make_simple_trace();
    let lean = export_lean5(&t).expect("Lean5 export should succeed");

    // Extract all identifiers from def, theorem, and axiom declarations.
    for line in lean.lines() {
        let trimmed = line.trim();
        for prefix in &["def ", "theorem ", "axiom ", "abbrev "] {
            if let Some(rest) = trimmed.strip_prefix(prefix) {
                let ident = rest.split_whitespace().next().unwrap_or("");
                if !ident.is_empty() {
                    assert!(
                        is_valid_lean_ident(ident),
                        "identifier '{ident}' should be valid (from line: {trimmed})"
                    );
                }
            }
        }
    }
}

// ===========================================================================
// 17. Binary export roundtrip
// ===========================================================================

#[test]
fn test_binary_export_roundtrip() {
    let cert = make_simple_certificate();
    let bytes = cert
        .to_bytes()
        .expect("binary serialization should succeed");
    assert!(!bytes.is_empty());
    let recovered =
        TrustVcProofCertificate::from_bytes(&bytes).expect("binary deserialization should succeed");
    assert_eq!(cert, recovered);
}

// ===========================================================================
// 18. Human-readable contains theory info
// ===========================================================================

#[test]
fn test_human_readable_contains_theory_info() {
    let cert = make_certificate_with_theory("Euf");
    let bytes = export_certificate(&cert, ExportFormat::HumanReadable)
        .expect("human-readable export should succeed");
    let text = std::str::from_utf8(&bytes).expect("should be valid UTF-8");
    assert!(
        text.contains("[T:EUF]"),
        "human-readable should contain theory tag [T:EUF]: got:\n{text}"
    );
}

// ===========================================================================
// 19. Proof check then export pipeline
// ===========================================================================

#[test]
fn test_proof_check_then_export_pipeline() {
    let cert = make_simple_certificate();
    let t = make_simple_trace();

    // Step 1: proof check
    assert_eq!(check_proof(&t), CheckResult::Valid);

    // Step 2: export to JSON
    let json_bytes =
        export_certificate(&cert, ExportFormat::Json).expect("JSON export should succeed");
    assert!(!json_bytes.is_empty());

    // Step 3: export to Lean5
    let lean = export_lean5(&t).expect("Lean5 export should succeed");

    // Step 4: validate Lean5 syntax
    validate_lean_syntax(&lean).expect("generated Lean5 should pass syntax validation");

    // Step 5: export to binary
    let bin_bytes =
        export_certificate(&cert, ExportFormat::Binary).expect("binary export should succeed");
    assert!(!bin_bytes.is_empty());
}

// ===========================================================================
// 20. Multiple theory lemmas
// ===========================================================================

#[test]
fn test_multiple_theory_lemmas() {
    // Input: {1}, {3}
    // EUF lemma 10: {-1, 2}
    // LRA lemma 20: {-2, -3}
    // Step 30: resolve(1, 10) on 1 -> {2}
    // Step 31: resolve(30, 20) on 2 -> {-3}
    // Step 32: resolve(2={3}, 31={-3}) on 3 -> {}
    let t = trace_with_theories(
        vec![cl(1, &[1]), cl(2, &[3])],
        vec![rs(30, 1, 1, 10), rs(31, 2, 30, 20), rs(32, 3, 2, 31)],
        vec![tl(10, "EUF", &[-1, 2]), tl(20, "LRA", &[-2, -3])],
        32,
    );
    let result = check_proof_with_theory(&t);
    assert_eq!(result.result, CheckResult::Valid);
    assert_eq!(result.theory_stats.verified_count, 2);
    assert_eq!(result.theory_stats.invalid_count, 0);
}

// ===========================================================================
// 21. Certificate with no theory lemmas
// ===========================================================================

#[test]
fn test_certificate_with_no_theory_lemmas() {
    let t = make_simple_trace();
    let result = check_proof_with_theory(&t);
    assert_eq!(result.result, CheckResult::Valid);
    assert_eq!(result.theory_stats.verified_count, 0);
    assert_eq!(result.theory_stats.trusted_count, 0);
    assert_eq!(result.theory_stats.invalid_count, 0);
    assert_eq!(result.theory_stats.total(), 0);
}

// ===========================================================================
// 22. Lean5 export includes axioms
// ===========================================================================

#[test]
fn test_lean5_export_includes_axioms() {
    let t = make_trace_with_theory("EUF");
    let lean = export_lean5(&t).expect("Lean5 export should succeed");
    assert!(
        lean.contains("axiom theory_lemma_10_valid"),
        "should include axiom for theory lemma 10"
    );
    assert!(
        lean.contains("-- Theory: EUF (trusted)"),
        "should include theory annotation"
    );
    assert!(
        lean.contains("Theory lemmas (trusted axioms)"),
        "should include theory lemma section header"
    );
}

// ===========================================================================
// 23. Lean5 export includes resolution steps
// ===========================================================================

#[test]
fn test_lean5_export_includes_resolution_steps() {
    let t = make_simple_trace();
    let lean = export_lean5(&t).expect("Lean5 export should succeed");
    assert!(
        lean.contains("-- Resolution steps"),
        "should include resolution steps section"
    );
    assert!(
        lean.contains("theorem resolution_step_1"),
        "should include first resolution theorem"
    );
    assert!(
        lean.contains("theorem resolution_step_2"),
        "should include second resolution theorem"
    );
    assert!(lean.contains(":= by"), "should include tactic block");
    assert!(lean.contains("  decide"), "should include decide tactic");
}

// ===========================================================================
// 24. Lean5 syntax error detection (malformed identifier)
// ===========================================================================

#[test]
fn test_lean5_syntax_error_detection() {
    // Construct malformed Lean5 source with an invalid identifier.
    let bad_source = concat!(
        "-- Auto-generated by trust-vc-kernel\n",
        "abbrev Literal := Int\n",
        "def 123invalid : Clause := \u{27e8}[1]\u{27e9}\n",
        "theorem proof_valid : Clause.isEmpty clause_1 := by\n",
        "  decide\n",
    );
    let errs =
        validate_lean_syntax(bad_source).expect_err("malformed ident should cause syntax error");
    let ident_errors: Vec<_> = errs
        .iter()
        .filter(|e| e.message.contains("invalid identifier"))
        .collect();
    assert!(
        !ident_errors.is_empty(),
        "should detect invalid identifier in def declaration"
    );
}

// ===========================================================================
// 25. SMT-LIB2 export produces valid output
// ===========================================================================

#[test]
fn test_smtlib2_export_produces_valid_output() {
    let cert = make_simple_certificate();
    let bytes =
        export_certificate(&cert, ExportFormat::SmtLib2).expect("SMT-LIB2 export should succeed");
    let text = std::str::from_utf8(&bytes).expect("SMT-LIB2 output should be valid UTF-8");
    assert!(!text.is_empty(), "SMT-LIB2 output should be non-empty");
    // SMT-LIB2 format uses s-expressions.
    assert!(
        text.contains('(') && text.contains(')'),
        "SMT-LIB2 output should contain s-expressions"
    );
}

// ===========================================================================
// Additional tests beyond the requested 25
// ===========================================================================

#[test]
fn test_lean5_export_chain_proof_validates() {
    // Build a 10-step chain and verify full pipeline.
    let t = make_large_trace(10);
    assert_eq!(check_proof(&t), CheckResult::Valid);
    let lean = export_and_validate_lean5(&t);
    // Should have 11 resolution steps (10 chain + 1 final).
    let step_count = lean
        .lines()
        .filter(|l| l.trim().starts_with("theorem resolution_step_"))
        .count();
    assert_eq!(step_count, 11, "should have 11 resolution step theorems");
}

#[test]
fn test_theory_lemma_check_individual() {
    // Directly check individual theory lemmas using the public API.
    let euf_lemma = tl(1, "EUF", &[-1, -2, 3]);
    let result = check_theory_lemma(&euf_lemma);
    assert!(
        matches!(result, TheoryCheckResult::Verified),
        "EUF lemma with 1 positive literal should be verified"
    );

    let lra_lemma = tl(2, "LRA", &[-1, -2]);
    let result = check_theory_lemma(&lra_lemma);
    assert!(
        matches!(result, TheoryCheckResult::Verified),
        "LRA lemma with 2 literals should be verified"
    );

    let bv_lemma = tl(3, "BV", &[-1]);
    let result = check_theory_lemma(&bv_lemma);
    assert!(
        matches!(result, TheoryCheckResult::Trusted),
        "BV lemma should be trusted (no dedicated checker)"
    );
}

#[test]
fn test_wire_format_version_constant() {
    assert_eq!(CERTIFICATE_VERSION, 1, "current wire format version is 1");
}

#[test]
fn test_full_pipeline_with_theory_and_lean5() {
    // Build a proof with EUF theory, verify, export to all formats,
    // and validate the Lean5 output.
    let cert = make_certificate_with_theory("Euf");
    let t = make_trace_with_theory("EUF");

    // Proof check
    let result = check_proof_with_theory(&t);
    assert_eq!(result.result, CheckResult::Valid);
    assert_eq!(result.theory_stats.verified_count, 1);

    // JSON export + roundtrip
    let json = cert.to_json().expect("JSON serialization should succeed");
    let recovered =
        TrustVcProofCertificate::from_json(&json).expect("JSON deserialization should succeed");
    assert_eq!(cert, recovered);

    // Binary export + roundtrip
    let bytes = cert
        .to_bytes()
        .expect("binary serialization should succeed");
    let recovered_bin =
        TrustVcProofCertificate::from_bytes(&bytes).expect("binary deserialization should succeed");
    assert_eq!(cert, recovered_bin);

    // Lean5 export + syntax validation
    let lean = export_and_validate_lean5(&t);
    assert!(lean.contains("axiom theory_lemma_10_valid"));
    assert!(lean.contains("theorem proof_valid"));

    // Human-readable export
    let hr_bytes = export_certificate(&cert, ExportFormat::HumanReadable)
        .expect("human-readable export should succeed");
    let hr_text = std::str::from_utf8(&hr_bytes).expect("should be UTF-8");
    assert!(hr_text.contains("[T:EUF]"));

    // SMT-LIB2 export
    let smt_bytes =
        export_certificate(&cert, ExportFormat::SmtLib2).expect("SMT-LIB2 export should succeed");
    assert!(!smt_bytes.is_empty());
}

#[test]
fn test_certificate_hash_display() {
    let cert = make_simple_certificate();
    let source_hex = cert.source_hash_hex();
    assert_eq!(source_hex.len(), 64);
    assert!(source_hex.chars().all(|c| c.is_ascii_hexdigit()));
    // 0xAB repeated 32 times.
    assert_eq!(source_hex, "ab".repeat(32));

    let vc_hex = cert.vc_hash_hex();
    assert_eq!(vc_hex.len(), 64);
    assert_eq!(vc_hex, "cd".repeat(32));
}

#[test]
fn test_lean5_by_decide_pairing() {
    let t = make_simple_trace();
    let lean = export_and_validate_lean5(&t);

    let by_count = lean.lines().filter(|l| l.trim().ends_with(":= by")).count();
    let decide_count = lean.lines().filter(|l| l.trim() == "decide").count();
    assert_eq!(
        by_count, decide_count,
        ":= by count ({by_count}) should equal decide count ({decide_count})"
    );
}

#[test]
fn test_lean5_angle_bracket_balance() {
    let t = make_trace_with_theory("EUF");
    let lean = export_and_validate_lean5(&t);

    let open_count = lean.chars().filter(|&c| c == '\u{27e8}').count();
    let close_count = lean.chars().filter(|&c| c == '\u{27e9}').count();
    assert_eq!(
        open_count, close_count,
        "angle brackets unbalanced: {open_count} open vs {close_count} close"
    );
}
