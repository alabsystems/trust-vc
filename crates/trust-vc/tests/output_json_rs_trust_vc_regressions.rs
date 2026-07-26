// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the expanded upstream output_json.rs TrustVc scout slice.
//!
//! These tests intentionally keep the upstream file as an unsupported gap. They
//! prove only a narrow contract/report-adjacent surface and pin unsupported
//! Verus output-json proof-note/custom-error metadata as fail-closed extraction
//! boundaries. Solver Unknown is rejected as replacement evidence.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

type ExpectedCase = (&'static str, &'static str, &'static str, usize);

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn output_json_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/output_json.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_output_json_path() -> PathBuf {
    common::pinned_verus_test_path("output_json.rs")
}

fn port_source_and_ast() -> (String, syn::File) {
    let source =
        std::fs::read_to_string(output_json_port_path()).expect("output_json port should read");
    let ast = syn::parse_file(&source).expect("output_json port should parse");
    (source, ast)
}

fn find_port_function<'a>(ast: &'a syn::File, case: &str, upstream_case: &str) -> &'a syn::ItemFn {
    ast.items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(function) if function.sig.ident == case => Some(function),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} ({upstream_case}) should exist in output_json port"))
}

fn verify_port_case(case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let (_source, ast) = port_source_and_ast();
    let function = find_port_function(&ast, case, upstream_case);
    let vc = extract_verification_conditions_with_file_context(&ast, function)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
    let obligations = vc.obligations().len();
    (vc.verify(), obligations)
}

fn assert_not_unknown(case: &str, upstream_case: &str, result: &VerifyResult) {
    if let VerifyResult::Unknown { reason, .. } = result {
        panic!(
            "{case} ({upstream_case}) returned solver Unknown, which is not output_json.rs replacement evidence: {reason}"
        );
    }
}

fn fail_closed_message(case: &str, upstream_case: &str) -> String {
    let path = output_json_port_path();
    let path = path
        .to_str()
        .expect("output_json port path should be UTF-8");
    match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable fail-closed evidence: {reason}")
        }
        Ok(other) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
        }
    }
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("output_json port should define {const_name}"));

    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("{const_name} should be a referenced array");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("{const_name} should reference an array");
    };
    array.clone()
}

fn parse_output_json_expected_cases_from_source(source: &str) -> Vec<ExpectedCase> {
    let ast = syn::parse_file(source).expect("output_json port should parse");
    let array = referenced_array_const(&ast, "OUTPUT_JSON_RS_EXPECTED_CASES");

    array
        .elems
        .iter()
        .map(|expr| {
            let syn::Expr::Tuple(tuple) = expr else {
                panic!("OUTPUT_JSON_RS_EXPECTED_CASES entries should be tuples");
            };
            assert_eq!(
                tuple.elems.len(),
                4,
                "OUTPUT_JSON_RS_EXPECTED_CASES entries should have four fields"
            );

            let case = string_lit(&tuple.elems[0]);
            let upstream_case = string_lit(&tuple.elems[1]);
            let status = string_lit(&tuple.elems[2]);
            let min_obligations = usize_lit(&tuple.elems[3]);

            (
                leak_string(case),
                leak_string(upstream_case),
                leak_string(status),
                min_obligations,
            )
        })
        .collect()
}

fn string_slice(expr: &syn::Expr) -> Vec<String> {
    let syn::Expr::Reference(reference) = expr else {
        panic!("expected referenced string-slice metadata");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("expected string-slice array metadata");
    };

    array.elems.iter().map(string_lit).collect()
}

fn error_pattern_entries(file: &syn::File) -> BTreeMap<String, Vec<String>> {
    let array = referenced_array_const(file, "OUTPUT_JSON_RS_EXPECTED_ERROR_PATTERNS");
    let mut entries = BTreeMap::new();

    for entry in &array.elems {
        let syn::Expr::Tuple(tuple) = entry else {
            panic!("expected tuple error-pattern metadata entry");
        };
        assert_eq!(
            tuple.elems.len(),
            2,
            "error-pattern entries should have case and fragments"
        );

        let case_id = string_lit(&tuple.elems[0]);
        let patterns = string_slice(&tuple.elems[1]);
        assert!(
            entries.insert(case_id.clone(), patterns).is_none(),
            "duplicate output_json error-pattern metadata for {case_id}"
        );
    }

    entries
}

fn metadata_entries(file: &syn::File) -> Vec<CaseMetadata> {
    let array = referenced_array_const(file, "OUTPUT_JSON_RS_EXPECTED_CASES");
    let mut error_patterns = error_pattern_entries(file);
    let mut seen = BTreeSet::new();
    let mut entries = Vec::new();

    for entry in &array.elems {
        let syn::Expr::Tuple(tuple) = entry else {
            panic!("expected tuple expected-case metadata entry");
        };
        assert_eq!(
            tuple.elems.len(),
            4,
            "expected-case entries should have case, upstream case, verdict, and min obligations"
        );
        let case_id = string_lit(&tuple.elems[0]);
        assert!(
            seen.insert(case_id.clone()),
            "duplicate output_json metadata for {case_id}"
        );
        let expected_error_patterns = error_patterns.remove(&case_id).unwrap_or_default();
        entries.push(CaseMetadata {
            case_id,
            upstream_case_id: string_lit(&tuple.elems[1]),
            expected_verdict: string_lit(&tuple.elems[2]),
            min_obligations: usize_lit(&tuple.elems[3]),
            expected_error_patterns,
        });
    }

    assert!(
        error_patterns.is_empty(),
        "error-pattern metadata should not contain orphan cases: {error_patterns:?}"
    );
    entries
}

fn manifest_expected_metadata() -> Vec<CaseMetadata> {
    let source =
        std::fs::read_to_string(verus_manifest_path()).expect("Verus manifest should be readable");
    let manifest: serde_json::Value =
        serde_json::from_str(&source).expect("Verus manifest should parse as JSON");
    let row = manifest["entries"]
        .as_array()
        .expect("Verus manifest should contain entries")
        .iter()
        .find(|entry| {
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/output_json.rs")
        })
        .expect("Verus manifest should contain output_json.rs row");

    row["expected_cases"]
        .as_array()
        .expect("output_json.rs row should contain expected_cases")
        .iter()
        .map(|entry| CaseMetadata {
            case_id: entry["case_id"]
                .as_str()
                .expect("case_id should be a string")
                .to_string(),
            upstream_case_id: entry["upstream_case_id"]
                .as_str()
                .expect("upstream_case_id should be a string")
                .to_string(),
            expected_verdict: entry["expected_verdict"]
                .as_str()
                .expect("expected_verdict should be a string")
                .to_string(),
            min_obligations: entry["min_obligations"]
                .as_u64()
                .expect("min_obligations should be an integer")
                as usize,
            expected_error_patterns: entry
                .get("expected_error_patterns")
                .and_then(serde_json::Value::as_array)
                .map(|patterns| {
                    patterns
                        .iter()
                        .map(|pattern| {
                            pattern
                                .as_str()
                                .expect("expected_error_patterns values should be strings")
                                .to_string()
                        })
                        .collect()
                })
                .unwrap_or_default(),
        })
        .collect()
}

fn expected_metadata() -> Vec<CaseMetadata> {
    let mut error_patterns = FAIL_CLOSED_CASES
        .iter()
        .map(|(case_id, _, patterns)| {
            (
                *case_id,
                patterns
                    .iter()
                    .map(|pattern| (*pattern).to_string())
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<BTreeMap<_, _>>();

    let entries = EXPECTED_CASES
        .iter()
        .map(
            |(case_id, upstream_case_id, expected_verdict, min_obligations)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: (*expected_verdict).to_string(),
                min_obligations: *min_obligations,
                expected_error_patterns: error_patterns.remove(*case_id).unwrap_or_default(),
            },
        )
        .collect();

    assert!(
        error_patterns.is_empty(),
        "expected error-pattern metadata should not contain orphan cases: {error_patterns:?}"
    );
    entries
}

fn leak_string(value: String) -> &'static str {
    Box::leak(value.into_boxed_str())
}

fn string_lit(expr: &syn::Expr) -> String {
    let syn::Expr::Lit(lit) = expr else {
        panic!("expected string literal in output_json expected-case metadata");
    };
    let syn::Lit::Str(value) = &lit.lit else {
        panic!("expected string literal in output_json expected-case metadata");
    };
    value.value()
}

fn usize_lit(expr: &syn::Expr) -> usize {
    let syn::Expr::Lit(lit) = expr else {
        panic!("expected usize literal in output_json expected-case metadata");
    };
    let syn::Lit::Int(value) = &lit.lit else {
        panic!("expected usize literal in output_json expected-case metadata");
    };
    value
        .base10_parse()
        .expect("output_json expected-case min obligation should parse")
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum InventoryStatus {
    Verified,
    Counterexample,
    Error,
    LocalBlocker,
}

#[derive(Clone, Copy, Debug)]
struct OutputJsonCaseInventory {
    case: Option<&'static str>,
    upstream_case: &'static str,
    status: InventoryStatus,
    blocker: &'static str,
}

const UPSTREAM_CASES: &[&str] = &[
    "test_json_proof_note_on_requires",
    "test_json_proof_note_on_ensures",
    "test_json_custom_err_on_ensures",
    "test_json_proof_note_on_assert",
    "test_json_custom_err_on_assert",
    "test_json_proof_note_on_assume_with_no_cheating",
    "test_json_custom_err_on_assume_with_no_cheating",
    "test_json_custom_err_on_requires",
    "test_json_proof_note_on_assume_and_req_with_no_cheating",
];

const CASE_INVENTORY: &[OutputJsonCaseInventory] = &[
    OutputJsonCaseInventory {
        case: Some("output_json_requires_ensures_report_verified"),
        upstream_case: "test_json_proof_note_on_requires",
        status: InventoryStatus::Verified,
        blocker: "",
    },
    OutputJsonCaseInventory {
        case: Some("output_json_requires_obligation_counterexample"),
        upstream_case: "test_json_proof_note_on_requires",
        status: InventoryStatus::Counterexample,
        blocker: "",
    },
    OutputJsonCaseInventory {
        case: Some("output_json_second_requires_obligation_counterexample"),
        upstream_case: "test_json_proof_note_on_requires",
        status: InventoryStatus::Counterexample,
        blocker: "",
    },
    OutputJsonCaseInventory {
        case: Some("output_json_two_ensures_report_verified"),
        upstream_case: "test_json_proof_note_on_ensures",
        status: InventoryStatus::Verified,
        blocker: "",
    },
    OutputJsonCaseInventory {
        case: Some("output_json_ensures_obligation_counterexample"),
        upstream_case: "test_json_proof_note_on_ensures",
        status: InventoryStatus::Counterexample,
        blocker: "",
    },
    OutputJsonCaseInventory {
        case: Some("output_json_two_ensures_obligation_counterexample"),
        upstream_case: "test_json_proof_note_on_ensures",
        status: InventoryStatus::Counterexample,
        blocker: "",
    },
    OutputJsonCaseInventory {
        case: Some("output_json_custom_error_ensures_report_verified"),
        upstream_case: "test_json_custom_err_on_ensures",
        status: InventoryStatus::Verified,
        blocker: "",
    },
    OutputJsonCaseInventory {
        case: Some("output_json_custom_error_ensures_obligation_counterexample"),
        upstream_case: "test_json_custom_err_on_ensures",
        status: InventoryStatus::Counterexample,
        blocker: "",
    },
    OutputJsonCaseInventory {
        case: Some("output_json_assert_obligation_counterexample"),
        upstream_case: "test_json_proof_note_on_assert",
        status: InventoryStatus::Counterexample,
        blocker: "",
    },
    OutputJsonCaseInventory {
        case: Some("output_json_proof_note_metadata_fails_closed"),
        upstream_case: "test_json_proof_note_on_assert",
        status: InventoryStatus::Error,
        blocker: "Verus proof_note JSON metadata is rejected before verification",
    },
    OutputJsonCaseInventory {
        case: Some("output_json_custom_error_assert_obligation_counterexample"),
        upstream_case: "test_json_custom_err_on_assert",
        status: InventoryStatus::Counterexample,
        blocker: "",
    },
    OutputJsonCaseInventory {
        case: Some("output_json_custom_error_metadata_fails_closed"),
        upstream_case: "test_json_custom_err_on_assert",
        status: InventoryStatus::Error,
        blocker: "Verus custom_err diagnostic metadata is rejected before verification",
    },
    OutputJsonCaseInventory {
        case: Some("output_json_no_cheating_assume_only_boundary_errors"),
        upstream_case: "test_json_proof_note_on_assume_with_no_cheating",
        status: InventoryStatus::Error,
        blocker: "TrustVc has no Verus --output-json no-cheating failed-note report",
    },
    OutputJsonCaseInventory {
        case: Some("output_json_custom_error_no_cheating_metadata_fails_closed"),
        upstream_case: "test_json_custom_err_on_assume_with_no_cheating",
        status: InventoryStatus::Error,
        blocker: "TrustVc rejects no-cheating/custom_err JSON metadata instead of reporting it",
    },
    OutputJsonCaseInventory {
        case: Some("output_json_custom_error_requires_report_verified"),
        upstream_case: "test_json_custom_err_on_requires",
        status: InventoryStatus::Verified,
        blocker: "",
    },
    OutputJsonCaseInventory {
        case: Some("output_json_custom_error_requires_obligation_counterexample"),
        upstream_case: "test_json_custom_err_on_requires",
        status: InventoryStatus::Counterexample,
        blocker: "",
    },
    OutputJsonCaseInventory {
        case: Some("output_json_no_cheating_metadata_fails_closed"),
        upstream_case: "test_json_proof_note_on_assume_and_req_with_no_cheating",
        status: InventoryStatus::Error,
        blocker: "TrustVc rejects no-cheating/proof_note JSON metadata instead of reporting it",
    },
    OutputJsonCaseInventory {
        case: None,
        upstream_case: "test_json_proof_note_on_assume_and_req_with_no_cheating",
        status: InventoryStatus::LocalBlocker,
        blocker: "combined failed requires plus failed no-cheating assumption JSON detail sets are not mirrored",
    },
];

const EXPECTED_CASES: &[ExpectedCase] = &[
    (
        "output_json_requires_ensures_report_verified",
        "test_json_proof_note_on_requires",
        "verified",
        2,
    ),
    (
        "output_json_two_ensures_report_verified",
        "test_json_proof_note_on_ensures",
        "verified",
        3,
    ),
    (
        "output_json_custom_error_requires_report_verified",
        "test_json_custom_err_on_requires",
        "verified",
        2,
    ),
    (
        "output_json_custom_error_ensures_report_verified",
        "test_json_custom_err_on_ensures",
        "verified",
        1,
    ),
    (
        "output_json_requires_obligation_counterexample",
        "test_json_proof_note_on_requires",
        "counterexample",
        1,
    ),
    (
        "output_json_second_requires_obligation_counterexample",
        "test_json_proof_note_on_requires",
        "counterexample",
        2,
    ),
    (
        "output_json_ensures_obligation_counterexample",
        "test_json_proof_note_on_ensures",
        "counterexample",
        1,
    ),
    (
        "output_json_two_ensures_obligation_counterexample",
        "test_json_proof_note_on_ensures",
        "counterexample",
        2,
    ),
    (
        "output_json_custom_error_requires_obligation_counterexample",
        "test_json_custom_err_on_requires",
        "counterexample",
        1,
    ),
    (
        "output_json_custom_error_ensures_obligation_counterexample",
        "test_json_custom_err_on_ensures",
        "counterexample",
        1,
    ),
    (
        "output_json_assert_obligation_counterexample",
        "test_json_proof_note_on_assert",
        "counterexample",
        1,
    ),
    (
        "output_json_custom_error_assert_obligation_counterexample",
        "test_json_custom_err_on_assert",
        "counterexample",
        1,
    ),
    (
        "output_json_no_cheating_assume_only_boundary_errors",
        "test_json_proof_note_on_assume_with_no_cheating",
        "error",
        1,
    ),
    (
        "output_json_proof_note_metadata_fails_closed",
        "test_json_proof_note_on_assert",
        "error",
        0,
    ),
    (
        "output_json_custom_error_metadata_fails_closed",
        "test_json_custom_err_on_assert",
        "error",
        0,
    ),
    (
        "output_json_no_cheating_metadata_fails_closed",
        "test_json_proof_note_on_assume_and_req_with_no_cheating",
        "error",
        0,
    ),
    (
        "output_json_custom_error_no_cheating_metadata_fails_closed",
        "test_json_custom_err_on_assume_with_no_cheating",
        "error",
        0,
    ),
];

const VERIFIED_CASES: &[ExpectedCase] = &[
    (
        "output_json_requires_ensures_report_verified",
        "test_json_proof_note_on_requires",
        "verified",
        2,
    ),
    (
        "output_json_two_ensures_report_verified",
        "test_json_proof_note_on_ensures",
        "verified",
        3,
    ),
    (
        "output_json_custom_error_requires_report_verified",
        "test_json_custom_err_on_requires",
        "verified",
        2,
    ),
    (
        "output_json_custom_error_ensures_report_verified",
        "test_json_custom_err_on_ensures",
        "verified",
        1,
    ),
];

const COUNTEREXAMPLE_CASES: &[ExpectedCase] = &[
    (
        "output_json_requires_obligation_counterexample",
        "test_json_proof_note_on_requires",
        "counterexample",
        1,
    ),
    (
        "output_json_second_requires_obligation_counterexample",
        "test_json_proof_note_on_requires",
        "counterexample",
        2,
    ),
    (
        "output_json_ensures_obligation_counterexample",
        "test_json_proof_note_on_ensures",
        "counterexample",
        1,
    ),
    (
        "output_json_two_ensures_obligation_counterexample",
        "test_json_proof_note_on_ensures",
        "counterexample",
        2,
    ),
    (
        "output_json_custom_error_requires_obligation_counterexample",
        "test_json_custom_err_on_requires",
        "counterexample",
        1,
    ),
    (
        "output_json_custom_error_ensures_obligation_counterexample",
        "test_json_custom_err_on_ensures",
        "counterexample",
        1,
    ),
    (
        "output_json_assert_obligation_counterexample",
        "test_json_proof_note_on_assert",
        "counterexample",
        1,
    ),
    (
        "output_json_custom_error_assert_obligation_counterexample",
        "test_json_custom_err_on_assert",
        "counterexample",
        1,
    ),
];

const ERROR_RESULT_CASES: &[(&str, &str, usize, &[&str])] = &[(
    "output_json_no_cheating_assume_only_boundary_errors",
    "test_json_proof_note_on_assume_with_no_cheating",
    1,
    &["only assumptions and no assertions"],
)];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "output_json_proof_note_metadata_fails_closed",
        "test_json_proof_note_on_assert",
        &["unknown contract clause `output_json` in #[contract]"],
    ),
    (
        "output_json_custom_error_metadata_fails_closed",
        "test_json_custom_err_on_assert",
        &["unknown contract clause `custom_err` in #[contract]"],
    ),
    (
        "output_json_no_cheating_metadata_fails_closed",
        "test_json_proof_note_on_assume_and_req_with_no_cheating",
        &["unknown contract clause `no_cheating` in #[contract]"],
    ),
    (
        "output_json_custom_error_no_cheating_metadata_fails_closed",
        "test_json_custom_err_on_assume_with_no_cheating",
        &["unknown contract clause `no_cheating` in #[contract]"],
    ),
];

#[test]
fn output_json_rs_port_file_is_rust_syntax() {
    let (source, _ast) = port_source_and_ast();
    syn::parse_file(&source).expect("output_json port should parse as ordinary Rust syntax");
    assert!(
        source.contains("OUTPUT_JSON_RS_EXPECTED_CASES")
            && source.contains("output_json_rs_expected_cases")
            && source.contains("OUTPUT_JSON_RS_EXPECTED_ERROR_PATTERNS")
            && source.contains("output_json_rs_expected_error_patterns"),
        "output_json scout should carry expected-case metadata helpers"
    );
}

#[test]
fn output_json_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_output_json_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream output_json.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    let mut previous = 0;
    for upstream_case in UPSTREAM_CASES {
        let current = source.find(upstream_case).unwrap_or_else(|| {
            panic!("pinned upstream output_json.rs should contain {upstream_case}")
        });
        assert!(
            current >= previous,
            "upstream output_json.rs case {upstream_case} should stay in pinned order"
        );
        previous = current;
    }

    assert_eq!(
        source.matches("[\"--output-json\"").count(),
        9,
        "upstream output_json.rs should keep nine output-json test cases"
    );
    assert_eq!(
        source.matches("\"--no-cheating\"").count(),
        3,
        "upstream output_json.rs should keep three no-cheating cases"
    );
    assert_eq!(
        source.matches("verifier::proof_note").count(),
        8,
        "upstream output_json.rs proof_note annotation count should stay pinned"
    );
    assert_eq!(
        source.matches("verifier::custom_err").count(),
        4,
        "upstream output_json.rs custom_err annotation count should stay pinned"
    );
    assert_eq!(
        source.matches("with_json_func_details").count(),
        13,
        "upstream output_json.rs func-details assertion count should stay pinned"
    );
    assert!(
        source.contains("pub obligation_proof_notes: HashSet<String>")
            && source.contains("pub failed_proof_notes: HashSet<String>"),
        "upstream output_json.rs should still deserialize func-details proof-note sets"
    );
}

#[test]
fn output_json_rs_expected_case_inventory_is_manifest_ready() {
    let (source, ast) = port_source_and_ast();
    let parsed_cases = parse_output_json_expected_cases_from_source(&source);
    assert_eq!(parsed_cases, EXPECTED_CASES);
    assert_eq!(metadata_entries(&ast), expected_metadata());

    for (case, upstream_case, status, min_obligations) in EXPECTED_CASES {
        assert!(
            matches!(*status, "verified" | "counterexample" | "error"),
            "{case} ({upstream_case}) has non-schema evidence status {status}"
        );
        assert_ne!(
            *status, "unknown",
            "{case} ({upstream_case}) must not inventory Unknown as evidence"
        );

        let found = ast.items.iter().any(|item| match item {
            syn::Item::Fn(function) => function.sig.ident == *case,
            _ => false,
        });
        assert!(found, "{case} should remain an explicit port witness");

        if *status != "error" || *min_obligations > 0 {
            assert!(
                *min_obligations >= 1,
                "{case} ({upstream_case}) should have a positive minimum obligation count"
            );
        }
    }
}

#[test]
fn output_json_rs_expected_case_metadata_matches_manifest() {
    let (_source, ast) = port_source_and_ast();
    assert_eq!(metadata_entries(&ast), manifest_expected_metadata());
}

#[test]
fn output_json_rs_expected_case_inventory_covers_upstream_cases() {
    assert_eq!(
        UPSTREAM_CASES.len(),
        9,
        "upstream output_json.rs active case count should stay pinned"
    );

    for upstream_case in UPSTREAM_CASES {
        assert!(
            CASE_INVENTORY
                .iter()
                .any(|case| case.upstream_case == *upstream_case),
            "{upstream_case} should remain represented in the local inventory"
        );
    }

    for case in CASE_INVENTORY {
        if case.status == InventoryStatus::LocalBlocker {
            assert!(
                case.case.is_none() && !case.blocker.is_empty(),
                "local blockers should not masquerade as manifest-ready evidence"
            );
        }

        if matches!(
            case.status,
            InventoryStatus::Verified | InventoryStatus::Counterexample
        ) {
            assert!(
                case.blocker.is_empty(),
                "{:?} should not carry blocker text",
                case
            );
        }
    }
}

#[test]
fn output_json_rs_report_adjacent_verified_subset_verifies_from_file() {
    for (case, upstream_case, _status, min_obligations) in VERIFIED_CASES {
        let (result, obligations) = verify_port_case(case, upstream_case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert_not_unknown(case, upstream_case, &result);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn output_json_rs_report_adjacent_counterexamples_from_file() {
    for (case, upstream_case, _status, min_obligations) in COUNTEREXAMPLE_CASES {
        let (result, obligations) = verify_port_case(case, upstream_case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert_not_unknown(case, upstream_case, &result);
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

#[test]
fn output_json_rs_no_cheating_assume_boundary_errors_from_file() {
    for (case, upstream_case, min_obligations, expected_fragments) in ERROR_RESULT_CASES {
        let (result, obligations) = verify_port_case(case, upstream_case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert_not_unknown(case, upstream_case, &result);
        let VerifyResult::Error { message } = result else {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {result:?}");
        };
        assert!(
            expected_fragments
                .iter()
                .any(|expected_fragment| message.contains(expected_fragment)),
            "{case} ({upstream_case}) error should contain one of {expected_fragments:?}, got: {message}"
        );
    }
}

#[test]
fn output_json_rs_unsupported_metadata_boundary_fails_closed_from_file() {
    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        let message = fail_closed_message(case, upstream_case);
        assert!(
            expected_fragments
                .iter()
                .any(|expected_fragment| message.contains(expected_fragment)),
            "{case} ({upstream_case}) error should contain one of {expected_fragments:?}, got: {message}"
        );
    }
}
