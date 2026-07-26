// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the currently ported upstream basic.rs subset.
//!
//! These tests intentionally do not claim full Verus basic.rs parity. They
//! prove that the listed upstream-derived slices execute through TrustVc while
//! the manifest keeps `source/rust_verify_test/tests/basic.rs` fail-closed.

use std::{collections::BTreeSet, path::PathBuf};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn basic_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/basic.rs")
}

fn verus_manifest_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

struct CaseExpectation {
    case_id: &'static str,
    upstream_case_id: &'static str,
    min_obligations: usize,
}

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
}

const VERIFIED_CASES: &[CaseExpectation] = &[
    CaseExpectation {
        case_id: "test1",
        upstream_case_id: "test1",
        min_obligations: 1,
    },
    CaseExpectation {
        case_id: "test2",
        upstream_case_id: "test2",
        min_obligations: 1,
    },
    CaseExpectation {
        case_id: "bool_xor",
        upstream_case_id: "bool_xor",
        min_obligations: 4,
    },
    CaseExpectation {
        case_id: "test_exec_fun1",
        upstream_case_id: "test_exec_fun1",
        min_obligations: 1,
    },
    CaseExpectation {
        case_id: "test_short_circuit_and",
        upstream_case_id: "test_short_circuit",
        min_obligations: 2,
    },
    CaseExpectation {
        case_id: "test_short_circuit_or",
        upstream_case_id: "test_short_circuit",
        min_obligations: 2,
    },
    CaseExpectation {
        case_id: "test_decl_init_let_pass",
        upstream_case_id: "test_decl_init_let_pass",
        min_obligations: 1,
    },
    CaseExpectation {
        case_id: "test_paren",
        upstream_case_id: "test_paren",
        min_obligations: 1,
    },
    CaseExpectation {
        case_id: "test_mut_param_exec_preserves_original",
        upstream_case_id: "test_mut_param",
        min_obligations: 1,
    },
];

const COUNTEREXAMPLE_CASES: &[CaseExpectation] = &[
    CaseExpectation {
        case_id: "test1_fails",
        upstream_case_id: "test1_fails",
        min_obligations: 1,
    },
    CaseExpectation {
        case_id: "test2_fails",
        upstream_case_id: "test2_fails",
        min_obligations: 1,
    },
    CaseExpectation {
        case_id: "test_assign",
        upstream_case_id: "test_assign",
        min_obligations: 1,
    },
    CaseExpectation {
        case_id: "test_assign_mut",
        upstream_case_id: "test_assign_mut",
        min_obligations: 1,
    },
    CaseExpectation {
        case_id: "bool_xor_fails",
        upstream_case_id: "bool_xor_fails",
        min_obligations: 1,
    },
    CaseExpectation {
        case_id: "bool_xor_fails_false_true",
        upstream_case_id: "bool_xor_fails",
        min_obligations: 1,
    },
    CaseExpectation {
        case_id: "bool_xor_fails_true_false",
        upstream_case_id: "bool_xor_fails",
        min_obligations: 1,
    },
    CaseExpectation {
        case_id: "bool_xor_fails_false_false",
        upstream_case_id: "bool_xor_fails",
        min_obligations: 1,
    },
    CaseExpectation {
        case_id: "test_short_circuit2",
        upstream_case_id: "test_short_circuit2",
        min_obligations: 2,
    },
    CaseExpectation {
        case_id: "test_short_circuit3",
        upstream_case_id: "test_short_circuit3",
        min_obligations: 2,
    },
    CaseExpectation {
        case_id: "test_mut_param_exec_wrong_postcondition",
        upstream_case_id: "test_mut_param",
        min_obligations: 1,
    },
];

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("basic port should define {const_name}"));

    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("{const_name} should be a referenced array");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("{const_name} should reference an array");
    };
    array.clone()
}

fn literal_string(expr: &syn::Expr) -> String {
    let syn::Expr::Lit(lit) = expr else {
        panic!("expected string literal");
    };
    let syn::Lit::Str(value) = &lit.lit else {
        panic!("expected string literal");
    };
    value.value()
}

fn literal_usize(expr: &syn::Expr) -> usize {
    let syn::Expr::Lit(lit) = expr else {
        panic!("expected integer literal");
    };
    let syn::Lit::Int(value) = &lit.lit else {
        panic!("expected integer literal");
    };
    value
        .base10_parse()
        .expect("min obligations should be a usize literal")
}

fn metadata_entries(file: &syn::File) -> Vec<CaseMetadata> {
    let array = referenced_array_const(file, "BASIC_RS_EXPECTED_CASES");
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
        let case_id = literal_string(&tuple.elems[0]);
        assert!(
            seen.insert(case_id.clone()),
            "duplicate basic metadata for {case_id}"
        );
        entries.push(CaseMetadata {
            case_id,
            upstream_case_id: literal_string(&tuple.elems[1]),
            expected_verdict: literal_string(&tuple.elems[2]),
            min_obligations: literal_usize(&tuple.elems[3]),
        });
    }

    entries
}

fn expected_metadata() -> Vec<CaseMetadata> {
    let verified = VERIFIED_CASES.iter().map(|case| CaseMetadata {
        case_id: case.case_id.to_string(),
        upstream_case_id: case.upstream_case_id.to_string(),
        expected_verdict: "verified".to_string(),
        min_obligations: case.min_obligations,
    });
    let counterexamples = COUNTEREXAMPLE_CASES.iter().map(|case| CaseMetadata {
        case_id: case.case_id.to_string(),
        upstream_case_id: case.upstream_case_id.to_string(),
        expected_verdict: "counterexample".to_string(),
        min_obligations: case.min_obligations,
    });

    verified.chain(counterexamples).collect()
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/basic.rs")
        })
        .expect("Verus manifest should contain basic.rs row");

    row["expected_cases"]
        .as_array()
        .expect("basic.rs row should contain expected_cases")
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
        })
        .collect()
}

fn verify_port_case(case: &CaseExpectation) -> (VerifyResult, usize) {
    let path = basic_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("basic port should read: {err}"));
    let file =
        syn::parse_file(&source).unwrap_or_else(|err| panic!("basic port should parse: {err}"));
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == case.case_id => Some(func),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{} should exist in basic port", case.case_id));

    let vc = extract_verification_conditions_with_file_context(&file, func).unwrap_or_else(|err| {
        panic!(
            "{} ({}) should extract: {err}",
            case.case_id, case.upstream_case_id
        )
    });
    let obligation_count = vc.obligations().len();
    (vc.verify(), obligation_count)
}

#[test]
fn basic_rs_expected_case_metadata_is_exact() {
    let source = std::fs::read_to_string(basic_port_path()).expect("basic port should be readable");
    let file = syn::parse_file(&source).expect("basic port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
}

#[test]
fn basic_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(basic_port_path()).expect("basic port should be readable");
    let file = syn::parse_file(&source).expect("basic port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn basic_rs_verified_subset_verifies_from_file() {
    for case in VERIFIED_CASES {
        let (result, obligations) = verify_port_case(case);
        assert!(
            obligations >= case.min_obligations,
            "{} ({}) should collect at least {} obligation(s), got {obligations}",
            case.case_id,
            case.upstream_case_id,
            case.min_obligations
        );
        assert!(
            matches!(result, VerifyResult::Verified),
            "{} ({}) should verify, got: {result:?}",
            case.case_id,
            case.upstream_case_id
        );
    }
}

#[test]
fn basic_rs_counterexample_subset_is_rejected_from_file() {
    for case in COUNTEREXAMPLE_CASES {
        let (result, obligations) = verify_port_case(case);
        assert!(
            obligations >= case.min_obligations,
            "{} ({}) should collect at least {} obligation(s), got {obligations}",
            case.case_id,
            case.upstream_case_id,
            case.min_obligations
        );
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{} ({}) should be rejected, got: {result:?}",
            case.case_id,
            case.upstream_case_id
        );
    }
}

#[test]
fn basic_rs_verify_function_from_file_entrypoint_still_covers_representative_cases() {
    let path = basic_port_path();
    let path = path.to_str().expect("basic port path should be UTF-8");

    for case in [
        &VERIFIED_CASES[0],
        &VERIFIED_CASES[4],
        &COUNTEREXAMPLE_CASES[0],
        &COUNTEREXAMPLE_CASES[8],
    ] {
        let result = verify_function_from_file(path, case.case_id).unwrap_or_else(|err| {
            panic!(
                "{} ({}) should extract through verify_function_from_file: {err}",
                case.case_id, case.upstream_case_id
            )
        });
        assert!(
            matches!(
                (&result, case.case_id),
                (VerifyResult::Verified, "test1" | "test_short_circuit_and")
                    | (
                        VerifyResult::Counterexample { .. },
                        "test1_fails" | "test_short_circuit2"
                    )
            ),
            "{} ({}) had unexpected verify_function_from_file result: {result:?}",
            case.case_id,
            case.upstream_case_id
        );
    }
}
