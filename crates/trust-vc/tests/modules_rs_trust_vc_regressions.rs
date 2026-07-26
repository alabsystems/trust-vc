// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the current upstream modules.rs TrustVc scout slice.
//!
//! These tests intentionally keep the upstream file as an unsupported gap. They
//! pin Rust-valid module ADT/helper evidence that TrustVc can verify today,
//! reject stable false claims in the same module-shaped contexts, and keep
//! unsupported Verus module spec-function visibility/reveal, mode, and
//! Verus-only syntax surfaces fail-closed.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

#[derive(Debug, Eq, PartialEq)]
struct ExpectedCaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn modules_port_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/modules.rs")
}

fn pinned_upstream_modules_path() -> PathBuf {
    common::pinned_verus_test_path("modules.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn verify_port_case(case: &str, upstream_case: &str) -> (VerifyResult, usize) {
    let path = modules_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("modules port should read: {err}"));
    let file =
        syn::parse_file(&source).unwrap_or_else(|err| panic!("modules port should parse: {err}"));
    let function = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(function) if function.sig.ident == case => Some(function),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} ({upstream_case}) should exist in modules port"));

    let vc = extract_verification_conditions_with_file_context(&file, function)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
    let obligation_count = vc.obligations().len();
    (vc.verify(), obligation_count)
}

fn modules_port_file() -> syn::File {
    let source =
        std::fs::read_to_string(modules_port_path()).expect("modules port should be readable");
    syn::parse_file(&source).expect("modules port should parse as ordinary Rust syntax")
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item_const) if item_const.ident == const_name => Some(item_const),
            _ => None,
        })
        .unwrap_or_else(|| panic!("modules port should expose {const_name}"));
    let syn::Expr::Reference(reference) = const_item.expr.as_ref() else {
        panic!("{const_name} should be a borrowed array literal");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("{const_name} should be a borrowed array literal");
    };

    array.clone()
}

fn string_literal(expr: &syn::Expr, field: &str) -> String {
    let syn::Expr::Lit(expr_lit) = expr else {
        panic!("MODULES_RS_EXPECTED_CASES {field} should be a string literal");
    };
    let syn::Lit::Str(lit) = &expr_lit.lit else {
        panic!("MODULES_RS_EXPECTED_CASES {field} should be a string literal");
    };
    lit.value()
}

fn usize_literal(expr: &syn::Expr, field: &str) -> usize {
    let syn::Expr::Lit(expr_lit) = expr else {
        panic!("MODULES_RS_EXPECTED_CASES {field} should be a usize literal");
    };
    let syn::Lit::Int(lit) = &expr_lit.lit else {
        panic!("MODULES_RS_EXPECTED_CASES {field} should be a usize literal");
    };
    lit.base10_parse::<usize>()
        .unwrap_or_else(|err| panic!("MODULES_RS_EXPECTED_CASES {field} should parse: {err}"))
}

fn string_slice(expr: &syn::Expr) -> Vec<String> {
    let syn::Expr::Reference(reference) = expr else {
        panic!("expected referenced string-slice metadata");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("expected string-slice array metadata");
    };

    array
        .elems
        .iter()
        .map(|expr| string_literal(expr, "expected_error_patterns"))
        .collect()
}

fn expected_error_patterns_from_port(file: &syn::File) -> BTreeMap<String, Vec<String>> {
    let array = referenced_array_const(file, "MODULES_RS_EXPECTED_ERROR_PATTERNS");
    let mut entries = BTreeMap::new();

    for elem in &array.elems {
        let syn::Expr::Tuple(tuple) = elem else {
            panic!("MODULES_RS_EXPECTED_ERROR_PATTERNS entries should be tuples");
        };
        assert_eq!(
            tuple.elems.len(),
            2,
            "MODULES_RS_EXPECTED_ERROR_PATTERNS entries should be (case, patterns)"
        );
        let case_id = string_literal(&tuple.elems[0], "case_id");
        let patterns = string_slice(&tuple.elems[1]);
        assert!(
            entries.insert(case_id.clone(), patterns).is_none(),
            "duplicate expected error patterns for {case_id}"
        );
    }

    entries
}

fn expected_case_metadata_from_port(file: &syn::File) -> Vec<ExpectedCaseMetadata> {
    let array = referenced_array_const(file, "MODULES_RS_EXPECTED_CASES");
    let mut error_patterns = expected_error_patterns_from_port(file);

    let entries = array
        .elems
        .iter()
        .map(|elem| {
            let syn::Expr::Tuple(tuple) = elem else {
                panic!("MODULES_RS_EXPECTED_CASES entries should be tuples");
            };
            assert_eq!(
                tuple.elems.len(),
                4,
                "MODULES_RS_EXPECTED_CASES entries should be (case, upstream, verdict, min_obligations)"
            );
            let case_id = string_literal(&tuple.elems[0], "case_id");
            ExpectedCaseMetadata {
                expected_error_patterns: error_patterns.remove(&case_id).unwrap_or_default(),
                case_id,
                upstream_case_id: string_literal(&tuple.elems[1], "upstream_case_id"),
                expected_verdict: string_literal(&tuple.elems[2], "expected_verdict"),
                min_obligations: usize_literal(&tuple.elems[3], "min_obligations"),
            }
        })
        .collect::<Vec<_>>();
    assert!(
        error_patterns.is_empty(),
        "error-pattern metadata should not contain orphan cases: {error_patterns:?}"
    );
    entries
}

fn expected_case_metadata_from_tests() -> Vec<ExpectedCaseMetadata> {
    VERIFIED_CASES
        .iter()
        .map(
            |(case_id, upstream_case_id, min_obligations)| ExpectedCaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: "verified".to_string(),
                min_obligations: *min_obligations,
                expected_error_patterns: Vec::new(),
            },
        )
        .chain(
            COUNTEREXAMPLE_CASES
                .iter()
                .map(
                    |(case_id, upstream_case_id, min_obligations)| ExpectedCaseMetadata {
                        case_id: (*case_id).to_string(),
                        upstream_case_id: (*upstream_case_id).to_string(),
                        expected_verdict: "counterexample".to_string(),
                        min_obligations: *min_obligations,
                        expected_error_patterns: Vec::new(),
                    },
                ),
        )
        .chain(FAIL_CLOSED_CASES.iter().map(
            |(case_id, upstream_case_id, expected_error_patterns)| {
                ExpectedCaseMetadata {
                    case_id: (*case_id).to_string(),
                    upstream_case_id: (*upstream_case_id).to_string(),
                    expected_verdict: "error".to_string(),
                    min_obligations: 0,
                    expected_error_patterns: expected_error_patterns
                        .iter()
                        .map(|pattern| (*pattern).to_string())
                        .collect(),
                }
            },
        ))
        .collect()
}

fn expected_case_metadata_from_manifest() -> Vec<ExpectedCaseMetadata> {
    let source =
        std::fs::read_to_string(verus_manifest_path()).expect("Verus manifest should be readable");
    let manifest: serde_json::Value =
        serde_json::from_str(&source).expect("Verus manifest should parse as JSON");
    let row = manifest["entries"]
        .as_array()
        .expect("Verus manifest should contain entries")
        .iter()
        .find(|entry| {
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/modules.rs")
        })
        .expect("Verus manifest should contain modules.rs row");

    row["expected_cases"]
        .as_array()
        .expect("modules.rs row should contain expected_cases")
        .iter()
        .map(|entry| ExpectedCaseMetadata {
            case_id: entry["case_id"]
                .as_str()
                .expect("case_id should be a string")
                .to_string(),
            upstream_case_id: entry
                .get("upstream_case_id")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("")
                .to_string(),
            expected_verdict: entry["expected_verdict"]
                .as_str()
                .expect("expected_verdict should be a string")
                .to_string(),
            min_obligations: entry["min_obligations"]
                .as_u64()
                .expect("min_obligations should be an integer")
                .try_into()
                .expect("min_obligations should fit usize"),
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

fn file_contains_function(file: &syn::File, name: &str) -> bool {
    fn items_contain_function(items: &[syn::Item], name: &str) -> bool {
        items.iter().any(|item| match item {
            syn::Item::Fn(function) => function.sig.ident == name,
            syn::Item::Mod(module) => module
                .content
                .as_ref()
                .is_some_and(|(_, items)| items_contain_function(items, name)),
            _ => false,
        })
    }

    items_contain_function(&file.items, name)
}

fn assert_verified(case: &str, upstream_case: &str, min_obligations: usize) {
    let (result, obligation_count) = verify_port_case(case, upstream_case);
    assert!(
        obligation_count >= min_obligations,
        "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligation_count}"
    );
    assert!(
        matches!(result, VerifyResult::Verified),
        "{case} ({upstream_case}) should verify, got: {result:?}"
    );
}

fn assert_counterexample(case: &str, upstream_case: &str, min_obligations: usize) {
    let (result, obligation_count) = verify_port_case(case, upstream_case);
    assert!(
        obligation_count >= min_obligations,
        "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligation_count}"
    );
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "{case} ({upstream_case}) should be rejected, got: {result:?}"
    );
}

fn fail_closed_message_for_case(
    path: &str,
    case: &str,
    upstream_case: &str,
    expected_fragments: &[&str],
) {
    let message = match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}")
        }
        Ok(other) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got {other:?}")
        }
    };

    for expected_fragment in expected_fragments {
        assert!(
            message.contains(expected_fragment),
            "{case} ({upstream_case}) error should contain {expected_fragment:?}, got: {message}"
        );
    }
}

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    (
        "module_public_struct_field_projection_verified",
        "test_mod_adt_0",
        1,
    ),
    (
        "module_qualified_helper_contract_verified",
        "test_mod_adt_1 / module-qualified helper call shape",
        1,
    ),
    (
        "module_use_alias_helper_contract_verified",
        "test_mod_adt_1 / imported module helper alias shape",
        1,
    ),
    (
        "module_public_qualified_helper_contract_verified",
        "test_mod_adt_1 public module-qualified helper call shape",
        1,
    ),
    (
        "module_private_qualified_helper_contract_verified",
        "test_mod_adt_1 private module-qualified helper call shape",
        1,
    ),
    (
        "module_imported_group_helper_contract_verified",
        "test_mod_adt_1 grouped imported helper call shape",
        1,
    ),
    (
        "module_crate_qualified_helper_contract_verified",
        "test_mod_adt_1 crate-qualified helper call shape",
        1,
    ),
    (
        "module_nested_qualified_helper_contract_verified",
        "open_crate/open_super/open_path nested module helper call shape",
        1,
    ),
    // Module spec-fn return-type registration: qualified/aliased/in-contract calls
    // to a transparent module spec fn now resolve and verify; the imported opaque fn
    // verifies only after `reveal!`. (upstream_case_id must match the port exactly.)
    (
        "module_public_spec_fn_qualified_currently_blocked",
        "test_mod_adt_1 qualified module spec-function boundary",
        1,
    ),
    (
        "module_public_spec_fn_alias_currently_blocked",
        "test_mod_adt_1 imported module spec-function alias boundary",
        1,
    ),
    (
        "module_public_spec_fn_in_contract_currently_blocked",
        "test_mod_child_ok module spec-function contract registration boundary",
        1,
    ),
    (
        "module_opaque_spec_fn_imported_reveal_currently_blocked",
        "test_mod_fn_publish_opaque_reveal imported opaque reveal boundary",
        1,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "module_public_struct_scope_false_counterexample",
        "test_mod_adt_0 module ADT false assertion sentinel",
        1,
    ),
    (
        "module_imported_public_struct_false_counterexample",
        "test_mod_adt_0 imported public module ADT false assertion sentinel",
        1,
    ),
    // False qualified assertion is refuted; the OPAQUE module spec fn WITHOUT reveal
    // stays uninterpreted (opacity guard), so asserting it is a counterexample — NOT
    // a false-verify. (upstream_case_id must match the port exactly.)
    (
        "module_public_spec_fn_qualified_false_currently_blocked",
        "test_mod_adt_1 false qualified module spec-function boundary",
        1,
    ),
    (
        "module_opaque_spec_fn_without_reveal_currently_blocked",
        "test_mod_fn_publish_opaque_no_reveal",
        1,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    // Private module spec fn stays encapsulated (visibility guard): an external
    // caller still fails closed with "unknown return type".
    (
        "module_private_spec_fn_qualified_currently_blocked",
        "test_requires_private private module spec-function registration boundary",
        &[
            "type inference failed: unknown return type for function",
            "module_specs::private_truth",
        ],
    ),
    (
        "module_qualified_helper_contract_in_ensures_fails_closed",
        "test_mod_sibling_fail contract-helper boundary shape",
        &[
            "Unsupported call to sibling helper `module_helpers::always_true` inside target requires/ensures",
        ],
    ),
    (
        "module_qualified_helper_contract_in_requires_fails_closed",
        "test_requires_private requires-helper boundary shape",
        &[
            "Unsupported call to sibling helper `module_helpers::always_true` inside target requires/ensures",
        ],
    ),
    (
        "module_self_qualified_helper_contract_in_ensures_fails_closed",
        "test_mod_sibling_fail self-qualified contract-helper boundary shape",
        &[
            "Unsupported call to sibling helper `self::module_helpers::always_true` inside target requires/ensures",
        ],
    ),
    (
        "module_qualified_opaque_reveal_fails_closed",
        "test_mod_fn_publish_opaque_reveal qualified reveal target boundary",
        &[
            "supports only unqualified function names",
            "module_adt :: opaque_is_four_doors",
        ],
    ),
    (
        "module_open_without_pub_diagnostic_fails_closed",
        "test_publish_but_not_marked_pub open-without-pub diagnostic boundary",
        &["unknown contract clause `open_without_pub` in #[contract]"],
    ),
    (
        "module_open_more_public_than_function_diagnostic_fails_closed",
        "open_more_public_than_function visibility diagnostic boundary",
        &["unknown contract clause `open_more_public_than_function` in #[contract]"],
    ),
    (
        "module_open_proof_mode_diagnostic_fails_closed",
        "publish_proof_fail proof/open mode diagnostic boundary",
        &["unknown contract clause `open_proof_mode` in #[contract]"],
    ),
    (
        "module_open_exec_mode_diagnostic_fails_closed",
        "publish_exec_fail exec/open mode diagnostic boundary",
        &["unknown contract clause `open_exec_mode` in #[contract]"],
    ),
    (
        "module_closed_exec_mode_diagnostic_fails_closed",
        "publish_exec_fail exec/closed mode diagnostic boundary",
        &["unknown contract clause `closed_exec_mode` in #[contract]"],
    ),
    (
        "module_open_crate_visibility_diagnostic_fails_closed",
        "open_crate visibility boundary",
        &["unknown contract clause `open_crate_visibility` in #[contract]"],
    ),
    (
        "module_open_super_visibility_diagnostic_fails_closed",
        "open_super visibility boundary",
        &["unknown contract clause `open_super_visibility` in #[contract]"],
    ),
    (
        "module_open_path_visibility_diagnostic_fails_closed",
        "open_path visibility boundary",
        &["unknown contract clause `open_path_visibility` in #[contract]"],
    ),
    (
        "module_main_proof_mode_diagnostic_fails_closed",
        "main_proof_fail main/proof mode diagnostic boundary",
        &["unknown contract clause `main_proof_mode` in #[contract]"],
    ),
    (
        "module_main_spec_mode_diagnostic_fails_closed",
        "main_spec_fail main/spec mode diagnostic boundary",
        &["unknown contract clause `main_spec_mode` in #[contract]"],
    ),
    (
        "module_uninterp_exec_syntax_diagnostic_fails_closed",
        "uninterp_exec_fail uninterp exec syntax boundary",
        &["unknown contract clause `uninterp_exec_syntax` in #[contract]"],
    ),
    (
        "module_uninterp_spec_body_diagnostic_fails_closed",
        "uninterp_spec_body_free_fail uninterp spec body boundary",
        &["unknown contract clause `uninterp_spec_body` in #[contract]"],
    ),
    (
        "module_uninterp_spec_body_assoc_diagnostic_fails_closed",
        "uninterp_spec_body_assoc_fail uninterp assoc spec body boundary",
        &["unknown contract clause `uninterp_spec_body_assoc` in #[contract]"],
    ),
    (
        "module_uninterp_spec_body_trait_diagnostic_fails_closed",
        "uninterp_spec_body_trait_fail uninterp trait spec body boundary",
        &["unknown contract clause `uninterp_spec_body_trait` in #[contract]"],
    ),
    (
        "module_uninterp_spec_body_trait_impl_diagnostic_fails_closed",
        "uninterp_spec_body_trait_impl_fail uninterp trait impl boundary",
        &["unknown contract clause `uninterp_spec_body_trait_impl` in #[contract]"],
    ),
    (
        "module_uninterp_open_syntax_diagnostic_fails_closed",
        "uninterp_open_fail uninterp/open syntax boundary",
        &["unknown contract clause `uninterp_open_syntax` in #[contract]"],
    ),
];

#[test]
fn modules_rs_port_file_is_rust_syntax() {
    let source =
        std::fs::read_to_string(modules_port_path()).expect("modules port should be readable");
    syn::parse_file(&source).expect("modules port should parse as ordinary Rust syntax");
}

#[test]
fn modules_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_modules_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream modules.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] test_mod_adt_0",
        "#[test] test_mod_adt_1",
        "pub open spec fn is_four_doors(c: Car) -> bool",
        "#[verifier(opaque_outside_module)]",
        "#[test] test_mod_fn_publish_opaque_no_reveal",
        "#[test] test_mod_fn_publish_opaque_reveal",
        "#[test] test_mod_child_ok",
        "#[test] test_mod_sibling_fail",
        "#[test] test_requires_private",
        "#[test] test_publish_but_not_marked_pub",
        "#[test] publish_proof_fail",
        "#[test] publish_exec_fail",
        "#[test] main_proof_fail",
        "#[test] main_spec_fail",
        "#[test] open_crate",
        "#[test] open_super",
        "#[test] open_path",
        "#[test] open_more_public_than_function",
        "#[test] uninterp_exec_fail",
        "#[test] uninterp_spec_body_free_fail",
        "#[test] uninterp_open_fail",
        "pub uninterp open fn bar();",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream modules.rs should still contain {expected}"
        );
    }
}

#[test]
fn modules_rs_expected_case_metadata_is_exact() {
    let source =
        std::fs::read_to_string(modules_port_path()).expect("modules port should be readable");
    assert!(
        source.contains("MODULES_RS_EXPECTED_CASES")
            && source.contains("modules_rs_expected_cases")
            && source.contains("MODULES_RS_EXPECTED_ERROR_PATTERNS")
            && source.contains("modules_rs_expected_error_patterns"),
        "modules port should expose expected-case metadata helpers"
    );

    let file = modules_port_file();
    let actual = expected_case_metadata_from_port(&file);
    let expected = expected_case_metadata_from_tests();
    assert_eq!(
        actual, expected,
        "modules port expected-case metadata should exactly match the executable regression inventory"
    );

    let mut seen = BTreeSet::new();
    for expected_case in &actual {
        assert!(
            seen.insert(expected_case.case_id.clone()),
            "duplicate expected case id {}",
            expected_case.case_id
        );
        assert!(
            matches!(
                expected_case.expected_verdict.as_str(),
                "verified" | "counterexample" | "error"
            ),
            "expected verdict for {} should be schema-valid, got {}",
            expected_case.case_id,
            expected_case.expected_verdict
        );
        assert_ne!(
            expected_case.expected_verdict, "Unknown",
            "Unknown is not stable expected-case evidence"
        );
        if expected_case.expected_verdict == "error" {
            assert!(
                !expected_case.expected_error_patterns.is_empty(),
                "{} should pin expected error patterns",
                expected_case.case_id
            );
        } else {
            assert!(
                expected_case.expected_error_patterns.is_empty(),
                "{} should not pin error patterns for non-error evidence",
                expected_case.case_id
            );
        }
        assert!(
            file_contains_function(&file, &expected_case.case_id),
            "metadata case {} should have a Rust-valid witness function",
            expected_case.case_id
        );
        match expected_case.expected_verdict.as_str() {
            "verified" | "counterexample" => assert!(
                expected_case.min_obligations >= 1,
                "{} should pin at least one obligation",
                expected_case.case_id
            ),
            "error" => assert_eq!(
                expected_case.min_obligations, 0,
                "{} should pin zero obligations for fail-closed Error metadata",
                expected_case.case_id
            ),
            _ => unreachable!("schema-valid verdict checked above"),
        }
    }
}

#[test]
fn modules_rs_expected_case_metadata_matches_manifest() {
    let file = modules_port_file();
    assert_eq!(
        expected_case_metadata_from_port(&file),
        expected_case_metadata_from_manifest(),
        "modules.rs manifest expected_cases should match port metadata and error patterns exactly"
    );
}

#[test]
fn modules_rs_verified_subset_verifies_from_file() {
    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        assert_verified(case, upstream_case, *min_obligations);
    }
}

#[test]
fn modules_rs_counterexample_subset_is_rejected_from_file() {
    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        assert_counterexample(case, upstream_case, *min_obligations);
    }
}

#[test]
fn modules_rs_contract_helper_boundary_fails_closed_from_file() {
    let path = modules_port_path();
    let path = path.to_str().expect("modules port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        fail_closed_message_for_case(path, case, upstream_case, expected_fragments);
    }
}
