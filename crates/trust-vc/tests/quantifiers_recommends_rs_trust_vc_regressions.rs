// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the current proof-language quantifier/recommends
//! unsupported-gap slices.
//!
//! These tests intentionally do not claim full Verus parity. They prove only
//! the listed upstream-derived witnesses while the manifest keeps both entries
//! fail-closed.

use std::path::PathBuf;
use trust_vc_core::vc::VerificationContext;
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn port_path(file: &str) -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join(format!("../../evals/verus/ported/{file}"))
}

fn assert_verified(path: &str, case: &str, upstream_case: &str) {
    let result = verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
    assert!(
        matches!(result, VerifyResult::Verified),
        "{case} ({upstream_case}) should verify, got: {result:?}"
    );
}

fn assert_counterexample(path: &str, case: &str, upstream_case: &str) {
    let result = verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "{case} ({upstream_case}) should be rejected, got: {result:?}"
    );
}

fn assert_not_verified(path: &str, case: &str, upstream_case: &str) {
    let result = verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
    assert!(
        !matches!(result, VerifyResult::Verified),
        "{case} ({upstream_case}) must fail closed, got: {result:?}"
    );
}

fn extract_port_case(file: &str, case: &str) -> VerificationContext {
    let path = port_path(file);
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("{file} should read from {:?}: {err}", path));
    let parsed =
        syn::parse_file(&source).unwrap_or_else(|err| panic!("{file} should parse: {err}"));
    let func = parsed
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == case => Some(func),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} should exist in {file}"));

    extract_verification_conditions_with_file_context(&parsed, func)
        .unwrap_or_else(|err| panic!("{case} should extract from {file}: {err}"))
}

#[test]
fn quantifiers_rs_verified_subset_verifies_from_file() {
    let path = port_path("quantifiers.rs");
    let path = path.to_str().expect("quantifiers.rs path should be UTF-8");

    for (case, upstream_case) in [
        ("test1", "test1"),
        ("simple_exists_witness", "simple exists witness"),
        ("simple_forall_reflexive", "simple forall reflexive"),
        (
            "inline_exists_nat_witness",
            "test1 inline exists nat witness",
        ),
    ] {
        assert_verified(path, case, upstream_case);
    }
}

#[test]
fn quantifiers_rs_counterexample_subset_is_rejected_from_file() {
    let path = port_path("quantifiers.rs");
    let path = path.to_str().expect("quantifiers.rs path should be UTF-8");

    for (case, upstream_case) in [
        ("test1_fails", "test1_fails"),
        ("simple_forall_fails", "simple forall false claim"),
    ] {
        assert_counterexample(path, case, upstream_case);
    }

    assert_not_verified(
        path,
        "inline_exists_nat_negative_fails",
        "test1_fails inline exists nat no-witness case",
    );
}

#[test]
fn quantifiers_rs_manual_trigger_surface_is_preserved_from_file() {
    let vc = extract_port_case("quantifiers.rs", "manual_trigger_expression_parity");
    let assertion = vc
        .obligations()
        .iter()
        .find(|obligation| obligation.name().starts_with("assertion"))
        .expect("manual trigger parity case should emit an assertion");

    assert!(
        assertion.condition().contains("# [trigger]"),
        "manual trigger attribute should survive source extraction, got: {}",
        assertion.condition()
    );
    assert!(
        assertion.condition().contains("forall"),
        "manual trigger case should remain a quantified assertion, got: {}",
        assertion.condition()
    );
}

#[test]
fn recommends_rs_concrete_witness_subset_verifies_from_file() {
    let path = port_path("recommends.rs");
    let path = path.to_str().expect("recommends.rs path should be UTF-8");

    assert_verified(
        path,
        "ensures_forall_recommends_positive_witness",
        "ensures_forall_recommends_failure in-range witness",
    );
}

#[test]
fn recommends_rs_concrete_recommends_violations_are_rejected_from_file() {
    let path = port_path("recommends.rs");
    let path = path.to_str().expect("recommends.rs path should be UTF-8");

    for (case, upstream_case) in [
        (
            "ensures_forall_recommends_failure",
            "ensures_forall_recommends_failure",
        ),
        (
            "ensures_type_substitutes_issue1566",
            "ensures_type_substitutes_issue1566",
        ),
    ] {
        assert_counterexample(path, case, upstream_case);
    }
}
