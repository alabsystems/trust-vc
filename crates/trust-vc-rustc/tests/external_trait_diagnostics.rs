//! Native source identities for external trait item diagnostics.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

const TRAIT_ERROR: &str = "a trait item cannot be marked 'external'. Perhaps you meant to mark the entire trait external?";
const IMPL_ERROR: &str = "an item in a trait impl cannot be marked 'external'. An individual item of a trait impl cannot be marked external independently of the implementation. Perhaps you meant to mark the entire trait impl external, or you meant to mark this item as `external_body`?";

fn rejected(name: &str, source: &str, message: &str, lines: &[usize]) {
    let run = common::run(name, source, &[]);
    assert_ne!(run.exit, 0, "{run:?}");
    assert_eq!(run.outcome(), "verus-rejected", "{run:?}");
    assert!(run.raw.is_empty(), "{run:?}");
    let errors = run.errors();
    assert_eq!(errors.len(), lines.len(), "{run:?}");
    let mut actual_lines = Vec::new();
    for error in errors {
        assert_eq!(error.message, message, "{run:?}");
        assert_eq!(error.primary_lines.len(), 1, "{run:?}");
        actual_lines.push(error.primary_lines[0]);
    }
    actual_lines.sort_unstable();
    assert_eq!(actual_lines, lines, "{run:?}");
    assert!(
        run.record["functions"]
            .as_array()
            .unwrap()
            .iter()
            .all(|function| function["verdict"] != "verified"),
        "{run:?}"
    );
}

#[test]
fn one_source_method_and_its_generated_companion_report_once() {
    rejected(
        "external_trait_generated_pair",
        "verus! {\ntrait T {\n#[verifier::external]\nfn f(&self);\n}\n}",
        TRAIT_ERROR,
        &[4],
    );
}

#[test]
fn two_source_methods_in_one_trait_keep_separate_diagnostics() {
    rejected(
        "external_trait_two_methods",
        "verus! {\ntrait T {\n#[verifier::external]\nfn f(&self);\n#[verifier::external]\nfn g(&self);\n}\n}",
        TRAIT_ERROR,
        &[4, 6],
    );
}

#[test]
fn same_method_name_in_different_traits_keeps_native_owner_identity() {
    rejected(
        "external_trait_two_owners",
        "verus! {\ntrait A {\n#[verifier::external]\nfn f(&self);\n}\ntrait B {\n#[verifier::external]\nfn f(&self);\n}\n}",
        TRAIT_ERROR,
        &[4, 8],
    );
}

#[test]
fn authored_prefix_lookalike_at_another_source_range_is_independent() {
    rejected(
        "external_trait_authored_prefix",
        "verus! {\ntrait T {\n#[verifier::external]\nfn f(&self) {}\n#[verifier::external]\nfn VERUS_SPEC__f(&self) {}\n}\n}",
        TRAIT_ERROR,
        &[4, 6],
    );
}

#[test]
fn unmatched_prefix_cannot_hide_external_error_or_create_a_body() {
    rejected(
        "external_trait_unmatched_prefix",
        "verus! {\ntrait T {\n#[verifier::external]\nfn VERUS_SPEC__missing(&self) {}\n}\n}",
        TRAIT_ERROR,
        &[4],
    );
}

#[test]
fn malformed_spec_companion_keeps_its_existing_missing_declaration_error() {
    rejected(
        "external_trait_orphan_spec",
        "verus! {\ntrait T {\nfn VERUS_SPEC__missing(&self) {}\n}\n}",
        "no matching method found for method specification",
        &[3],
    );
}

#[test]
fn implementation_method_keeps_its_own_external_error() {
    rejected(
        "external_trait_impl",
        "verus! {\ntrait T { fn f(&self); }\nstruct X {}\nimpl T for X {\n#[verifier::external]\nfn f(&self) {}\n}\n}",
        IMPL_ERROR,
        &[6],
    );
}
