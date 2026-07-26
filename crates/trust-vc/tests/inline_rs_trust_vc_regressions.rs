// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first upstream inline.rs TrustVc scout slice.
//!
//! These tests intentionally keep the upstream file as an unsupported gap. They
//! prove only inline-marked source-spec contract/assertion surfaces, reject
//! false bodies/assertions against those source specs, pin Rust-valid upstream
//! shapes, and pin the current fail-closed boundaries for executable helpers,
//! hide, and trait/default-impl surfaces.

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn inline_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/inline.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn verify_port_case(case: &str) -> (VerifyResult, usize) {
    let path = inline_port_path();
    let source =
        std::fs::read_to_string(&path).expect("inline port should be readable for extraction");
    let file = syn::parse_file(&source).expect("inline port should parse for extraction");
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == case => Some(func),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} should exist in inline port"));

    let vc = extract_verification_conditions_with_file_context(&file, func)
        .unwrap_or_else(|err| panic!("{case} should extract: {err}"));
    let obligations = vc.obligations().len();
    (vc.verify(), obligations)
}

fn parse_inline_port() -> (String, syn::File) {
    let path = inline_port_path();
    let source =
        std::fs::read_to_string(&path).expect("inline port should be readable for extraction");
    let file = syn::parse_file(&source).expect("inline port should parse for extraction");
    (source, file)
}

fn top_level_fn<'a>(file: &'a syn::File, case: &str) -> &'a syn::ItemFn {
    file.items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == case => Some(func),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} should exist in inline port"))
}

fn has_attr(func: &syn::ItemFn, attr_name: &str) -> bool {
    func.attrs.iter().any(|attr| {
        attr.path()
            .segments
            .last()
            .is_some_and(|segment| segment.ident == attr_name)
    })
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("inline port should define {const_name}"));

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

fn string_slice(expr: &syn::Expr) -> Vec<String> {
    let syn::Expr::Reference(reference) = expr else {
        panic!("expected referenced string-slice metadata");
    };
    let syn::Expr::Array(array) = reference.expr.as_ref() else {
        panic!("expected string-slice array metadata");
    };

    array.elems.iter().map(literal_string).collect()
}

fn error_pattern_entries(file: &syn::File) -> BTreeMap<String, Vec<String>> {
    let array = referenced_array_const(file, "INLINE_RS_EXPECTED_ERROR_PATTERNS");
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

        let case_id = literal_string(&tuple.elems[0]);
        let patterns = string_slice(&tuple.elems[1]);
        assert!(
            entries.insert(case_id.clone(), patterns).is_none(),
            "duplicate inline error-pattern metadata for {case_id}"
        );
    }

    entries
}

fn metadata_entries(file: &syn::File) -> Vec<CaseMetadata> {
    let array = referenced_array_const(file, "INLINE_RS_EXPECTED_CASES");
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
        let case_id = literal_string(&tuple.elems[0]);
        assert!(
            seen.insert(case_id.clone()),
            "duplicate inline metadata for {case_id}"
        );
        let expected_error_patterns = error_patterns.remove(&case_id).unwrap_or_default();
        entries.push(CaseMetadata {
            case_id,
            upstream_case_id: literal_string(&tuple.elems[1]),
            expected_verdict: literal_string(&tuple.elems[2]),
            min_obligations: literal_usize(&tuple.elems[3]),
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/inline.rs")
        })
        .expect("Verus manifest should contain inline.rs row");

    row["expected_cases"]
        .as_array()
        .expect("inline.rs row should contain expected_cases")
        .iter()
        .map(|case| CaseMetadata {
            case_id: case["case_id"]
                .as_str()
                .expect("manifest case should contain case_id")
                .to_string(),
            upstream_case_id: case
                .get("upstream_case_id")
                .and_then(serde_json::Value::as_str)
                .unwrap_or("")
                .to_string(),
            expected_verdict: case["expected_verdict"]
                .as_str()
                .expect("manifest case should contain expected_verdict")
                .to_string(),
            min_obligations: case["min_obligations"]
                .as_u64()
                .expect("manifest case should contain min_obligations")
                .try_into()
                .expect("min_obligations should fit usize"),
            expected_error_patterns: case
                .get("expected_error_patterns")
                .and_then(serde_json::Value::as_array)
                .map(|patterns| {
                    patterns
                        .iter()
                        .map(|pattern| {
                            pattern
                                .as_str()
                                .expect("expected_error_patterns entries should be strings")
                                .to_string()
                        })
                        .collect()
                })
                .unwrap_or_default(),
        })
        .collect()
}

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    ("inline_spec_contract_surface_verified", "test1", 1),
    ("inline_spec_assertion_verified", "test1", 1),
    ("inline_local_binding_spec_contract_verified", "test1", 1),
    ("inline_test1_arithmetic_assertions_verified", "test1", 1),
    ("inline_test1_arithmetic_contract_verified", "test1", 1),
    ("inline_test1_generic_identity_verified", "test1", 1),
    ("inline_test1_opaque_wrapper_requires_verified", "test1", 1),
    ("inline_test1_opaque_wrapper_reveal_verified", "test1", 1),
    (
        "inline_ensures_type_inference_direct_field_verified",
        "test_ensures_type_inference",
        1,
    ),
    // File-path inline substitution (#2777): the local-binding call-through body
    // inlines to `a+2b`, so `f(33,44)==121` verifies. Legacy "fails_closed"
    // case_id kept for pin stability (was an "undefined variable za" placeholder).
    (
        "inline_test1_local_binding_call_plain_fails_closed",
        "test1",
        1,
    ),
    // Faithful port of upstream `test_ensures_type_inference` (`test1() -> Foo
    // ensures get_b(b)` returning `Foo{b:true}` => Ok). Datatype-parameter inline
    // spec fns now encode (#2777): `inline_get_b(result)` inlines to `result.b`.
    // Legacy "fails_closed" case_id kept (was "unsupported parameter type").
    (
        "inline_ensures_type_inference_getter_fails_closed",
        "test_ensures_type_inference",
        1,
    ),
    // Generic tuple-returning inline spec fn (#2777): call-site substitution +
    // tuple-carrier renormalization makes `swap::<u8, bool>(10u8, true)` inline
    // to `(true, 10u8)`, so `swapped.0` and `swapped.1 == 10u8` verify (upstream
    // test1 `fg`). Legacy "fails_closed" case_id kept (was "conflicting variant
    // metadata"). Moved here from FAIL_CLOSED_CASES.
    (
        "inline_test1_generic_swap_return_type_fails_closed",
        "test1",
        1,
    ),
];

const REJECTED_CASES: &[(&str, &str, usize)] = &[
    (
        "inline_spec_contract_surface_wrong_counterexample",
        "test1 false inline spec function contract body",
        1,
    ),
    (
        "inline_spec_assertion_wrong_counterexample",
        "test1 false inline spec function assertion",
        1,
    ),
    (
        "inline_local_binding_spec_false_counterexample",
        "test1 false inline local-binding spec assertion",
        1,
    ),
    (
        "inline_test1_arithmetic_wrong_counterexample",
        "test1 false inline arithmetic assertion",
        1,
    ),
    (
        "inline_test1_generic_identity_wrong_counterexample",
        "test1 false generic inline spec assertion",
        1,
    ),
    (
        "inline_test1_opaque_wrapper_without_reveal_counterexample",
        "test1 false unrevealed uninterpreted-wrapper assertion",
        1,
    ),
    (
        "inline_ensures_type_inference_direct_field_counterexample",
        "test_ensures_type_inference false direct struct field postcondition",
        1,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    ("inline_test1_arithmetic_body_counterexample", "test1", 1),
    ("inline_bool_negate_body_counterexample", "test1", 1),
    // hide! supported (#2785): hiding the inline fn (Verus opaques it) with no
    // reveal leaves the asserted body-fact unprovable → Counterexample. Legacy
    // case_id (was a fail-closed "unsupported hide!" placeholder).
    ("inline_hide_macro_boundary_fails_closed", "test_spec_fn", 1),
    // trust-vc-authored negative probe for datatype-parameter inline getters
    // (#2777): returns `Foo{b:false}`, so the inlined postcondition `result.b`
    // is false → Counterexample (mirrors the direct-field control). Legacy
    // "fails_closed" case_id kept (was "unsupported parameter type" placeholder).
    (
        "inline_ensures_type_inference_getter_wrong_fails_closed",
        "test_ensures_type_inference",
        1,
    ),
    // Faithful port of upstream `inline_poly` (assert_one_fails): a generic
    // `#[inline]` spec fn `forall|a: A| s.contains(a)` at `Set<int>` is false for
    // a general set. The generic inline body is monomorphized to `A = int` at the
    // call site (#2777) — the `forall` binder + `contains` select take the
    // concrete `int` sort — so the assertion is refuted with `s = {}` instead of
    // returning Unknown on a `Poly` sort mismatch.
    ("inline_poly_all_contains_counterexample", "inline_poly", 1),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "inline_exec_helper_in_contract_fails_closed",
        "test_nonspec_fails",
        &["Unsupported call to sibling helper"],
    ),
    // inline_hide_macro_boundary_fails_closed moved to COUNTEREXAMPLE_CASES
    // (hide! supported, #2785 — faithful CE, no longer a fail-closed error).
    // local_binding_call_plain + getter moved to VERIFIED_CASES and getter_wrong
    // to COUNTEREXAMPLE_CASES (file-path inline substitution, #2777 — no longer
    // fail-closed errors).
    // inline_test1_generic_swap_return_type_fails_closed moved to VERIFIED_CASES
    // (generic inline substitution + tuple-carrier renormalization, #2777 — the
    // generic tuple return now verifies, no longer a fail-closed error).
    (
        "inline_default_impl_trait_boundary_fails_closed",
        "default_impl_issue1407",
        &[
            "unsupported",
            "inline_default_value",
            "InlineDefaultOverride",
        ],
    ),
    // Faithful port of upstream `test_rec_fails1`: an `#[inline]` spec fn with a
    // `decreases` clause is rejected at definition time (`from_item_fn`) with the
    // verbatim Verus message. Surfaces when the diagnostic caller resolves the
    // inline body.
    (
        "inline_rec_decreases_diagnostic",
        "test_rec_fails1",
        &["'inline' functions cannot be recursive"],
    ),
    // Faithful port of upstream `test_rec_fails2`: an `#[inline]` spec fn with a
    // genuine self-call and no `decreases` clause.
    (
        "inline_rec_no_decreases_diagnostic",
        "test_rec_fails2",
        &["recursive function must have a decreases clause"],
    ),
    // Faithful port of upstream `test_nonspec_fails`: `#[inline]` on a proof fn is
    // rejected at definition time (vc_extraction mode check) with the verbatim
    // Verus message.
    (
        "inline_nonspec_proof_diagnostic",
        "test_nonspec_fails",
        &["'inline' is only allowed for 'spec' functions"],
    ),
    // Faithful port of upstream `test_private_fails`: `#[inline]` on a `closed`
    // (opaque, body-hidden) spec fn is rejected at definition time with the
    // verbatim Verus message. trust-vc's `#[trust_vc::opaque]` is the faithful
    // analog of Verus `closed`.
    (
        "inline_private_closed_diagnostic",
        "test_private_fails",
        &["'inline' is only allowed for private or 'open spec' functions"],
    ),
];

const INLINE_HELPER_SHAPE_PINS: &[(&str, &str)] = &[
    ("inline_negate", "existing boolean inline helper"),
    ("inline_let_roundtrip", "test1 local-binding boolean helper"),
    ("inline_arith_formula", "test1 fi direct arithmetic helper"),
    ("inline_arith_wrapper", "test1 f2 wrapper helper"),
    ("inline_arith_renamed", "test1 f3 renamed-argument helper"),
    (
        "inline_arith_local_bindings",
        "test1 f4 arithmetic local-binding helper",
    ),
    (
        "inline_arith_local_bindings_call_plain",
        "test1 f4 exact local-binding call-through helper",
    ),
    (
        "inline_generic_identity",
        "test1 generic inline spec surrogate",
    ),
    ("inline_generic_swap", "test1 fg generic tuple-swap helper"),
    (
        "inline_opaque_predicate_wrapper",
        "test1 fy/fpy opaque predicate wrapper",
    ),
    ("inline_less_than", "test_spec_fn f1/f2 relation helper"),
    ("inline_get_b", "test_ensures_type_inference getter helper"),
    (
        "inline_trait_default_wrapper",
        "default_impl_issue1407 trait wrapper helper",
    ),
];

#[test]
fn inline_rs_port_file_is_rust_syntax() {
    let source =
        std::fs::read_to_string(inline_port_path()).expect("inline port should be readable");
    syn::parse_file(&source).expect("inline port should parse as ordinary Rust syntax");
}

#[test]
fn inline_rs_upstream_shape_pins_are_present() {
    let (source, file) = parse_inline_port();
    assert!(
        source.contains("INLINE_RS_EXPECTED_CASES")
            && source.contains("inline_rs_expected_cases")
            && source.contains("INLINE_RS_EXPECTED_ERROR_PATTERNS")
            && source.contains("inline_rs_expected_error_patterns"),
        "inline port should expose expected-case and error-pattern metadata helpers"
    );
    assert_eq!(
        metadata_entries(&file),
        manifest_expected_metadata(),
        "inline.rs manifest expected_cases should match port metadata and error patterns exactly"
    );

    for (helper, upstream_shape) in INLINE_HELPER_SHAPE_PINS {
        let func = top_level_fn(&file, helper);
        assert!(
            has_attr(func, "spec"),
            "{helper} ({upstream_shape}) should remain a source spec helper"
        );
        assert!(
            has_attr(func, "inline"),
            "{helper} ({upstream_shape}) should remain inline-marked"
        );
    }

    for required_fragment in [
        "fn inline_arith_formula(x: int, y: int) -> int",
        "fn inline_arith_wrapper(x: int, y: int) -> int",
        "fn inline_arith_renamed(a: int, b: int) -> int",
        "fn inline_arith_local_bindings(a: int, b: int) -> int",
        "fn inline_arith_local_bindings_call_plain(a: int, b: int) -> int",
        "fn inline_generic_swap<A, B>(a: A, b: B) -> (B, A)",
        "fn inline_get_b(foo: InlineFoo) -> bool",
        "trait InlineDefaultTrait",
    ] {
        assert!(
            source.contains(required_fragment),
            "inline port should keep upstream-shaped fragment {required_fragment:?}"
        );
    }
}

#[test]
fn inline_rs_verified_inline_spec_subset_verifies_from_file() {
    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        let (result, obligations) = verify_port_case(case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn inline_rs_false_inline_spec_claims_are_rejected_from_file() {
    for (case, upstream_case, min_obligations) in REJECTED_CASES {
        let (result, obligations) = verify_port_case(case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert!(
            !matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should not verify, got: {result:?}"
        );
    }

    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        let (result, obligations) = verify_port_case(case);
        assert!(
            obligations >= *min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
        );
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be rejected, got: {result:?}"
        );
    }
}

#[test]
fn inline_rs_exec_helper_spec_term_fails_closed_from_file() {
    let path = inline_port_path();
    let path = path.to_str().expect("inline port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        let message = match verify_function_from_file(path, case) {
            Err(err) => err.to_string(),
            Ok(VerifyResult::Error { message }) => message,
            Ok(other) => {
                panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
            }
        };

        assert!(
            expected_fragments
                .iter()
                .any(|expected_fragment| message.contains(expected_fragment)),
            "{case} ({upstream_case}) error should contain one of {expected_fragments:?}, got: {message}"
        );
    }
}
