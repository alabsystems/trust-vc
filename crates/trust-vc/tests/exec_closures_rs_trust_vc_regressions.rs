// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the focused upstream exec_closures.rs TrustVc scout.
//!
//! These tests intentionally keep the upstream file as an unsupported gap. They
//! prove only the Rust-valid TrustVc function-contract subset that mirrors
//! executable closure pre/post and call-site obligations, reject stable false
//! postcondition and call witnesses, pin upstream case shapes, and keep direct
//! closure surfaces fail-closed.

mod common;

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn exec_closures_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../evals/verus/ported/exec_closures.rs")
}

fn verus_manifest_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_exec_closures_path() -> PathBuf {
    common::pinned_verus_test_path("exec_closures.rs")
}

fn verify_case_with_obligations(
    path: &Path,
    case: &str,
    upstream_case: &str,
) -> (VerifyResult, usize) {
    let source = std::fs::read_to_string(path)
        .unwrap_or_else(|err| panic!("exec_closures port should be readable: {err}"));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("exec_closures port should parse: {err}"));
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == case => Some(func),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} ({upstream_case}) should exist in exec_closures port"));

    let vc = extract_verification_conditions_with_file_context(&file, func)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
    let obligations = vc.obligations().len();
    (vc.verify(), obligations)
}

fn fail_closed_message(path: &str, case: &str, upstream_case: &str) -> String {
    match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(VerifyResult::Unknown { reason, .. }) => {
            panic!("{case} ({upstream_case}) returned solver Unknown, which is not stable evidence: {reason}")
        }
        Ok(other) => {
            panic!("{case} ({upstream_case}) should fail closed with Error, got: {other:?}")
        }
    }
}

const VERIFIED_CASES: &[(&str, &str, usize)] = &[
    (
        "exec_closure_zero_arg_contract_verified",
        "basic_test_0_args / zero-argument executable closure contract",
        1,
    ),
    (
        "exec_closure_one_arg_contract_verified",
        "basic_test / one-argument executable closure contract",
        1,
    ),
    (
        "exec_closure_two_arg_contract_verified",
        "basic_test_2_args / two-argument executable closure contract",
        1,
    ),
    (
        "exec_closure_helper_application_verified",
        "basic_test / valid executable closure call postcondition",
        1,
    ),
    (
        "exec_closure_call_assignment_contract_verified",
        "test_calls_in_assignments_to_mut_var / call result assignment",
        1,
    ),
    (
        "exec_closure_call_as_sub_expression_contract_verified",
        "test_calls_as_sub_expression / closure call as call argument",
        1,
    ),
    (
        // Phase C part 2 FLIP: DIRECT application `f(2)` of a UNARY def-side-checked
        // `closure!` literal now lowers to the shared `spec_fn_apply` UF, with the
        // call-site seam proving `requires` (2 == 2) and assuming the
        // def-side-CHECKED `ensures` (f(2) == 2). The embedded `assert!(f(2) == 2)`
        // reads the identical term and discharges. Formerly fail-closed (deferred).
        "exec_closure_contract_macro_direct_application_currently_errors",
        "basic_test / direct application of a def-side-checked unary closure! contract",
        1,
    ),
    (
        // BARE-CLOSURE INLINE FLIP: a bare (non-`closure!`) capture-free local
        // closure applied by name is INLINED at the call site — `f(2)` models as
        // its body `2`, so `assert!(f(2) == 2)` VERIFIES. An exact value
        // substitution of the real body (captures/free-callees stay fail-closed;
        // false claims counterexample). See the adversarial suite
        // `trust-vc-core/tests/closure_inline_capture_free_capability.rs`.
        "exec_closure_direct_application_currently_errors",
        "basic_test / direct local executable closure application",
        1,
    ),
    (
        // BARE-CLOSURE INLINE FLIP (zero-arg): `let f = || { 7 }; f()` inlines to
        // `7`, so `assert!(f() == 7)` VERIFIES.
        "exec_closure_zero_arg_direct_application_currently_errors",
        "basic_test_0_args / direct zero-argument closure application",
        1,
    ),
    (
        // INCREMENT 1 (Fn-bound typing foundation) FLIP: an `F: Fn(u64) -> u64`
        // value parameter is typed as a first-class `SpecFn(u64, u64)`, so `f(3)`
        // lowers to the CONGRUENT `spec_fn_apply` UF. `Fn` is deterministic across
        // calls, so two calls with equal arguments give the equal result — a
        // SOUND, non-tautological property. Formerly fail-closed
        // ("Undefined function: f"). The result stays otherwise unconstrained and
        // `FnMut`/`FnOnce` remain fail-closed (see the adversarial suite
        // `trust-vc-core/tests/fn_bound_closure_typing_soundness.rs`).
        "exec_closure_fn_trait_bound_application_is_deterministic_verified",
        "pass_closure_via_typ_param / Fn-bound closure argument call is deterministic",
        1,
    ),
    (
        // INCREMENT 2a (Fn-bound callee-side obligation model) FLIP: an `F: Fn(u64)
        // -> u64` value parameter can now USE the closure's own spec. At `f(a)` the
        // callee-side seam emits the SOUND conditional assume `call_requires%(f, a)
        // ==> call_ensures%(f, a, f(a))` over the OPAQUE reflection UFs, so a callee
        // that establishes `requires f.requires((a,))` discharges a postcondition
        // written over `ensures f.ensures((a,), result)`. The ensures stays opaque
        // (a concrete pin still counterexamples) and omitting the requires fails
        // closed (see the adversarial suite
        // `trust-vc-core/tests/fn_bound_closure_obligation_soundness.rs`).
        "exec_closure_fn_trait_bound_callee_ensures_verified",
        "pass_closure_via_typ_param / Fn-bound closure callee uses its requires+ensures spec",
        1,
    ),
    (
        // INCREMENT 2b (Fn-bound cross-boundary PASS-SITE linkage) FLIP: a caller
        // passes a concrete `closure!` literal `c` into the reflecting callee at
        // `g(c, 5)`. The pass-site linkage ties the callee's opaque
        // `call_requires%` / `call_ensures%` to `c`'s own concrete, arg-substituted
        // requires/ensures, so the caller PROVES the callee's prove-requires (from
        // `c`'s `5 < 10`) and USES its assumed ensures (`c`'s `y == 6`). Fires only
        // for a registered closure literal; the closure's def-side is independently
        // checked (see the adversarial suite
        // `trust-vc-core/tests/fn_bound_closure_pass_site_soundness.rs`).
        "exec_closure_fn_trait_bound_pass_site_roundtrip_verified",
        "pass_closure_via_typ_param / Fn-bound closure literal passed to a reflecting callee round-trips its requires+ensures",
        1,
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str, usize)] = &[
    (
        "exec_closure_zero_arg_bad_ensures_counterexample",
        "test_ensures_fail_0_args / false zero-argument closure postcondition",
        1,
    ),
    (
        "exec_closure_one_arg_bad_ensures_counterexample",
        "test_ensures_fail / false one-argument closure postcondition",
        1,
    ),
    (
        "exec_closure_one_arg_bad_ensures_return_stmt_counterexample",
        "test_ensures_fail_return_stmt / false return-statement postcondition",
        1,
    ),
    (
        "exec_closure_two_arg_bad_ensures_counterexample",
        "test_ensures_fail_2_args / false two-argument closure postcondition",
        1,
    ),
    (
        "exec_closure_two_arg_bad_ensures_return_stmt_counterexample",
        "test_ensures_fail_return_stmt_2_args / false two-argument return postcondition",
        1,
    ),
    (
        "exec_closure_helper_bad_call_requires_counterexample",
        "test_call_requires_fail / invalid executable closure call precondition",
        1,
    ),
    (
        "exec_closure_helper_bad_call_ensures_counterexample",
        "test_call_ensures_fail / invalid executable closure call post-use assertion",
        1,
    ),
    (
        "exec_closure_call_assignment_false_counterexample",
        "test_calls_in_assignments_to_mut_var_fail / false post-assignment assertion",
        1,
    ),
    (
        "exec_closure_call_as_sub_expression_requires_counterexample",
        "test_calls_as_sub_expression_fail / call argument violates callee requires",
        1,
    ),
    (
        // INCREMENT 2b requires-violation companion: the passed closure `c`
        // requires `x < 10`, but the pass-site argument is `50`. The linkage pins
        // `call_requires%(c, (50,)) == (50 < 10) == false`, so the callee's
        // prove-requires obligation is false — the linkage is LOAD-BEARING and
        // rejects a precondition-violating call.
        "exec_closure_fn_trait_bound_pass_site_requires_violation_counterexample",
        "pass_closure_via_typ_param / Fn-bound closure literal passed with a precondition-violating argument",
        1,
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str, &[&str])] = &[
    (
        "exec_closure_requires_reflection_currently_errors",
        "basic_test / f.requires reflection",
        &["requires", "method", "Unsupported", "standalone closure"],
    ),
    (
        "exec_closure_ensures_reflection_currently_errors",
        "basic_test / f.ensures reflection",
        &["ensures", "method", "Unsupported", "standalone closure"],
    ),
    (
        "exec_closure_capture_application_currently_errors",
        "test_requires_is_about_external_var / captured value closure application",
        &["unknown return type for function 'f'", "standalone closure"],
    ),
    (
        "exec_closure_mutable_capture_application_currently_errors",
        "disallowed_mut_capture1 / mutable capture closure application",
        &[
            "unknown return type for function 'f'",
            "standalone closure",
            "assignment",
        ],
    ),
];

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
    expected_error_patterns: Vec<String>,
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("exec_closures port should define {const_name}"));

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
    let array = referenced_array_const(file, "EXEC_CLOSURES_RS_EXPECTED_ERROR_PATTERNS");
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
            "duplicate error-pattern metadata for {case_id}"
        );
    }

    entries
}

fn metadata_entries(file: &syn::File) -> Vec<CaseMetadata> {
    let array = referenced_array_const(file, "EXEC_CLOSURES_RS_EXPECTED_CASES");
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
            "duplicate exec_closures metadata for {case_id}"
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

fn manifest_expected_case_metadata() -> Vec<CaseMetadata> {
    let source =
        std::fs::read_to_string(verus_manifest_path()).expect("Verus manifest should be readable");
    let manifest: serde_json::Value =
        serde_json::from_str(&source).expect("Verus manifest should parse as JSON");
    let row = manifest["entries"]
        .as_array()
        .expect("Verus manifest should contain entries")
        .iter()
        .find(|entry| {
            entry["upstream_path"].as_str()
                == Some("source/rust_verify_test/tests/exec_closures.rs")
        })
        .expect("Verus manifest should contain exec_closures.rs row");

    row["expected_cases"]
        .as_array()
        .expect("exec_closures.rs manifest row should contain expected_cases")
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

#[test]
fn exec_closures_rs_port_file_is_rust_syntax() {
    let source = std::fs::read_to_string(exec_closures_port_path())
        .expect("exec_closures port should be readable");
    syn::parse_file(&source).expect("exec_closures port should parse as ordinary Rust syntax");
}

#[test]
fn exec_closures_rs_pinned_upstream_case_shapes_are_present() {
    let path = pinned_upstream_exec_closures_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream exec_closures.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));
    for expected in [
        "#[test] basic_test",
        "#[test] test_ensures_fail",
        "#[test] test_ensures_fail_return_stmt",
        "#[test] test_assert_requires_fail",
        "#[test] test_assert_not_ensures_fail",
        "#[test] test_call_requires_fail",
        "#[test] test_call_ensures_fail",
        "#[test] test_loop_forever",
        "#[test] test_requires_is_about_external_var",
        "#[test] basic_test_2_args",
        "#[test] test_ensures_fail_2_args",
        "#[test] test_ensures_fail_return_stmt_2_args",
        "#[test] basic_test_0_args",
        "#[test] test_ensures_fail_0_args",
        "#[test] pass_closure_via_typ_param",
        "#[test] pass_closure_via_typ_param_fn_once",
        "#[test] pass_closure_via_typ_param_fn_mut",
        "#[test] call_closure_requires_in_exec_code_fail",
        "#[test] call_closure_ensures_in_exec_code_fail",
        "#[test] test_calls_in_assignments_to_mut_var",
        "#[test] test_calls_as_sub_expression",
        "#[test] old_works_for_params_from_outside_the_closure",
        "#[test] return_unit",
        "#[test] closure_is_dead_end",
        "#[test] disallowed_mut_capture1",
        "#[test] closure_depends_on_type_param",
        "#[test] right_decorations_for_tuple_arg",
        "#[test] tracked_variables_captured_by_closures_send",
        "#[test] return_in_loop_in_closure",
    ] {
        assert!(
            source.contains(expected),
            "pinned upstream exec_closures.rs should still contain {expected}"
        );
    }
}

#[test]
fn exec_closures_rs_expected_case_metadata_matches_manifest() {
    let source = std::fs::read_to_string(exec_closures_port_path())
        .expect("exec_closures port should be readable");
    let file =
        syn::parse_file(&source).expect("exec_closures port should parse as ordinary Rust syntax");

    assert_eq!(
        metadata_entries(&file),
        manifest_expected_case_metadata(),
        "exec_closures.rs manifest expected_cases should match port metadata and error patterns exactly"
    );
    assert!(
        source.contains("exec_closures_rs_expected_cases"),
        "exec_closures port should export expected-case metadata"
    );
    assert!(
        source.contains("EXEC_CLOSURES_RS_EXPECTED_ERROR_PATTERNS"),
        "exec_closures port should define expected-error-pattern metadata"
    );
    assert!(
        source.contains("exec_closures_rs_expected_error_patterns"),
        "exec_closures port should export expected-error-pattern metadata"
    );
    assert!(
        source.contains("exec_closures_rs_fail_closed_error_patterns"),
        "exec_closures port should keep the fail-closed error-pattern accessor"
    );
}

#[test]
fn exec_closures_rs_expected_error_patterns_match_diagnostics() {
    let source = std::fs::read_to_string(exec_closures_port_path())
        .expect("exec_closures port should be readable");
    let file =
        syn::parse_file(&source).expect("exec_closures port should parse as ordinary Rust syntax");
    let path = exec_closures_port_path();
    let path = path
        .to_str()
        .expect("exec_closures port path should be UTF-8");

    for metadata in metadata_entries(&file)
        .into_iter()
        .filter(|metadata| !metadata.expected_error_patterns.is_empty())
    {
        let upstream_case = FAIL_CLOSED_CASES
            .iter()
            .find_map(|(case, upstream_case, _)| {
                if *case == metadata.case_id {
                    Some(*upstream_case)
                } else {
                    None
                }
            })
            .unwrap_or(&metadata.upstream_case_id);
        let message = fail_closed_message(path, &metadata.case_id, upstream_case);

        for expected_fragment in metadata.expected_error_patterns {
            assert!(
                message.contains(&expected_fragment),
                "{} ({upstream_case}) error should contain {expected_fragment:?}, got: {message}",
                metadata.case_id
            );
        }
    }
}

#[test]
fn exec_closures_rs_verified_contract_subset_verifies_from_file() {
    let path = exec_closures_port_path();

    for (case, upstream_case, min_obligations) in VERIFIED_CASES {
        let (result, obligations) = verify_case_with_obligations(&path, case, upstream_case);
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
fn exec_closures_rs_counterexample_subset_is_rejected_from_file() {
    let path = exec_closures_port_path();

    for (case, upstream_case, min_obligations) in COUNTEREXAMPLE_CASES {
        let (result, obligations) = verify_case_with_obligations(&path, case, upstream_case);
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
fn exec_closures_rs_direct_closure_application_fails_closed_from_file() {
    let path = exec_closures_port_path();
    let path = path
        .to_str()
        .expect("exec_closures port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_CASES {
        let message = fail_closed_message(path, case, upstream_case);

        assert!(
            expected_fragments
                .iter()
                .any(|expected_fragment| message.contains(expected_fragment)),
            "{case} ({upstream_case}) error should contain one of {expected_fragments:?}, got: {message}"
        );
    }
}
