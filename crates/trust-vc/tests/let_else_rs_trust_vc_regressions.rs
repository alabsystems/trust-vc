// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the accepted upstream let_else.rs port.

use std::path::PathBuf;
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn let_else_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../evals/verus/ported/let_else/src/lib.rs")
}

const VERIFIED_CASES: &[(&str, &str)] = &[
    (
        "let_else_irrefutable_binding",
        "let_else_just_a_normal_var::test",
    ),
    (
        "let_else_option_some_path",
        "test_let_else_returns Some success-path smoke",
    ),
    (
        "let_else_option_symbolic_refutable_path",
        "test_let_else_returns symbolic refutable Option subset",
    ),
    (
        "let_else_custom_enum_early_return_postcondition",
        "test_let_else_returns custom enum early-return postcondition",
    ),
    (
        "let_else_custom_enum_dotted_pattern_extracts_fields",
        "test_let_else_dots custom enum dotted pattern field binding",
    ),
    (
        "let_else_dotted_pattern_loop_else_verified",
        "test_let_else_dots diverging else path",
    ),
];

const FAIL_CLOSED_CASES: &[(&str, &str)] = &[
    (
        "let_else_verus_parse_else_counterexample",
        "let_else_verus_parse_else",
    ),
    (
        "let_else_irrefutable_binding_false_counterexample",
        "let_else_just_a_normal_var::test_fails",
    ),
    (
        "let_else_custom_enum_wrong_else_return_counterexample",
        "test_let_else_ensures_failed_no_unwind_condition2",
    ),
];

const EXTRACTION_BLOCKED_CASES: &[(&str, &str, &str)] = &[
    (
        "let_else_not_supported_in_proof_mode",
        "let_else_not_supported_in_proof",
        "let-else in spec/proof",
    ),
    (
        "let_else_not_supported_in_spec_mode",
        "let_else_not_supported_in_spec",
        "let-else in spec/proof",
    ),
];

#[test]
fn let_else_rs_verified_subset_verifies_from_file() {
    let path = let_else_port_path();
    let path = path.to_str().expect("let_else port path should be UTF-8");

    for (case, upstream_case) in VERIFIED_CASES {
        let result = verify_function_from_file(path, case)
            .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn let_else_rs_wrong_else_return_fails_closed_from_file() {
    let path = let_else_port_path();
    let path = path.to_str().expect("let_else port path should be UTF-8");

    for (case, upstream_case) in FAIL_CLOSED_CASES {
        let result = verify_function_from_file(path, case)
            .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
        assert!(
            matches!(
                result,
                VerifyResult::Counterexample { .. } | VerifyResult::Unknown { .. }
            ),
            "{case} ({upstream_case}) must not verify, got: {result:?}"
        );
    }
}

#[test]
fn let_else_rs_unsupported_surfaces_fail_closed_from_file() {
    let path = let_else_port_path();
    let path = path.to_str().expect("let_else port path should be UTF-8");

    for (case, upstream_case, expected) in EXTRACTION_BLOCKED_CASES {
        let err = verify_function_from_file(path, case)
            .expect_err("unsupported let-else surface should fail during extraction");
        let message = err.to_string();
        assert!(
            message.contains(expected),
            "{case} ({upstream_case}) should report {expected:?}, got: {message}"
        );
    }
}
