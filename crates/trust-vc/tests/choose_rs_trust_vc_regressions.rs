// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the faithful 1:1 upstream choose.rs port.
//!
//! Upstream `rust_verify_test/tests/choose.rs` is a sequence of
//! `test_verify_one_file!` blocks, and each block is its own compilation unit.
//! Three helper names are declared twice upstream at DIFFERENT ARITIES (`f`,
//! `cnatf`, `cintf`), so the port carries upstream's own compilation-unit
//! boundary: the single-binder half is `evals/verus/ported/choose.rs` and the
//! multi-binder / `choose_tuple` half is `evals/verus/ported/choose_tuple.rs`.
//! Together they reproduce all 17 upstream harness cases (the two
//! multi-subproof cases `test1` and `test1_tuple` are split into their upstream
//! subproofs, for 20 executable functions). These tests prove that every case
//! reproduces its upstream verdict — 10 verified, 8 counterexample, 2 compile
//! errors — and that each port file's expected-case table, this file's
//! `EXPECTED_CASES` table, and the corpus manifest row all agree exactly.

use std::{collections::BTreeSet, path::PathBuf};
use trust_vc_core::vc::VerificationContext;
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::{verify_function_from_file, VerifyResult};

/// `(port_path, case_id, upstream_case_id, expected_verdict, min_obligations)`.
type ExpectedCase = (
    &'static str,
    &'static str,
    &'static str,
    &'static str,
    usize,
);

const CHOOSE_PORT: &str = "evals/verus/ported/choose.rs";
const CHOOSE_TUPLE_PORT: &str = "evals/verus/ported/choose_tuple.rs";

/// The port files, each paired with the expected-case table it must declare.
const PORT_FILES: &[(&str, &str)] = &[
    (CHOOSE_PORT, "CHOOSE_RS_EXPECTED_CASES"),
    (CHOOSE_TUPLE_PORT, "CHOOSE_TUPLE_RS_EXPECTED_CASES"),
];

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    trust_vc_path: String,
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
}

/// Case metadata for the faithful 20-function choose.rs port, in the order the
/// manifest row declares it: the single-binder file first, then the
/// multi-binder file. The `min_obligations` values are pinned from a passing
/// corpus refresh and must stay identical across this table, each port file's
/// own expected-case table, and the manifest row.
const EXPECTED_CASES: &[ExpectedCase] = &[
    (CHOOSE_PORT, "test1_choose", "test1", "verified", 3),
    (
        CHOOSE_PORT,
        "test1_choose_inference",
        "test1",
        "verified",
        3,
    ),
    (CHOOSE_PORT, "test1_choose_eq", "test1", "verified", 2),
    (
        CHOOSE_PORT,
        "test1_fails1",
        "test1_fails1",
        "counterexample",
        2,
    ),
    (
        CHOOSE_PORT,
        "test1_fails2",
        "test1_fails2",
        "counterexample",
        3,
    ),
    (
        CHOOSE_PORT,
        "test1_fails3",
        "test1_fails3",
        "counterexample",
        2,
    ),
    (CHOOSE_PORT, "test_refine", "test_refine", "verified", 3),
    (
        CHOOSE_PORT,
        "test_refine_fail1",
        "test_refine_fail1",
        "counterexample",
        3,
    ),
    (CHOOSE_PORT, "test_refine2", "test_refine2", "verified", 3),
    (
        CHOOSE_TUPLE_PORT,
        "test1_choose_with_closure_illegal",
        "test1_choose_with_closure_illegal",
        "error",
        0,
    ),
    (
        CHOOSE_TUPLE_PORT,
        "test1_tuple_choose",
        "test1_tuple",
        "verified",
        3,
    ),
    (
        CHOOSE_TUPLE_PORT,
        "test1_tuple_choose_eq",
        "test1_tuple",
        "verified",
        3,
    ),
    (
        CHOOSE_TUPLE_PORT,
        "test1_fails1_tuple",
        "test1_fails1_tuple",
        "counterexample",
        2,
    ),
    (
        CHOOSE_TUPLE_PORT,
        "test1_fails2_tuple",
        "test1_fails2_tuple",
        "counterexample",
        3,
    ),
    (
        CHOOSE_TUPLE_PORT,
        "test1_fails3_tuple",
        "test1_fails3_tuple",
        "counterexample",
        2,
    ),
    (
        CHOOSE_TUPLE_PORT,
        "test_refine_tuple",
        "test_refine_tuple",
        "verified",
        3,
    ),
    (
        CHOOSE_TUPLE_PORT,
        "test_refine_fail1_tuple",
        "test_refine_fail1_tuple",
        "counterexample",
        3,
    ),
    (
        CHOOSE_TUPLE_PORT,
        "test_refine2_tuple",
        "test_refine2_tuple",
        "verified",
        3,
    ),
    (
        CHOOSE_TUPLE_PORT,
        "test1_choose_tuple_wrong_type",
        "test1_choose_tuple_wrong_type",
        "error",
        0,
    ),
    (
        CHOOSE_TUPLE_PORT,
        "test1_choose_tuple_no_ascription_regression_1183",
        "test1_choose_tuple_no_ascription_regression_1183",
        "verified",
        3,
    ),
];

/// The two malformed upstream inputs and the verbatim Verus diagnostic each must
/// reproduce through the general frontend body-extraction checks.
const ERROR_CASE_PATTERNS: &[(&str, &str)] = &[
    (
        "test1_choose_with_closure_illegal",
        "forall, choose, and exists do not allow parentheses",
    ),
    (
        "test1_choose_tuple_wrong_type",
        "expected choose_tuple to have type",
    ),
];

fn repo_path(relative: &str) -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(relative)
}

fn verus_manifest_path() -> PathBuf {
    repo_path("evals/verus/verus-tests.json")
}

fn port_ast(relative: &str) -> syn::File {
    let source = std::fs::read_to_string(repo_path(relative))
        .unwrap_or_else(|err| panic!("{relative} should be readable: {err}"));
    syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("{relative} should parse as ordinary Rust syntax: {err}"))
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("choose port should define {const_name}"));

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

/// Every port file's own expected-case table, concatenated in `PORT_FILES`
/// order and tagged with the file that declared it.
fn metadata_entries() -> Vec<CaseMetadata> {
    let mut seen = BTreeSet::new();
    let mut entries = Vec::new();

    for (port_path, const_name) in PORT_FILES {
        let file = port_ast(port_path);
        let array = referenced_array_const(&file, const_name);

        for entry in &array.elems {
            let syn::Expr::Tuple(tuple) = entry else {
                panic!("expected tuple expected-case metadata entry");
            };
            assert_eq!(
                tuple.elems.len(),
                4,
                "expected-case entries should have case, upstream case, verdict, and min \
                 obligations"
            );
            let case_id = literal_string(&tuple.elems[0]);
            assert!(
                seen.insert(case_id.clone()),
                "duplicate choose metadata for {case_id}"
            );
            entries.push(CaseMetadata {
                trust_vc_path: (*port_path).to_string(),
                case_id,
                upstream_case_id: literal_string(&tuple.elems[1]),
                expected_verdict: literal_string(&tuple.elems[2]),
                min_obligations: literal_usize(&tuple.elems[3]),
            });
        }
    }

    entries
}

fn expected_metadata() -> Vec<CaseMetadata> {
    EXPECTED_CASES
        .iter()
        .map(
            |(port_path, case_id, upstream_case_id, expected_verdict, min_obligations)| {
                CaseMetadata {
                    trust_vc_path: (*port_path).to_string(),
                    case_id: (*case_id).to_string(),
                    upstream_case_id: (*upstream_case_id).to_string(),
                    expected_verdict: (*expected_verdict).to_string(),
                    min_obligations: *min_obligations,
                }
            },
        )
        .collect()
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/choose.rs")
        })
        .expect("Verus manifest should contain choose.rs row");

    let declared_paths: Vec<&str> = row["trust_vc_paths"]
        .as_array()
        .expect("choose.rs row should declare trust_vc_paths")
        .iter()
        .map(|value| value.as_str().expect("trust_vc_path should be a string"))
        .collect();
    assert_eq!(
        declared_paths,
        PORT_FILES.iter().map(|(path, _)| *path).collect::<Vec<_>>(),
        "the manifest row must bind exactly the two port files, in order"
    );

    row["expected_cases"]
        .as_array()
        .expect("choose.rs row should contain expected_cases")
        .iter()
        .map(|entry| CaseMetadata {
            trust_vc_path: entry["trust_vc_path"]
                .as_str()
                .expect("trust_vc_path should be a string")
                .to_string(),
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

fn assert_verified(path: &str, case: &str, upstream_case: &str) {
    let result = verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
    assert!(
        matches!(result, VerifyResult::Verified),
        "{case} ({upstream_case}) should verify, got: {result:?}"
    );
}

/// The corpus `counterexample` verdict is upstream's `assert_fails`, which only
/// requires that the obligation FAILS — upstream's `assert_one_fails` never
/// inspects a model (verus common/mod.rs). Verus itself produces two shapes of
/// that failure: a model-bearing `Invalid(Some(model), ..)` and a model-LESS
/// `Invalid(None, None, None)` when Z3 answers `unknown` from incompleteness.
/// trust-vc mirrors both: `VerifyResult::Counterexample` and
/// `VerifyResult::NotProved` respectively (`docs/design-unknown-as-failure.md`).
///
/// `test1_fails1` is exactly the model-less case: its VC is semantically UNSAT
/// (the triggerless `choose` axiom instantiated at `y := 5` contradicts `c < 5`),
/// so NO model exists and none may be invented — upstream only "fails" it
/// because Z3's e-matching never fires without a ground witness term.
///
/// A soft `Unknown` is still rejected: that is the pre-fix divergence.
fn assert_counterexample(path: &str, case: &str, upstream_case: &str) {
    let result = verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} ({upstream_case}) should extract: {err}"));
    assert!(
        result.is_failure(),
        "{case} ({upstream_case}) should FAIL (model-bearing counterexample or model-less \
         non-proof), got: {result:?}"
    );
}

/// The two malformed upstream inputs must be rejected with the upstream Verus
/// diagnostic. TrustVc surfaces the body-extraction diagnostic either as an
/// extraction `Err` (the common path) or as a `VerifyResult::Error`; both carry
/// the verbatim message, and both are accepted here so long as the expected
/// pattern is present. Any success verdict is a hard failure.
fn assert_error(path: &str, case: &str, upstream_case: &str, pattern: &str) {
    let message = match verify_function_from_file(path, case) {
        Err(err) => err.to_string(),
        Ok(VerifyResult::Error { message }) => message,
        Ok(other) => {
            panic!("{case} ({upstream_case}) should be rejected as an error, got: {other:?}")
        }
    };
    assert!(
        message.contains(pattern),
        "{case} ({upstream_case}) error message should contain {pattern:?}, got: {message}"
    );
}

fn verify_context(context: VerificationContext) -> VerifyResult {
    let mut pipeline = VerificationPipeline::new();
    pipeline.replace_context(context);
    pipeline.verify()
}

#[test]
fn choose_rs_expected_case_metadata_is_exact() {
    assert_eq!(metadata_entries(), expected_metadata());
}

#[test]
fn choose_rs_expected_case_metadata_matches_manifest() {
    assert_eq!(metadata_entries(), manifest_expected_metadata());
}

/// Upstream declares `f`, `cnatf` and `cintf` at two arities in two different
/// compilation units, and the port keeps upstream's own names by keeping
/// upstream's own unit boundary. So NEITHER port file may reintroduce a
/// disambiguating rename: a name the port invents corresponds to no upstream
/// statement, which is what the corpus gate's claim comparison catches.
///
/// Read off the parsed AST's item names and the CODE of each line (the port
/// headers discuss `f2`/`cnatf2`/`cintf2` by name, and a comment is not a
/// claim), so this pins the spelling the gate actually reads.
#[test]
fn choose_ports_use_upstream_helper_names_only() {
    const INVENTED: &[&str] = &["f2", "cnatf2", "cintf2"];

    for (port_path, _) in PORT_FILES {
        let source = std::fs::read_to_string(repo_path(port_path))
            .unwrap_or_else(|err| panic!("{port_path} should be readable: {err}"));

        for item in &port_ast(port_path).items {
            if let syn::Item::Fn(item) = item {
                let name = item.sig.ident.to_string();
                assert!(
                    !INVENTED.contains(&name.as_str()),
                    "{port_path} must not declare a helper `{name}`; upstream never writes it"
                );
            }
        }

        // The port files carry no string literal containing `//`, so cutting
        // each line at its first `//` leaves exactly the code.
        for (number, line) in source.lines().enumerate() {
            let code = line.split("//").next().unwrap_or("");
            for invented in INVENTED {
                assert!(
                    !code.contains(invented),
                    "{port_path}:{} spells `{invented}` in code; upstream never writes it, so a \
                     claim naming it corresponds to no upstream statement",
                    number + 1
                );
            }
        }
    }
}

#[test]
fn choose_rs_verified_subset_verifies_from_file() {
    for &(port_path, case, upstream_case, verdict, _) in EXPECTED_CASES {
        if verdict == "verified" {
            let path = repo_path(port_path);
            let path = path.to_str().expect("port path should be UTF-8");
            assert_verified(path, case, upstream_case);
        }
    }
}

#[test]
fn choose_rs_counterexample_subset_fails_from_file() {
    for &(port_path, case, upstream_case, verdict, _) in EXPECTED_CASES {
        if verdict == "counterexample" {
            let path = repo_path(port_path);
            let path = path.to_str().expect("port path should be UTF-8");
            assert_counterexample(path, case, upstream_case);
        }
    }
}

#[test]
fn choose_rs_error_subset_reports_upstream_diagnostic_from_file() {
    // Every EXPECTED_CASES `error` entry must have a pinned diagnostic pattern,
    // and vice versa, so neither table can silently drop the other.
    let error_cases: BTreeSet<&str> = EXPECTED_CASES
        .iter()
        .filter(|(_, _, _, verdict, _)| *verdict == "error")
        .map(|(_, case, _, _, _)| *case)
        .collect();
    let patterned_cases: BTreeSet<&str> =
        ERROR_CASE_PATTERNS.iter().map(|(case, _)| *case).collect();
    assert_eq!(
        error_cases, patterned_cases,
        "every error case must pin exactly one diagnostic pattern"
    );

    for &(case, pattern) in ERROR_CASE_PATTERNS {
        let (port_path, upstream_case) = EXPECTED_CASES
            .iter()
            .find(|(_, c, _, _, _)| *c == case)
            .map(|(port_path, _, upstream, _, _)| (*port_path, *upstream))
            .expect("error case should appear in EXPECTED_CASES");
        let path = repo_path(port_path);
        let path = path.to_str().expect("port path should be UTF-8");
        assert_error(path, case, upstream_case, pattern);
    }
}

#[test]
fn choose_rs_multi_binder_inline_tuple_projection_verifies() {
    let choose = "choose|i: int, j: int| i <= j";
    let mut ctx = VerificationContext::new();
    ctx.push_assert(
        "multi_binder_projection_order",
        &format!("({choose}).0 <= ({choose}).1"),
    );

    let result = verify_context(ctx);
    assert!(
        matches!(result, VerifyResult::Verified),
        "inline multi-binder choose tuple projections should verify, got: {result:?}"
    );
}
