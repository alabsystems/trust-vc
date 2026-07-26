// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the faithful 1:1 upstream z3_restart.rs TrustVc port.
//!
//! Upstream `z3_restart.rs` is a 7-case mashup of `nonlinear.rs`,
//! `adts_generics.rs`, `multiset.rs`, and `examples/bitvector_basic.rs`, run
//! under Verus's z3 spinoff/restart scheduling. Every case is reproduced with
//! its upstream verdict; multi-fn upstream cases map several port fns to one
//! `upstream_case_id`.
//!
//! `spinoff_prover` is a solver-SCHEDULING knob with no verdict semantics —
//! TrustVc already discharges each obligation as its own query, so ignoring it
//! is verdict-equivalent.
//!
//! These tests pin the case mapping, the per-case verdicts, exact agreement
//! with the corpus manifest row, and — because the port carries ONE documented
//! deviation (see `test_with_bitvec_nlarith` below) — the soundness controls
//! that show the deviation removes hypotheses rather than obligations.

mod common;

use std::{collections::BTreeSet, path::PathBuf};
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn z3_restart_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/z3_restart.rs")
}

fn verus_manifest_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn pinned_upstream_z3_restart_path() -> PathBuf {
    common::pinned_verus_test_path("z3_restart.rs")
}

/// Every upstream `test_verify_one_file!` case id, in pinned order. All 7 are
/// mapped by the port; none is `#[ignore]`d upstream.
const UPSTREAM_CASES: &[&str] = &[
    "test_with_bitvec_nlarith",
    "test_box_unbox_struct",
    "test_with_nlarith",
    "test_with_bv",
    "test1_fails",
    "test2_fails",
    "multiset_basics",
];

const EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "test_with_bitvec_nlarith",
        "test_with_bitvec_nlarith",
        "verified",
        1,
    ),
    (
        "test_box_unbox_struct_one",
        "test_box_unbox_struct",
        "verified",
        1,
    ),
    (
        "test_box_unbox_struct_two",
        "test_box_unbox_struct",
        "verified",
        1,
    ),
    ("test_with_nlarith", "test_with_nlarith", "verified", 1),
    ("test_with_bv", "test_with_bv", "verified", 1),
    ("test1_fails", "test1_fails", "counterexample", 1),
    ("test2_fails", "test2_fails", "counterexample", 1),
    (
        "multiset_basics_commutative",
        "multiset_basics",
        "verified",
        1,
    ),
    (
        "multiset_basics_associative",
        "multiset_basics",
        "verified",
        1,
    ),
    ("multiset_basics_insert2", "multiset_basics", "verified", 1),
    (
        "multiset_basics_insert2_count",
        "multiset_basics",
        "verified",
        1,
    ),
    (
        "multiset_basics_add_sub_cancel",
        "multiset_basics",
        "verified",
        1,
    ),
    (
        "multiset_basics_sub_add_cancel",
        "multiset_basics",
        "counterexample",
        1,
    ),
];

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("z3_restart port should define {const_name}"));

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
    let array = referenced_array_const(file, "Z3_RESTART_RS_EXPECTED_CASES");
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
            "duplicate z3_restart metadata for {case_id}"
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
    EXPECTED_CASES
        .iter()
        .map(
            |(case_id, upstream_case_id, expected_verdict, min_obligations)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: (*expected_verdict).to_string(),
                min_obligations: *min_obligations,
            },
        )
        .collect()
}

/// The accepted-corpus manifest pins `min_obligations` to the exact observed
/// obligation count, which is >= the lower bound declared in the port's own
/// metadata table. Compare every other field exactly.
fn assert_matches_manifest(port: &[CaseMetadata], manifest: &[CaseMetadata]) {
    assert_eq!(
        port.len(),
        manifest.len(),
        "port and manifest should agree on the case count"
    );
    for (port_case, manifest_case) in port.iter().zip(manifest.iter()) {
        assert_eq!(port_case.case_id, manifest_case.case_id);
        assert_eq!(port_case.upstream_case_id, manifest_case.upstream_case_id);
        assert_eq!(port_case.expected_verdict, manifest_case.expected_verdict);
        assert!(
            manifest_case.min_obligations >= port_case.min_obligations,
            "manifest min_obligations for {} ({}) should be at least the port lower bound {}",
            manifest_case.case_id,
            manifest_case.min_obligations,
            port_case.min_obligations
        );
    }
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
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/z3_restart.rs")
        })
        .expect("Verus manifest should contain z3_restart.rs row");

    row["expected_cases"]
        .as_array()
        .expect("z3_restart.rs row should contain expected_cases")
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

/// The corpus `counterexample` expectation means "assert_fails": either a
/// genuine model-bearing counterexample OR a model-less incompleteness
/// non-proof, which maps to the gate's `counterexample` label per
/// design-unknown-as-failure.md. Never a fabricated model.
fn is_rejected(result: &VerifyResult) -> bool {
    match result {
        VerifyResult::Counterexample { .. } => true,
        // The incompleteness non-proof (Verus's Invalid(None,None,None)). Since
        // `docs/design-unknown-as-failure.md` landed, an obligation-scoped
        // incompleteness surfaces as the dedicated `NotProved` FAILURE rather
        // than a soft `Unknown{Incompleteness}`; both spellings are "rejected".
        VerifyResult::NotProved { .. } => true,
        // A residual soft Unknown only counts as a rejection when it is a
        // genuine incompleteness (kept for robustness; obligation-scoped
        // incompleteness now takes the NotProved arm above).
        VerifyResult::Unknown { category, .. } => category.is_incompleteness(),
        _ => false,
    }
}

fn verify_case(case: &str) -> VerifyResult {
    let path = z3_restart_port_path();
    let path = path.to_str().expect("z3_restart port path should be UTF-8");
    verify_function_from_file(path, case)
        .unwrap_or_else(|err| panic!("{case} should extract: {err}"))
}

fn verify_fixture(source: &str, case: &str) -> VerifyResult {
    let mut path = std::env::temp_dir();
    path.push(format!("tvc_z3_restart_{}_{case}.rs", std::process::id()));
    std::fs::write(&path, source).expect("write control fixture");
    let result = verify_function_from_file(path.to_str().expect("fixture path"), case)
        .unwrap_or_else(|err| VerifyResult::Error {
            message: err.to_string(),
        });
    let _ = std::fs::remove_file(&path);
    result
}

#[test]
fn z3_restart_rs_port_file_is_rust_syntax() {
    let source =
        std::fs::read_to_string(z3_restart_port_path()).expect("z3_restart port should read");
    syn::parse_file(&source).expect("z3_restart port should parse as ordinary Rust syntax");
}

#[test]
fn z3_restart_rs_expected_case_metadata_is_exact() {
    let source =
        std::fs::read_to_string(z3_restart_port_path()).expect("z3_restart port should read");
    let file =
        syn::parse_file(&source).expect("z3_restart port should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), expected_metadata());
    assert!(
        source.contains("z3_restart_rs_expected_cases"),
        "z3_restart port should export expected-case metadata"
    );
}

#[test]
fn z3_restart_rs_expected_case_metadata_matches_manifest() {
    let source =
        std::fs::read_to_string(z3_restart_port_path()).expect("z3_restart port should read");
    let file =
        syn::parse_file(&source).expect("z3_restart port should parse as ordinary Rust syntax");
    assert_matches_manifest(&metadata_entries(&file), &manifest_expected_metadata());
}

/// Every upstream case id is mapped by at least one expected case (via
/// `upstream_case_id`), and every port fn named by a `case_id` exists.
#[test]
fn z3_restart_rs_expected_cases_cover_upstream_one_to_one() {
    let mapped: BTreeSet<&str> = EXPECTED_CASES
        .iter()
        .map(|(_, upstream_case_id, _, _)| *upstream_case_id)
        .collect();
    for upstream_case in UPSTREAM_CASES {
        assert!(
            mapped.contains(upstream_case),
            "upstream case {upstream_case} should be mapped by the port"
        );
    }
    assert_eq!(
        mapped.len(),
        UPSTREAM_CASES.len(),
        "the port should not claim upstream cases that do not exist"
    );

    let source =
        std::fs::read_to_string(z3_restart_port_path()).expect("z3_restart port should read");
    let parsed = syn::parse_file(&source).expect("z3_restart port should parse");
    for (case_id, _, _, _) in EXPECTED_CASES {
        let found = parsed.items.iter().any(|item| match item {
            syn::Item::Fn(function) => function.sig.ident == case_id,
            _ => false,
        });
        assert!(found, "{case_id} should be a top-level port fn");
    }
}

#[test]
fn z3_restart_rs_verified_subset_verifies_from_file() {
    for (case, upstream_case, _, _) in EXPECTED_CASES
        .iter()
        .filter(|(_, _, verdict, _)| *verdict == "verified")
    {
        let result = verify_case(case);
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} ({upstream_case}) should verify, got: {result:?}"
        );
    }
}

#[test]
fn z3_restart_rs_counterexample_subset_is_rejected_from_file() {
    for (case, upstream_case, _, _) in EXPECTED_CASES
        .iter()
        .filter(|(_, _, verdict, _)| *verdict == "counterexample")
    {
        let result = verify_case(case);
        assert!(
            is_rejected(&result),
            "{case} ({upstream_case}) should be rejected (counterexample or incompleteness non-proof), got: {result:?}"
        );
    }
}

/// upstream `test2_fails` (= `wrong_lemma_2`) and the trailing `assert(false)`
/// in `multiset_basics::sub_add_cancel` are model-BEARING counterexamples: the
/// port must never stand in a model-less non-proof for these.
#[test]
fn z3_restart_rs_model_bearing_failures_stay_model_bearing() {
    for case in ["test2_fails", "multiset_basics_sub_add_cancel"] {
        let result = verify_case(case);
        assert!(
            matches!(result, VerifyResult::Counterexample { model: Some(_), .. }),
            "{case} should be a model-bearing counterexample, got: {result:?}"
        );
    }
}

/// upstream `test1_fails`: the FAILS obligation is `((b << 2) as int) == (b as
/// int) * 4`, which is GENUINELY FALSE (`b << 2` truncates at 32 bits). On its
/// own it is a model-bearing counterexample. In the full upstream shape the
/// preceding nonlinear by-assert's product fact drives the same query into the
/// known BV<->Int bridge incompleteness, so the port's fn reports a model-less
/// incompleteness non-proof instead. Pin BOTH facts, so a future engine fix that
/// promotes the fn to a model-bearing counterexample is visible, and a
/// regression that makes the obligation VERIFY is caught.
const T1_FAILS_ISOLATED_OBLIGATION: &str = r#"
use trust_vc_types::int;

#[trust_vc::ensures(true)]
fn t1_fails_isolated(b: u32) {
    trust_vc::assert!(((b << 2u32) as int) == (b as int) * 4); // FAILS
}

// the two non-FAILS upstream obligations, on their own
#[trust_vc::verifier(spinoff_prover)]
#[trust_vc::ensures(true)]
fn t1_fails_prefix(b: u32, b2: u32) {
    trust_vc::assert_by_nonlinear!(b * b2 == b2 * b);
    trust_vc::assert_by_bit_vector!(b << 2u32 == mul(b, 4u32));
}
"#;

#[test]
fn z3_restart_rs_test1_fails_obligation_is_genuinely_false() {
    let isolated = verify_fixture(T1_FAILS_ISOLATED_OBLIGATION, "t1_fails_isolated");
    assert!(
        matches!(isolated, VerifyResult::Counterexample { model: Some(_), .. }),
        "the upstream test1_fails FAILS obligation must be a model-bearing counterexample in isolation, got: {isolated:?}"
    );

    let prefix = verify_fixture(T1_FAILS_ISOLATED_OBLIGATION, "t1_fails_prefix");
    assert!(
        matches!(prefix, VerifyResult::Verified),
        "the two non-FAILS upstream test1_fails obligations must verify on their own, got: {prefix:?}"
    );
}

/// The port's ONE deviation: in `test_with_bitvec_nlarith` the trailing
/// `x * y * z == y * x * z` nonlinear by-assert is hoisted ABOVE the bit-vector
/// by-assert, because TrustVc cannot encode a bit-vector-derived general `&`
/// fact as an assumption of a subsequent nonlinear-solver query.
///
/// The hoist is obligation-preserving and never weakening. Pin it:
///   1. the hoisted goal holds WITHOUT the bit-vector fact (strictly harder);
///   2. the post-hoist context is not inconsistent (`assert(false)` still fails),
///      so the bit-vector obligations are not proved vacuously;
///   3. upstream's literal statement order still hard-errors, so the deviation
///      is forced, not chosen.
const BITVEC_NLARITH_CONTROLS: &str = r#"
// (1) the hoisted nonlinear goal, with NO bit-vector fact in scope
#[trust_vc::ensures(true)]
fn hoisted_goal_alone(x: u32, y: u32, z: u32) {
    trust_vc::assert_by_nonlinear!(x * y * z == y * x * z);
}

// (2) the post-hoist context must not be inconsistent
#[trust_vc::verifier(spinoff_prover)]
#[trust_vc::requires(x < 0xfffu32)]
#[trust_vc::ensures(true)]
fn hoisted_context_not_inconsistent(x: u32, y: u32, z: u32) {
    trust_vc::assert_by_nonlinear!(x * y * z == y * x * z);
    trust_vc::assert_by_bit_vector!(!(x < 0xfffu32) || (x & y < 0xfffu32));
    trust_vc::assert!(false); // must fail
}

// (3) upstream's literal order: a BV-derived `&` fact feeding a nonlinear query
#[trust_vc::verifier(spinoff_prover)]
#[trust_vc::requires(x < 0xfffu32)]
#[trust_vc::ensures(true)]
fn upstream_order(x: u32, y: u32, z: u32) {
    trust_vc::assert_by_bit_vector!(!(x < 0xfffu32) || (x & y < 0xfffu32));
    trust_vc::assert!(x & y < 0xfffu32);
    trust_vc::assert_by_nonlinear!(x * y * z == y * x * z);
}
"#;

#[test]
fn z3_restart_rs_bitvec_nlarith_hoist_is_not_a_weakening() {
    let alone = verify_fixture(BITVEC_NLARITH_CONTROLS, "hoisted_goal_alone");
    assert!(
        matches!(alone, VerifyResult::Verified),
        "the hoisted nonlinear goal must hold without the bit-vector fact, got: {alone:?}"
    );

    let consistent = verify_fixture(BITVEC_NLARITH_CONTROLS, "hoisted_context_not_inconsistent");
    assert!(
        is_rejected(&consistent),
        "the post-hoist context must not be inconsistent, got: {consistent:?}"
    );
}

/// The hoist is FORCED by an engine limitation, not chosen for convenience. If
/// this ever starts passing, restore upstream's literal statement order.
#[test]
fn z3_restart_rs_upstream_statement_order_still_hard_errors() {
    let result = verify_fixture(BITVEC_NLARITH_CONTROLS, "upstream_order");
    let VerifyResult::Error { message } = &result else {
        panic!(
            "upstream's literal statement order is expected to hard-error on the \
             bit-vector-fact-into-nonlinear-query assumption encoder; it now yields \
             {result:?} — restore upstream order in the port and delete this test"
        );
    };
    assert!(
        message.contains("BitAnd (&) in quantifier body only supports power-of-2 masks"),
        "unexpected hard-error for upstream statement order: {message}"
    );
}

/// The pinned upstream file's shape must not drift: case order and verdict
/// counts (4 x Ok, 3 x assert_one_fails, no `#[ignore]`).
#[test]
fn z3_restart_rs_pinned_upstream_shape_stays_expected() {
    let path = pinned_upstream_z3_restart_path();
    if !path.exists() {
        eprintln!(
            "skipping pinned upstream z3_restart.rs shape check; missing {}",
            path.display()
        );
        return;
    }

    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()));

    let mut previous = 0;
    for case in UPSTREAM_CASES {
        let marker = format!("\n    #[test] {case}");
        let current = source
            .find(&marker)
            .unwrap_or_else(|| panic!("upstream z3_restart.rs should contain case {case}"));
        assert!(
            current >= previous,
            "upstream z3_restart.rs case {case} should stay in pinned order"
        );
        previous = current;
    }

    assert_eq!(
        source.matches("=> Ok(())").count(),
        4,
        "upstream z3_restart.rs verified-case count should stay pinned"
    );
    assert_eq!(
        source.matches("assert_one_fails").count(),
        3,
        "upstream z3_restart.rs one-failure count should stay pinned"
    );
    assert_eq!(
        source.matches("#[ignore]").count(),
        0,
        "upstream z3_restart.rs has no ignored cases"
    );
    assert!(
        source.contains("assert(false) // FAILS"),
        "upstream multiset_basics sub_add_cancel should keep its trailing assert(false)"
    );
}
