// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the TrustVc port of upstream `assert_forall_by.rs`
//! (pinned ref a40d57c73650cd3648b09386bfdb96ab5c270626, 17 cases).
//!
//! All 17 upstream cases now have a TrustVc fn. The manifest row is STILL
//! `unsupported-gap` until a green validation run + evidence refresh land — see
//! that row's `reason`. Three engine features carry the last four cases:
//!
//!   * PROOF-MODE VARIABLES — `test_assertby1_fail3`, `test_forallstmt1_fail3`
//!     (the rejection "expression has mode spec, expected mode proof" when a
//!     `tracked` proof var is CONSUMED inside a by-block) and the third fn of
//!     `test_forallstmt1` (the positive counterpart, which must VERIFY).
//!   * THE `implies` KEYWORD — upstream `test_forallstmt2` / `_fails1` use it;
//!     its by-block ASSUMES the antecedent and it emits NO warning, unlike `==>`.
//!   * VERIFIER WARNINGS — `test_forallstmt_implies` asserts the `==>` warning.
//!
//! Every `upstream_case_id` here is a REAL upstream `#[test]` name.

use std::{collections::BTreeSet, path::PathBuf};
use trust_vc_core::{
    extract_verification_conditions_with_file_context, parse_file_allow_tracked,
    vc::VerificationContext, VerifyResult,
};

/// The verbatim Verus warning upstream `test_forallstmt_implies` content-checks.
const IMPLIES_ARROW_WARNING: &str =
    "using ==> in `assert forall` does not currently assume the antecedent in the body";

type ExpectedCase = (&'static str, &'static str, &'static str, usize);

#[derive(Debug, Eq, PartialEq)]
struct CaseMetadata {
    case_id: String,
    upstream_case_id: String,
    expected_verdict: String,
    min_obligations: usize,
}

const EXPECTED_CASES: &[ExpectedCase] = &[
    ("assertby_test", "test_assertby1", "verified", 2),
    (
        "assertby_test_fail1",
        "test_assertby1_fail1",
        "counterexample",
        1,
    ),
    (
        "assertby_test_fail2",
        "test_assertby1_fail2",
        "counterexample",
        3,
    ),
    (
        "assertby_proof_var_disallowed",
        "test_assertby1_fail3",
        "error",
        0,
    ),
    ("forallstmt_test", "test_forallstmt1", "verified", 3),
    (
        "forallstmt_test_inference",
        "test_forallstmt1",
        "verified",
        3,
    ),
    (
        "forallstmt_proof_var_allowed_as_spec",
        "test_forallstmt1",
        "verified",
        2,
    ),
    (
        "forallstmt_test_fail1",
        "test_forallstmt1_fail1",
        "counterexample",
        1,
    ),
    (
        "forallstmt_test_fail2",
        "test_forallstmt1_fail2",
        "counterexample",
        3,
    ),
    (
        "forallstmt_proof_var_disallowed",
        "test_forallstmt1_fail3",
        "error",
        0,
    ),
    ("forallstmt2_test", "test_forallstmt2", "verified", 3),
    (
        "forallstmt2_test_fails1",
        "test_forallstmt2_fails1",
        "counterexample",
        3,
    ),
    (
        "forallstmt2_test_fails2",
        "test_forallstmt2_fails2",
        "counterexample",
        1,
    ),
    ("scope", "test_scope", "verified", 3),
    ("forallstmt_typ", "test_forallstmt_typ", "verified", 3),
    (
        "forallstmt_typ_fails",
        "test_forallstmt_typ_fails",
        "counterexample",
        1,
    ),
    ("assertby_let", "test_assertby1_let", "verified", 3),
    ("forallstmt_let", "test_forallstmt_let", "verified", 3),
    (
        "forallstmt_implies",
        "test_forallstmt_implies",
        "verified",
        1,
    ),
];

fn assert_forall_by_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../evals/verus/ported/assert_forall_by.rs")
}

fn verus_manifest_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn port_source_and_ast() -> (String, syn::File) {
    let path = assert_forall_by_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("assert_forall_by port should read: {err}"));
    let file = parse_file_allow_tracked(&source)
        .unwrap_or_else(|err| panic!("assert_forall_by port should parse: {err}"));
    (source, file)
}

fn referenced_array_const(file: &syn::File, const_name: &str) -> syn::ExprArray {
    let const_item = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Const(item) if item.ident == const_name => Some(item),
            _ => None,
        })
        .unwrap_or_else(|| panic!("assert_forall_by port should define {const_name}"));

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
    let array = referenced_array_const(file, "ASSERT_FORALL_BY_RS_EXPECTED_CASES");
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
            "duplicate assert_forall_by metadata for {case_id}"
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
            entry["upstream_path"].as_str()
                == Some("source/rust_verify_test/tests/assert_forall_by.rs")
        })
        .expect("Verus manifest should contain assert_forall_by.rs row");

    row["expected_cases"]
        .as_array()
        .expect("assert_forall_by.rs row should contain expected_cases")
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

/// The real upstream `#[test]` names of `assert_forall_by.rs`. Every
/// `upstream_case_id` the port claims must be one of these — the guard that
/// stops a port from inventing case ids.
const UPSTREAM_CASE_IDS: &[&str] = &[
    "test_assertby1",
    "test_assertby1_fail1",
    "test_assertby1_fail2",
    "test_assertby1_fail3",
    "test_forallstmt1",
    "test_forallstmt1_fail1",
    "test_forallstmt1_fail2",
    "test_forallstmt1_fail3",
    "test_forallstmt2",
    "test_forallstmt2_fails1",
    "test_forallstmt2_fails2",
    "test_scope",
    "test_forallstmt_typ",
    "test_forallstmt_typ_fails",
    "test_assertby1_let",
    "test_forallstmt_let",
    "test_forallstmt_implies",
];

fn try_extract_port_case(case: &str) -> Result<VerificationContext, String> {
    let (_source, file) = port_source_and_ast();
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == case => Some(func),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} should exist in assert_forall_by port"));

    extract_verification_conditions_with_file_context(&file, func).map_err(|err| err.to_string())
}

fn extract_port_case(case: &str) -> VerificationContext {
    try_extract_port_case(case).unwrap_or_else(|err| panic!("{case} should extract: {err}"))
}

fn verify_port_case(case: &str) -> (VerifyResult, usize) {
    let vc = extract_port_case(case);
    let obligations = vc.obligations().len();
    (vc.verify(), obligations)
}

/// Upstream `assert_one_fails` asserts an obligation FAILED; it never inspects a
/// model. A model-less theory-incompleteness `Unknown` is trust-vc's fail-closed
/// reading of exactly that outcome (design-unknown-as-failure.md; Verus
/// maps Z3's incompleteness `unknown` to `Invalid(None, None, None)` the same
/// way), so it belongs to the gate's `counterexample` class. This mirrors the
/// accepted z3_restart.rs port's `test1_fails`. A RESOURCE/timeout `Unknown`
/// stays `Unknown` and is NOT accepted here.
fn is_failure_verdict(result: &VerifyResult) -> bool {
    match result {
        VerifyResult::Counterexample { .. } => true,
        VerifyResult::Unknown { category, .. } => category.is_incompleteness(),
        // A model-less incompleteness non-proof is the same fail-closed rejection
        // whether the engine wraps it as `Unknown` or `NotProved`
        // (design-unknown-as-failure.md); e.g. `forallstmt_test_fail2` returns
        // NotProved "incomplete quantifier-ematching-exists".
        VerifyResult::NotProved { category, .. } => category.is_incompleteness(),
        _ => false,
    }
}

fn assert_verified(case: &str, upstream_case: &str, min_obligations: usize) {
    let (result, obligations) = verify_port_case(case);
    assert!(
        obligations >= min_obligations,
        "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
    );
    assert!(
        matches!(result, VerifyResult::Verified),
        "{case} ({upstream_case}) should verify, got: {result:?}"
    );
}

fn assert_counterexample(case: &str, upstream_case: &str, min_obligations: usize) {
    let (result, obligations) = verify_port_case(case);
    assert!(
        obligations >= min_obligations,
        "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligations}"
    );
    assert!(
        is_failure_verdict(&result),
        "{case} ({upstream_case}) should be rejected, got: {result:?}"
    );
}

#[test]
fn assert_forall_by_rs_expected_case_metadata_is_exact() {
    let (_source, file) = port_source_and_ast();
    assert_eq!(metadata_entries(&file), expected_metadata());
}

#[test]
fn assert_forall_by_rs_expected_case_metadata_matches_manifest() {
    let (_source, file) = port_source_and_ast();
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

/// GATE-INTEGRITY PIN: every `upstream_case_id` the port claims must be a real
/// upstream `#[test]` name. The previous port invented ids like "TrustVc routing
/// guard" and "bare assert forall statement guard"; those can never be checked
/// against upstream and must never come back.
#[test]
fn assert_forall_by_rs_upstream_case_ids_are_real() {
    for &(case_id, upstream_case_id, _, _) in EXPECTED_CASES {
        assert!(
            UPSTREAM_CASE_IDS.contains(&upstream_case_id),
            "{case_id} claims upstream case `{upstream_case_id}`, which is NOT an upstream \
             #[test] in assert_forall_by.rs. Invented upstream_case_ids are gate gaming."
        );
    }
}

#[test]
fn assert_forall_by_rs_verified_subset_verifies_from_file() {
    for &(case, upstream_case, verdict, min_obligations) in EXPECTED_CASES {
        if verdict == "verified" {
            assert_verified(case, upstream_case, min_obligations);
        }
    }
}

#[test]
fn assert_forall_by_rs_failing_subset_is_rejected_from_file() {
    for &(case, upstream_case, verdict, min_obligations) in EXPECTED_CASES {
        if verdict == "counterexample" {
            assert_counterexample(case, upstream_case, min_obligations);
        }
    }
}

/// Upstream `test_assertby1_fail3` / `test_forallstmt1_fail3`: a `tracked`
/// PROOF-mode variable CONSUMED inside a by-block is a MODE error, with Verus's
/// verbatim message. Inside `assert … by` / `assert forall … by`, Verus coerces
/// every variable read to mode `spec` (`vir/src/modes.rs` pushes
/// `in_forall_stmt` for BOTH flavours), so handing that read to a `tracked`
/// (proof-mode) parameter violates `mode_le(spec, proof)`.
#[test]
fn assert_forall_by_rs_proof_var_consumed_in_by_block_is_a_mode_error() {
    for &(case, upstream_case, verdict, _) in EXPECTED_CASES {
        if verdict != "error" {
            continue;
        }
        let err = try_extract_port_case(case)
            .expect_err(&format!("{case} ({upstream_case}) must be REJECTED"));
        assert!(
            err.contains("expression has mode spec, expected mode proof"),
            "{case} ({upstream_case}) must carry Verus's verbatim mode diagnostic, got: {err}"
        );
    }
}

/// The POSITIVE counterpart (upstream `test_forallstmt1`'s third fn): the same
/// spec-demoted proof variable used where SPEC mode is expected is FINE. If the
/// rejection above over-fired, this would break — the rule must be exactly
/// "consumed by a `tracked` parameter", not "mentioned at all".
#[test]
fn assert_forall_by_rs_proof_var_in_spec_position_is_allowed() {
    let result = verify_port_case("forallstmt_proof_var_allowed_as_spec").0;
    assert!(
        matches!(result, VerifyResult::Verified),
        "a proof-mode variable used in SPEC position inside a by-block is LEGAL Verus \
         (upstream test_forallstmt1's third fn); got {result:?}"
    );
}

/// The Verus `implies` KEYWORD lets the by-block ASSUME the antecedent — that is
/// precisely what distinguishes it from `==>`, and what upstream's warning says.
/// Without the assumption this could not discharge `0 <= x`.
#[test]
fn assert_forall_by_rs_implies_keyword_assumes_the_antecedent_in_the_block() {
    let source = r#"
        use trust_vc_types::int;

        #[trust_vc::spec]
        #[trust_vc::opaque]
        fn g1(i: int) -> int {
            i + 1
        }

        #[trust_vc::ensures(true)]
        fn implies_assumes() {
            trust_vc::assert_forall_by!(assert forall|x: int| 0int <= x implies g1(x) >= 1int by {
                trust_vc::reveal!(g1);
                trust_vc::assert!(0int <= x);
            });
        }
    "#;
    let file = parse_file_allow_tracked(source).expect("probe source should parse");
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == "implies_assumes" => Some(func),
            _ => None,
        })
        .expect("probe function should exist");
    let result = extract_verification_conditions_with_file_context(&file, func)
        .expect("probe should extract")
        .verify();
    assert!(
        matches!(result, VerifyResult::Verified),
        "the `implies` by-block must ASSUME the antecedent `0 <= x` (Verus keeps it in \
         AssertBy::require); got {result:?}"
    );
}

/// WARNING PARITY (upstream `test_forallstmt_implies`): a top-level `==>` in an
/// `assert forall` body raises Verus's warning, and the `implies` keyword does
/// NOT. Upstream's default `=> Ok(())` harness arm asserts `warnings.len() == 0`,
/// so a spurious warning on the `implies` cases would be a real divergence.
#[test]
fn assert_forall_by_rs_warning_fires_for_arrow_and_not_for_implies() {
    let arrow = extract_port_case("forallstmt_implies");
    assert_eq!(
        arrow.warnings().len(),
        1,
        "`==>` in an assert forall must raise exactly one verifier warning, got {:?}",
        arrow.warnings()
    );
    assert!(
        arrow.warnings()[0].contains(IMPLIES_ARROW_WARNING),
        "the warning must carry Verus's verbatim text, got {:?}",
        arrow.warnings()
    );

    for case in [
        "forallstmt2_test",
        "forallstmt2_test_fails1",
        "assertby_test",
        "forallstmt_test",
        "forallstmt_let",
        "scope",
    ] {
        let vc = extract_port_case(case);
        assert!(
            vc.warnings().is_empty(),
            "{case} must emit NO verifier warning (upstream's `=> Ok(())` arm asserts \
             warnings.len() == 0), got {:?}",
            vc.warnings()
        );
    }
}

// ---------------------------------------------------------------------------
// Soundness / faithfulness pins
// ---------------------------------------------------------------------------

/// Upstream `test_forallstmt1`'s inference variant: `assert forall|x| f1(x) > x`
/// with NO binder type annotation. The type is read off `f1`'s declared
/// parameter (`int`) — not guessed.
#[test]
fn assert_forall_by_rs_untyped_binder_is_inferred_from_the_spec_fn_signature() {
    let vc = extract_port_case("forallstmt_test_inference");
    let bound = vc
        .forall_bound_vars()
        .values()
        .flatten()
        .map(|decl| (decl.name.clone(), decl.ty.to_type_string()))
        .collect::<Vec<_>>();
    assert!(
        bound
            .iter()
            .any(|(name, ty)| name == "x" && ty.contains("int")),
        "the untyped binder `x` should be inferred as int from f1(i: int), got: {bound:?}"
    );
    assert!(
        matches!(vc.verify(), VerifyResult::Verified),
        "the inferred-binder form must verify"
    );
}

/// FAIL-CLOSED: a binder whose type nothing in the program forces is NOT
/// guessed. Inference only ever reads a type off a spec fn's declared parameter.
#[test]
fn assert_forall_by_rs_unconstrained_untyped_binder_still_fails_closed() {
    let source = r#"
        #[trust_vc::ensures(true)]
        fn unconstrained_binder() {
            trust_vc::assert_forall_by!(|x| x == x, {});
        }
    "#;
    let file = parse_file_allow_tracked(source).expect("probe source should parse");
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == "unconstrained_binder" => Some(func),
            _ => None,
        })
        .expect("probe function should exist");
    let err = extract_verification_conditions_with_file_context(&file, func)
        .expect_err("an unconstrained untyped binder must fail closed");
    assert!(
        err.to_string().contains("binders must be typed"),
        "expected the typed-binder diagnostic, got: {err}"
    );
}

/// CARDINAL PIN (upstream `test_scope`): an `assert forall|i: int|` binder that
/// SHADOWS an `i: u64` parameter is a fresh universally-quantified `int`, not
/// the parameter. If the alpha-rename ever aliased the two, `forall|i: int| i >= 0`
/// would VERIFY (a u64 is always >= 0) — proving MORE than Verus. It must refute.
#[test]
fn assert_forall_by_rs_shadowing_binder_is_not_aliased_to_the_parameter() {
    let source = r#"
        use trust_vc_types::int;

        #[trust_vc::ensures(true)]
        fn shadowing_binder(i: u64) {
            trust_vc::assert_forall_by!(|i: int| i >= 0int, {});
        }
    "#;
    let file = parse_file_allow_tracked(source).expect("probe source should parse");
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == "shadowing_binder" => Some(func),
            _ => None,
        })
        .expect("probe function should exist");
    let vc = extract_verification_conditions_with_file_context(&file, func)
        .expect("a binder shadowing a parameter must extract, not error");
    let result = vc.verify();
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "*** CARDINAL SOUNDNESS FAILURE *** the `|i: int|` binder was conflated with the \
         `i: u64` PARAMETER: `forall|i: int| i >= 0` was accepted, but it is FALSE over the \
         integers (i = -1). A quantifier binder must alpha-rename to a fresh symbol. \
         Got {result:?}"
    );
}

/// Upstream `test_forallstmt1_fail2`'s obligation is a GENUINE non-proof, not a
/// faithfulness gap. Outside the by-block the only fact is `forall x. f1(x) > x`,
/// and that does NOT entail `f1(3) == 4`. This pins it CONSTRUCTIVELY: `f2 = λx.
/// x + 2` satisfies the very same hypothesis, yet `f2(3) == 5 != 4`. So a model
/// of the hypothesis refuting the goal exists, upstream's `// FAILS` is correct,
/// and trust-vc's model-less fail-closed verdict is the right CLASS (it is not
/// hiding a fact trust-vc should have proved).
#[test]
fn assert_forall_by_rs_fail2_obligation_is_genuinely_unprovable() {
    let source = r#"
        use trust_vc_types::int;

        #[trust_vc::spec]
        fn f2(i: int) -> int {
            i + 2
        }

        // f2 is a MODEL of test_forallstmt1_fail2's post-block hypothesis ...
        #[trust_vc::ensures(true)]
        fn witness_satisfies_the_hypothesis() {
            trust_vc::assert!(forall(|x: int| f2(x) > x));
        }

        // ... under which the upstream goal `f1(3) == 4` is FALSE (f2(3) == 5).
        #[trust_vc::ensures(true)]
        fn witness_refutes_the_goal() {
            trust_vc::assert!(f2(3int) != 4int);
        }
    "#;
    let file = parse_file_allow_tracked(source).expect("witness source should parse");
    for case in [
        "witness_satisfies_the_hypothesis",
        "witness_refutes_the_goal",
    ] {
        let func = file
            .items
            .iter()
            .find_map(|item| match item {
                syn::Item::Fn(func) if func.sig.ident == case => Some(func),
                _ => None,
            })
            .unwrap_or_else(|| panic!("{case} should exist"));
        let result = extract_verification_conditions_with_file_context(&file, func)
            .unwrap_or_else(|err| panic!("{case} should extract: {err}"))
            .verify();
        assert!(
            matches!(result, VerifyResult::Verified),
            "{case} must verify — it is the constructive non-entailment witness for \
             test_forallstmt1_fail2. Got {result:?}"
        );
    }
}

/// Upstream `test_forallstmt_implies` warns that "using ==> in `assert forall`
/// does not currently assume the antecedent in the body". trust-vc emits no
/// warning (no warning channel), but it must have the SEMANTICS the warning
/// describes: the by-block does NOT get to assume the antecedent. If it did,
/// this would verify — and trust-vc would prove more than Verus.
#[test]
fn assert_forall_by_rs_implies_does_not_assume_the_antecedent() {
    let source = r#"
        use trust_vc_types::int;

        #[trust_vc::spec]
        #[trust_vc::opaque]
        fn p(x: int) -> bool {
            true
        }

        #[trust_vc::spec]
        #[trust_vc::opaque]
        fn q(x: int) -> bool {
            true
        }

        #[trust_vc::proof]
        fn antecedent_not_assumed() {
            trust_vc::assert_forall_by!(|x: int| p(x) ==> q(x), {
                trust_vc::assert!(p(x));
            });
        }
    "#;
    let file = parse_file_allow_tracked(source).expect("probe source should parse");
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == "antecedent_not_assumed" => Some(func),
            _ => None,
        })
        .expect("probe function should exist");
    let result = extract_verification_conditions_with_file_context(&file, func)
        .expect("probe should extract")
        .verify();
    assert!(
        is_failure_verdict(&result),
        "*** the `assert forall |x| p(x) ==> q(x) by {{ .. }}` block ASSUMED the antecedent \
         `p(x)`. Verus explicitly does NOT (that is what its warning says), so this proves \
         MORE than Verus. Got {result:?}"
    );
}

/// The `requires` hypothesis is what discharges `test_forallstmt_implies` — not
/// a leaked body from the two `#[opaque]` stand-ins for upstream's `uninterp
/// spec fn`s. Strip the hypothesis and the very same goal must be REFUTED. This
/// is what makes `#[spec] #[opaque]`-never-revealed a faithful encoding of an
/// uninterpreted predicate.
#[test]
fn assert_forall_by_rs_implies_hypothesis_is_load_bearing() {
    let source = r#"
        use trust_vc_types::int;

        #[trust_vc::spec]
        #[trust_vc::opaque]
        fn p(x: int) -> bool {
            true
        }

        #[trust_vc::spec]
        #[trust_vc::opaque]
        fn q(x: int) -> bool {
            true
        }

        #[trust_vc::proof]
        fn no_hypothesis() {
            trust_vc::assert_forall_by!(|x: int| p(x) ==> q(x), {});
        }
    "#;
    let file = parse_file_allow_tracked(source).expect("probe source should parse");
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == "no_hypothesis" => Some(func),
            _ => None,
        })
        .expect("probe function should exist");
    let result = extract_verification_conditions_with_file_context(&file, func)
        .expect("probe should extract")
        .verify();
    assert!(
        is_failure_verdict(&result),
        "without the `requires`, `forall|x| p(x) ==> q(x)` must NOT be provable — if it is, \
         an opaque body leaked and the `uninterp` stand-in is unfaithful. Got {result:?}"
    );
}
