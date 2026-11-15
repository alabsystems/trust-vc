// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for the first partial upstream adts_generics.rs TrustVc slice.
//!
//! These tests intentionally keep `source/rust_verify_test/tests/adts_generics.rs`
//! fail-closed in the manifest. They prove only local Rust-valid witnesses for
//! generic struct field projection/refinement and generic enum construction
//! while broader Verus-only generic ADT syntax remains unsupported.

use std::{
    collections::{BTreeMap, BTreeSet},
    path::PathBuf,
};
use trust_vc_core::{extract_verification_conditions_with_file_context, VerifyResult};

fn adts_generics_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../evals/verus/ported/adts_generics.rs")
}

fn verus_manifest_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

fn port_function(case: &str) -> syn::ItemFn {
    let path = adts_generics_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("adts_generics port should read: {err}"));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("adts_generics port should parse: {err}"));

    file.items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(function) if function.sig.ident == case => Some(function.clone()),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} should exist in adts_generics port"))
}

fn verify_port_case(case: &str) -> (VerifyResult, usize) {
    let path = adts_generics_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("adts_generics port should read: {err}"));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("adts_generics port should parse: {err}"));
    let function = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(function) if function.sig.ident == case => Some(function),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} should exist in adts_generics port"));

    let vc = extract_verification_conditions_with_file_context(&file, function)
        .unwrap_or_else(|err| panic!("{case} should extract: {err}"));
    let obligation_count = vc.obligations().len();
    (vc.verify(), obligation_count)
}

// Retained for future fail-closed error-message cases; no case currently errors.
#[allow(dead_code)]
fn error_message_for_case(case: &str) -> String {
    let path = adts_generics_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("adts_generics port should read: {err}"));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("adts_generics port should parse: {err}"));
    let function = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(function) if function.sig.ident == case => Some(function),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} should exist in adts_generics port"));

    match extract_verification_conditions_with_file_context(&file, function) {
        Err(err) => err.to_string(),
        Ok(vc) => match vc.verify() {
            VerifyResult::Error { message } => message,
            other => panic!("{case} should fail with Error, got: {other:?}"),
        },
    }
}

fn assert_verified(case: &str, upstream_case: &str, min_obligations: usize) {
    let (result, obligation_count) = verify_port_case(case);
    assert!(
        obligation_count >= min_obligations,
        "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligation_count}"
    );
    assert!(
        matches!(result, VerifyResult::Verified),
        "{case} ({upstream_case}) should verify, got: {result:?}"
    );
}

const EXPECTED_CASES: &[(&str, &str, &str, usize)] = &[
    (
        "generic_struct_projection_preserves_equal_payloads",
        "test_generic_adt_eq",
        "verified",
        2,
    ),
    (
        "generic_struct_u8_field_nonnegative",
        "test_box_unbox_struct",
        "verified",
        2,
    ),
    (
        "generic_spec_identity_preserves_projected_field",
        "test_refinements1",
        "verified",
        3,
    ),
    (
        "generic_enum_constructor_smoke",
        "test_box_enum",
        "verified",
        2,
    ),
    (
        "generic_enum_match_extracts_payload_verified",
        "test_box_enum",
        "verified",
        2,
    ),
    (
        "generic_struct_projection_wrong_value_compute_counterexample",
        "test_generic_adt_eq",
        "counterexample",
        2,
    ),
    (
        "generic_tuple_struct_destructure_currently_error",
        "test_erase1",
        "verified",
        3,
    ),
    (
        "test_generic_adt_eq_counterexample",
        "test_generic_adt_eq",
        "counterexample",
        3,
    ),
    (
        "test_generic_adt_u8_counterexample",
        "test_generic_adt_u8",
        "counterexample",
        2,
    ),
];

// The tuple-struct destructure gap has closed (monomorphized tuple-field
// selector support); no case fails closed on an error message any more.
const ERROR_CASES: &[(&str, &[&str])] = &[];

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
        .unwrap_or_else(|| panic!("adts_generics port should define {const_name}"));

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
    let array = referenced_array_const(file, "ADTS_GENERICS_RS_FAIL_CLOSED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "ADTS_GENERICS_RS_EXPECTED_CASES");
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
            "duplicate adts_generics metadata for {case_id}"
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

fn expected_metadata() -> Vec<CaseMetadata> {
    let mut error_patterns = BTreeMap::new();
    for (case, expected_fragments) in ERROR_CASES {
        assert!(
            error_patterns
                .insert(
                    *case,
                    expected_fragments
                        .iter()
                        .map(|fragment| (*fragment).to_string())
                        .collect::<Vec<_>>(),
                )
                .is_none(),
            "duplicate error-case metadata for {case}"
        );
    }

    EXPECTED_CASES
        .iter()
        .map(
            |(case_id, upstream_case_id, expected_verdict, min_obligations)| CaseMetadata {
                case_id: (*case_id).to_string(),
                upstream_case_id: (*upstream_case_id).to_string(),
                expected_verdict: (*expected_verdict).to_string(),
                min_obligations: *min_obligations,
                expected_error_patterns: error_patterns.remove(case_id).unwrap_or_default(),
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
                == Some("source/rust_verify_test/tests/adts_generics.rs")
        })
        .expect("Verus manifest should contain adts_generics.rs row");

    row["expected_cases"]
        .as_array()
        .expect("adts_generics.rs row should contain expected_cases")
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

#[test]
fn adts_generics_rs_expected_case_metadata_is_exact() {
    let path = adts_generics_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("adts_generics port should read: {err}"));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("adts_generics port should parse: {err}"));
    assert_eq!(metadata_entries(&file), expected_metadata());
    assert!(
        source.contains("adts_generics_rs_expected_cases")
            && source.contains("adts_generics_rs_fail_closed_error_patterns"),
        "adts_generics port should export expected-case and error-pattern metadata"
    );
}

#[test]
fn adts_generics_rs_expected_case_metadata_matches_manifest() {
    let path = adts_generics_port_path();
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|err| panic!("adts_generics port should read: {err}"));
    let file = syn::parse_file(&source)
        .unwrap_or_else(|err| panic!("adts_generics port should parse: {err}"));
    assert_eq!(metadata_entries(&file), manifest_expected_metadata());
}

#[test]
fn adts_generics_rs_verified_subset_verifies_from_file() {
    for (case, upstream_case, min_obligations) in [
        (
            "generic_struct_projection_preserves_equal_payloads",
            "test_generic_adt_eq verified equality prefix",
            2,
        ),
        (
            "generic_struct_u8_field_nonnegative",
            "test_box_unbox_struct Thing<u8> field refinement",
            2,
        ),
        (
            "generic_spec_identity_preserves_projected_field",
            "test_refinements1/test_refinements2 generic id over projected fields",
            4,
        ),
        (
            "generic_enum_constructor_smoke",
            "test_box_enum generic enum construction",
            2,
        ),
        (
            "generic_named_struct_field_projection_verified",
            "test_erase2 direct named-field projection",
            3,
        ),
        (
            "generic_named_struct_numeric_field_projection_verified",
            "test_refinements2/test_erase2 direct numeric named-field projection",
            3,
        ),
        (
            "out_of_order_nested_struct_construction_smoke",
            "test_out_of_order nested struct construction",
            2,
        ),
        (
            // SOUND-IMPROVEMENT pin update 2->1 (audited 2026-07-03, VC cache
            // disabled; flip bisected to trust-vc 54510d7 "MATCH + SPEC-FN-CALL
            // + Result/Option lowering", 2026-06-27): a match-returning body's
            // canonical return value is now INLINED into the postcondition and
            // the separate `return_value` obligation (an ASSUME
            // `result == match ...`, not a proof goal) is dropped. Before:
            // {postcondition: `result`, return_value(assume): `result == match ...`};
            // after: {postcondition: `match Choice::<u64>::First(11u64) { ... }`}.
            // Same single proof goal, nothing semantically lost, and the goal
            // stays load-bearing: mutating the arm to `payload == 12u64` yields
            // Counterexample (result = false), never Verified.
            "generic_enum_match_extracts_payload_verified",
            "test_box_enum generic enum payload match",
            1,
        ),
    ] {
        assert_verified(case, upstream_case, min_obligations);
    }
}

#[test]
fn adts_generics_rs_false_generic_struct_case_is_rejected_from_file() {
    // Re-pinned 2026-09-13: these refutations used to be accepted as either
    // Counterexample or a fail-closed Unknown; the engine now refutes every one
    // with a model (the u8 lower bound with `a = 0`, the inequality as a
    // hypothesis-robust reflexive disequality), so only Counterexample is the
    // honest verdict. The two `test_generic_adt_*_counterexample` rows are the
    // upstream cases verbatim (`one` with both asserts, `two`).
    for (case, upstream_case, min_obligations) in [
        (
            "generic_struct_projection_wrong_inequality_counterexample",
            "test_generic_adt_eq false inequality",
            2,
        ),
        (
            "generic_struct_u8_field_at_least_one_counterexample",
            "test_generic_adt_u8 false lower bound",
            2,
        ),
        (
            "test_generic_adt_eq_counterexample",
            "test_generic_adt_eq",
            3,
        ),
        (
            "test_generic_adt_u8_counterexample",
            "test_generic_adt_u8",
            2,
        ),
    ] {
        let (result, obligation_count) = verify_port_case(case);
        assert!(
            obligation_count >= min_obligations,
            "{case} ({upstream_case}) should collect at least {min_obligations} obligation(s), got {obligation_count}"
        );
        assert!(
            matches!(result, VerifyResult::Counterexample { .. }),
            "{case} ({upstream_case}) should be refuted with a model, got: {result:?}"
        );
    }
}

#[test]
fn adts_generics_rs_generic_struct_compute_false_case_is_rejected_from_file() {
    let case = "generic_struct_projection_wrong_value_compute_counterexample";
    let (result, obligation_count) = verify_port_case(case);
    assert!(
        obligation_count >= 2,
        "{case} (test_generic_adt_eq false projection, compute-supported slice) should collect at least two obligations, got {obligation_count}"
    );
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "{case} (test_generic_adt_eq false projection, compute-supported slice) should produce a counterexample, got: {result:?}"
    );
}

#[test]
fn adts_generics_rs_generic_enum_helpers_counterexample_from_file() {
    // SOUND-IMPROVEMENT pin update (native-`Sort::Datatype` migration, 0737e64):
    // the body asserts `value.is_First()` on a *symbolic* `Choice<u64>`, which
    // may be the `Empty` variant — so the assertion does NOT hold and the
    // CORRECT answer is a counterexample (`value = Choice_u64_Empty`). The native
    // datatype theory now reasons about symbolic datatype values exhaustively, so
    // this no longer degrades to a fail-closed Unknown but is soundly refuted.
    let case = "generic_enum_variant_helpers_currently_error";
    let (result, _) = verify_port_case(case);
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "{case} should counterexample (symbolic Choice may be Empty), got: {result:?}"
    );
}

#[test]
fn adts_generics_rs_generic_identity_struct_field_from_file() {
    // SOUND-IMPROVEMENT pin update (#2778 generic fn-call return-type
    // monomorphization). The lowering now monomorphizes a generic fn's
    // `TypeParam` return into the concrete carrier inferred from the argument
    // types + turbofish, and the encoder bridges the type-erased `Poly` call
    // result back through `Unbox_T` — so a following field projection
    // (`projected.a`) resolves instead of failing closed with
    // `field 'a' on type 'A'`. The three cases below upgrade from a (honest, but
    // unhelpful) hard Error to their genuine, sound verdicts:
    //
    //  * EXEC identity (`#[ensures(result == value)]`): the ensures clause is a
    //    ground fact connecting the projection to the argument, so
    //    `projected.a == 9` / `projected.b == 2` VERIFY (real, sound gain).
    //
    //  * TRANSPARENT-SPEC identity on a TRUE goal: VERIFIED — SOUND-IMPROVEMENT
    //    pin update (audited 2026-07-03, VC cache disabled). The flip is
    //    ay-side, bisected to the single ay commit 8deace993b ("ay-dpll:
    //    datatype-value equality congruence axiom", entered via the 3a23c63 pin
    //    bump f587be09 -> 25356919f9; no trust-vc engine source changed in the
    //    flip window). Mechanism: the instantiated body axiom yields a BARE
    //    datatype-value equality (`generic_id@inst == boxed Pair{9,2}`, neither
    //    side a constructor application); the eager DT reduction previously
    //    emitted NO congruence axiom for it, so field equality never propagated
    //    (spurious SAT, fail-closed here to the empty-model Unknown). ay now
    //    emits the datatype-equality biconditional (injectivity/field
    //    congruence — a true fact of datatype semantics), so `projected.a == 9`
    //    / `projected.b == 2` are UNSAT-proved. Non-degeneracy verified at the
    //    flip rev AND at the current pin: the FALSE goals (`projected.a == 10`,
    //    `projected.b == 3`) still return honest Unknown (solver SAT with no
    //    concrete witness -> degraded), which also proves the assumption set is
    //    satisfiable on its own (a contradictory/vacuous context would have
    //    proved the false goals too).
    //
    //  * TRANSPARENT-SPEC identity on a FALSE goal (`projected.a == 10`): fails
    //    closed — Unknown (under-constrained model) or Counterexample. Never a
    //    false Verified.
    let (exec_result, exec_obligations) =
        verify_port_case("generic_exec_identity_struct_field_currently_error");
    assert!(
        exec_obligations >= 2,
        "generic_exec_identity_struct_field should collect at least two obligations, got {exec_obligations}"
    );
    assert!(
        matches!(exec_result, VerifyResult::Verified),
        "generic_exec_identity_struct_field (exec `#[ensures(result == value)]` identity) should \
         verify the lifted field projections, got: {exec_result:?}"
    );

    let (spec_true_result, _) =
        verify_port_case("generic_spec_identity_struct_field_currently_error");
    assert!(
        matches!(spec_true_result, VerifyResult::Verified),
        "generic_spec_identity_struct_field (transparent-spec identity, TRUE goal) should verify \
         via the ay datatype-value-equality congruence axiom (8deace993b), got: {spec_true_result:?}"
    );

    let (spec_false_result, _) =
        verify_port_case("generic_spec_identity_wrong_struct_field_currently_rejected");
    assert!(
        matches!(
            spec_false_result,
            VerifyResult::Unknown { .. } | VerifyResult::Counterexample { .. }
        ),
        "generic_spec_identity_wrong_struct_field (transparent-spec identity, FALSE goal) should \
         fail closed (Unknown or Counterexample), never Verified, got: {spec_false_result:?}"
    );
}

#[test]
fn adts_generics_rs_generic_tuple_struct_destructure_verifies_from_file() {
    // SOUND-IMPROVEMENT pin update (audited 2026-07-07, VC cache disabled): the
    // generic tuple-struct destructure gap has closed (monomorphized tuple-field
    // selector support). `let TupleThing(first, second) = value;` now binds each
    // pattern variable to the constructor's positional field, so for
    // `TupleThing::<bool, bool>(true, false)` the collected obligations are
    // `first` (== true) and `!second` (== !false), both TRUE — Verified is the
    // CORRECT verdict (previously an over-rejecting "unresolved variable `first`"
    // Error). Non-degeneracy verified firsthand on crafted witnesses: asserting
    // the false field claim (`second`) or the negated true one (`!first`) each
    // yields a Counterexample; a swapped/order-mismatched symbolic claim
    // (`first == y` for `TupleThing(x, y)`) refutes with model `x = false,
    // y = true`; and the symbolic `first == x && second == y` verifies — the
    // binding tracks constructor positions and refutes false claims, so this is
    // not a vacuous verify.
    let (result, obligation_count) =
        verify_port_case("generic_tuple_struct_destructure_currently_error");
    assert!(
        obligation_count >= 3,
        "generic_tuple_struct_destructure should collect at least three obligations, got {obligation_count}"
    );
    assert!(
        matches!(result, VerifyResult::Verified),
        "generic_tuple_struct_destructure (true field claims through a tuple-struct \
         let-local destructure) should verify, got: {result:?}"
    );
}

#[test]
fn adts_generics_rs_generic_named_struct_destructure_verifies_from_file() {
    // SOUND-IMPROVEMENT pin update (audited 2026-07-03, VC cache disabled; flip
    // bisected to trust-vc c3f1b4e "named + tuple struct destructure of a
    // let-local", 2026-06-24 — that commit's own message declared this exact
    // pin flip for owner-side reclassification). `let Pair { a: first, b: second }
    // = value;` now resolves the destructure base from the let-local's inferred
    // scoped struct type and binds each pattern variable to a FIELD PROJECTION
    // of the local's own value — the collected obligations are
    // `(Pair::<bool,bool>{a:true,b:false}).a` and `!(...).b`, both TRUE, so
    // Verified is the CORRECT verdict (previously an over-rejecting
    // "unresolved variable `first`" Error). Non-degeneracy verified firsthand:
    // flipping either claim (`!first` / `second`) OR swapping the destructure
    // bindings (`a: second, b: first`) each yields a Counterexample, never
    // Verified; trust-vc-core's vc_extraction/tests/generic_adt_destructure.rs
    // pins both directions including a symbolic binds-the-field-value witness.
    // The generic TUPLE-struct destructure stays fail-closed (separate
    // monomorphized-selector gap) — see
    // adts_generics_rs_generic_tuple_struct_destructure_errors_from_file.
    let (result, obligation_count) =
        verify_port_case("generic_named_struct_destructure_currently_error");
    assert!(
        obligation_count >= 3,
        "generic_named_struct_destructure should collect at least three obligations, got {obligation_count}"
    );
    assert!(
        matches!(result, VerifyResult::Verified),
        "generic_named_struct_destructure (true field claims through a let-local destructure) \
         should verify, got: {result:?}"
    );
}

#[test]
fn adts_generics_rs_out_of_order_tuple_projection_verifies_from_file() {
    // SOUND-IMPROVEMENT pin update (native-`Sort::Datatype` migration, 0737e64):
    // the body builds `tz.p = (3, 4)` and asserts `tz.p.0 == 3` and `tz.p.1 == 4`
    // — both TRUE — so `Verified` is the CORRECT answer; the nested-tuple
    // projection gap that previously fail-closed here has been closed by the
    // native datatype theory. (The case predates this fix: it verified even at
    // the migration parent.) `adts_generics.rs` stays an unsupported-gap port.
    let (result, _) = verify_port_case("out_of_order_nested_tuple_projection_currently_error");
    assert!(
        matches!(result, VerifyResult::Verified),
        "out_of_order_nested_tuple_projection should now verify (true projections), got: {result:?}"
    );
}

#[test]
fn adts_generics_rs_generic_tuple_struct_field_projection_verifies_from_file() {
    // SOUND-IMPROVEMENT pin update (nullary-variant tester-postcondition fix,
    // this change): the body builds `TupleThing::<bool, bool>(true, false)` and
    // asserts `value.0` and `!value.1` — both TRUE — so `Verified` is the CORRECT
    // answer. The concrete-compute recovery added to discharge the unit-variant
    // tester regression also resolves this tuple-struct field projection by
    // substituting the constructor binding and evaluating the field accesses on
    // the concrete value. A wrong projection (e.g. `assert!(value.1)`) still fails
    // closed. `adts_generics.rs` stays an unsupported-gap port.
    let (result, _) = verify_port_case("generic_tuple_struct_field_projection_currently_unknown");
    assert!(
        matches!(result, VerifyResult::Verified),
        "generic_tuple_struct_field_projection should now verify (true projections), got: {result:?}"
    );
}

#[test]
fn adts_generics_rs_port_inventory_stays_intentional() {
    for case in [
        "generic_struct_projection_preserves_equal_payloads",
        "generic_struct_projection_wrong_inequality_counterexample",
        "generic_struct_u8_field_nonnegative",
        "generic_struct_u8_field_at_least_one_counterexample",
        "generic_spec_identity_preserves_projected_field",
        "generic_exec_identity_struct_field_currently_error",
        "generic_spec_identity_struct_field_currently_error",
        "generic_spec_identity_wrong_struct_field_currently_rejected",
        "generic_struct_projection_wrong_value_compute_counterexample",
        "generic_enum_constructor_smoke",
        "generic_tuple_struct_field_projection_currently_unknown",
        "generic_named_struct_field_projection_verified",
        "generic_named_struct_numeric_field_projection_verified",
        "generic_named_struct_destructure_currently_error",
        "out_of_order_nested_struct_construction_smoke",
        "out_of_order_nested_tuple_projection_currently_error",
        "generic_enum_match_extracts_payload_verified",
        "generic_enum_variant_helpers_currently_error",
        "generic_tuple_struct_destructure_currently_error",
        "test_generic_adt_eq_counterexample",
        "test_generic_adt_u8_counterexample",
    ] {
        let function = port_function(case);
        assert_eq!(
            function.sig.ident, case,
            "{case} should remain an explicit top-level port witness"
        );
    }
}
