// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guard for the currently ported upstream bitvector.rs subset.
//!
//! This is intentionally narrower than full replacement evidence: the upstream
//! file still contains Verus-only proof syntax, diagnostics, arch-width options,
//! quantifiers, function-mode bit-vector attributes, and mixed-width stress
//! cases that are not ported here.

use std::{
    collections::{BTreeMap, BTreeSet},
    path::PathBuf,
};
use trust_vc_core::{
    vc::{ProofObligation, SolverMode, VerificationContext},
    verify_function_from_file, VerifyResult,
};

fn bitvector_port_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/ported/bitvector.rs")
}

fn verus_manifest_path() -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../evals/verus/verus-tests.json")
}

const VERIFIED_CASES: &[(&str, &str)] = &[
    ("mask_and_basic_identities", "test1"),
    ("shift_left_times_four", "test2"),
    ("bounded_shift_left_matches_math_product", "test2"),
    ("shift_right_divide_by_two", "test2"),
    ("reflexive_and_compound_bitwise", "test3"),
    ("verus_wrapping_free_function_identities", "test3"),
    ("pack_u32_pair", "test4"),
    ("unpack_u64_upper_word", "test5"),
    ("xor_cancellation", "test6"),
    ("not_identities", "test7"),
    ("commuted_mask_bound", "test8"),
    ("quantified_bitwise_and_commutativity_u32", "test8"),
    ("unsigned_max_tautologies", "test9"),
    ("signed_reflexive_le", "test8_ok"),
    ("usize_in_by_bit_vector", "usize_in_by_bit_vector"),
    (
        "const_usize_in_by_bit_vector",
        "const_usize_in_by_bit_vector",
    ),
    ("usize_cast_in_by_bit_vector", "usize_cast_in_by_bit_vector"),
    (
        "const_math_int_in_by_bit_vector",
        "const_int_in_by_bit_vector",
    ),
    (
        "finite_width_cast_to_larger_word",
        "test_casting_to_higher_width_issue386",
    ),
    (
        "bool_guarded_bitwise_identity",
        "test_bool_variable_issue369",
    ),
    ("shift_right_upper_bound_issue415", "test_issue415"),
    (
        "positive_shift_right_decreases",
        "bitvector_in_decreases_by",
    ),
    ("signed_euclidean_div_constants", "div_signed_euclidean"),
    ("signed_euclidean_rem_constants", "mod_signed_euclidean"),
    (
        "signed_cast_to_math_int_div_neg_one_i8",
        "div_mod_signed_properties",
    ),
    (
        "signed_min_div_neg_one_math_int_i8",
        "div_mod_signed_properties",
    ),
    ("signed_min_div_neg_one_math_int_i16", "div_signed_overflow"),
    (
        "signed_euclidean_div_rem_constants_i16",
        "div_signed_euclidean/mod_signed_euclidean",
    ),
    ("unsigned_division_nonzero_guards", "div0_underspecified"),
    ("unsigned_remainder_nonzero_guards", "mod0_underspecified"),
    (
        "unsigned_div_rem_identity_u8",
        "div_mod_unsigned_properties",
    ),
    (
        "unsigned_div_rem_unit_divisor_u16",
        "div_mod_unsigned_properties",
    ),
    ("unsigned_remainder_bound_u8", "div_mod_unsigned_properties"),
    ("unsigned_div_rem_constants_u16", "div0/mod0 arithmetic"),
    (
        "concrete_signed_extreme_arithmetic_4_4_subset",
        "test_extreme_cases_arithmetic1",
    ),
    (
        "concrete_signed_extreme_arithmetic_8_8_subset",
        "test_extreme_cases_arithmetic2",
    ),
    (
        "concrete_signed_extreme_arithmetic_8_16_subset",
        "test_extreme_cases_arithmetic3",
    ),
    (
        "concrete_signed_extreme_arithmetic_15_16_subset",
        "test_extreme_cases_arithmetic5",
    ),
    ("concrete_by_equating_add_subset", "test_by_equating_add"),
    ("concrete_by_equating_sub_subset", "test_by_equating_sub"),
    ("concrete_by_equating_mul_subset", "test_by_equating_mul"),
    ("concrete_by_equating_le_subset", "test_by_equating_le"),
    (
        "concrete_unsigned_by_equating_shr_subset",
        "test_by_equating_shr",
    ),
    ("concrete_by_equating_shl_subset", "test_by_equating_shl"),
    (
        "signed_unsigned_div_rem_concrete_subset",
        "test_signed_and_unsigned",
    ),
    ("bitnot_u64_subtraction_identity", "bitnot"),
    ("signed_bitnot_i64_subtraction_identity", "bitnot"),
    ("signed_bitnot_i32_constant", "bitnot"),
    (
        "clipping_and_casting_valid_subset",
        "test_clipping_and_casting",
    ),
    (
        "cross_width_unsigned_ineq_valid_subset",
        "bitvector_ineq_different_bitwidth",
    ),
    ("mixed_signed_unsigned_ineq_valid_subset", "test_eq_ineq"),
    (
        "mixed_signed_unsigned_reflexive_cast_valid_subset",
        "test_eq_ineq",
    ),
    ("mixed_u32_i32_comparison_valid_subset", "test_eq_ineq2"),
    ("cross_width_bitnot_valid_subset", "bitnot"),
    (
        "mixed_width_or_and_xor_valid_subset",
        "test_or/test_and/test_xor",
    ),
    ("u16_bitwise_zero_extend_valid_subset", "test_normal_solver"),
    ("mixed_width_shift_valid_subset", "test_shl/test_shr"),
    ("u16_shift_right_cast_valid_subset", "test_shr"),
    ("u32_shift_right_matches_low_u16_when_bounded", "test_shr"),
    ("signed_shift_left_valid_subset", "test_shl_signed"),
    ("signed_shift_right_valid_subset", "test_shr_signed"),
    (
        "signed_i16_shift_right_sign_extend_valid_subset",
        "test_shr_signed",
    ),
    ("let_bound_shift_valid_subset", "test_let_binder"),
    ("forall_shift_right_equal_width_subset", "test_forall"),
    (
        "mixed_width_shift_keeps_lhs_width_valid_subset",
        "test_shl/test_shr",
    ),
    (
        "function_level_bit_vector_attribute_valid_subset",
        "#[verifier(bit_vector)]",
    ),
    (
        "recursive_bitvector_spec_compute_verified",
        "recursive spec-function bitvector compute boundary",
    ),
    ("bitvector_function_shaped_helpers", "test_functions"),
    // Class-A flips (stale fail-closed pins -> Verified), audited per the
    // sweep-backlog control ledger before re-pinning. All three claims are
    // mathematically true sign-cast monotonicity/bitnot identities; the old
    // "sort metadata mismatch" fail-closed pins predate 121fced (same-width
    // signedness as-cast lowering). False-mutation controls (2026-07-03, run
    // against a mutated copy, TRUST_VC_DISABLE_VC_CACHE=1):
    // - mixed_signed_unsigned_cast_guard_diagnostic [conclusion >= tightened
    //   to >]: Counterexample x = 127, y = 127 (also in the step-2 ledger).
    // - mixed_u32_i32_reverse_guard_diagnostic [hypothesis > loosened to >=]:
    //   Counterexample a = 2147483647, b = 2147483647.
    // - signed_unsigned_bitnot_cast_guard_diagnostic [(-1i32 - b) ->
    //   (-2i32 - b)]: Counterexample a = 1073741823, b = 1073741823.
    // NOTE: the port-file metadata tables and the manifest row still pin these
    // as error/"sort metadata mismatch" — syncing them requires editing
    // evals/verus/verus-tests.json, which the sweep-backlog plan must not
    // touch; deferred to a manifest-touching step.
    (
        "mixed_signed_unsigned_cast_guard_diagnostic",
        "test_eq_ineq",
    ),
    ("mixed_u32_i32_reverse_guard_diagnostic", "test_eq_ineq2"),
    ("signed_unsigned_bitnot_cast_guard_diagnostic", "bitnot"),
    // Masked sibling exposed by the flips above: TRUE under Verus's value
    // semantics for &mut in spec position (*x == *y ==> x == y); upstream's
    // Err is a by(bit_vector) capability rejection, not a falsity claim.
    // False-mutation control (2026-07-03, mutated copy): [x == y -> x != y]
    // => Counterexample x = 18446744073709551615, y = 18446744073709551615,
    // confirming consistent value semantics. Attributed to the mut-ref
    // substrate wiring (ead157a/c695266 lineage). Manifest still pins
    // error/"dereference" — sync deferred as above.
    (
        "bitvector_mut_ref_deref_diagnostic",
        "test_dereference_mut_ref_2",
    ),
];

const COUNTEREXAMPLE_CASES: &[(&str, &str)] = &[
    (
        "finite_width_cast_to_larger_word_counterexample",
        "test_casting_to_higher_width_issue386",
    ),
    ("b_or_b_greater_counterexample", "test1_fails"),
    ("b_and_zero_positive_counterexample", "test3_fails"),
    ("wrapping_increment_identity_counterexample", "test2_fails"),
    ("shift_roundtrip_counterexample", "test4_fails"),
    ("shift_left_wrong_multiplier_counterexample", "test5_fails"),
    ("bitnot_constants_then_false_counterexample", "test7_fails"),
    (
        "clipping_cast_u32_to_u16_counterexample",
        "test_clipping_and_casting",
    ),
    (
        "clipping_cast_i32_to_i16_counterexample",
        "test_clipping_and_casting",
    ),
    (
        "cross_width_unsigned_ineq_counterexample",
        "bitvector_ineq_different_bitwidth",
    ),
    ("mixed_signed_unsigned_eq_counterexample", "test_eq_ineq"),
    ("mixed_signed_unsigned_ineq_counterexample", "test_eq_ineq"),
    ("mixed_u32_i32_comparison_counterexample", "test_eq_ineq2"),
    ("cross_width_bitnot_counterexample", "bitnot"),
    (
        "mixed_width_or_and_xor_counterexample",
        "test_or/test_and/test_xor",
    ),
    (
        "i16_bitwise_unsigned_cast_counterexample",
        "test_normal_solver",
    ),
    ("mixed_width_shift_counterexample", "test_shl"),
    (
        "mixed_width_shift_lhs_width_counterexample",
        "test_shl/test_shr",
    ),
    ("u16_shift_right_low_byte_counterexample", "test_shr"),
    ("u32_shift_right_low_u16_counterexample", "test_shr"),
    ("signed_shift_left_width_counterexample", "test_shl_signed"),
    (
        "signed_i16_shift_right_zero_extend_counterexample",
        "test_shr_signed",
    ),
    (
        "positive_shift_right_decreases_counterexample",
        "bitvector_in_decreases_by",
    ),
    (
        "casting_u16_to_u8_counterexample",
        "test_clipping_and_casting",
    ),
    (
        "casting_i16_to_i8_counterexample",
        "test_clipping_and_casting",
    ),
    ("verus_wrapping_free_function_counterexample", "test1_fails"),
    (
        "quantified_shift_positive_counterexample_u64",
        "test10_fails",
    ),
    (
        "unsigned_div_rem_identity_counterexample_u8",
        "div_mod_unsigned_properties",
    ),
    (
        "unsigned_div_rem_unit_divisor_counterexample_u16",
        "div_mod_unsigned_properties",
    ),
    (
        "unsigned_division_zero_guard_missing_counterexample",
        "div0_underspecified",
    ),
    (
        "concrete_signed_extreme_arithmetic_counterexample",
        "test_extreme_cases_arithmetic2",
    ),
    (
        "concrete_by_equating_arithmetic_counterexample",
        "test_by_equating_mul",
    ),
    (
        "signed_unsigned_div_rem_concrete_counterexample",
        "test_signed_and_unsigned",
    ),
    (
        "function_level_bit_vector_attribute_counterexample",
        "#[verifier(bit_vector)]",
    ),
    (
        "recursive_bitvector_spec_compute_counterexample",
        "recursive spec-function bitvector compute boundary",
    ),
];

const FAIL_CLOSED_ERROR_CASES: &[(&str, &str, &[&str])] = &[
    // Upstream rejects a possibly-negative shift amount with a VIR error, and
    // since 4653198/b2bd315 the engine emits the byte-exact upstream fragment
    // instead of a counterexample (class-C diagnostic re-pin; both verdicts are
    // non-Verified so no soundness control is needed). NOTE: the port-file
    // metadata tables and the manifest row still pin these two cases as
    // `counterexample` — syncing them requires editing
    // evals/verus/verus-tests.json, which the sweep-backlog plan must not
    // touch; deferred to a manifest-touching step.
    (
        "signed_shift_amount_left_diagnostic",
        "test_shl_signed_unsupported",
        &["not supported: bit-shift with possibly negative shift"],
    ),
    (
        "signed_shift_amount_right_diagnostic",
        "test_shr_signed_unsupported",
        &["not supported: bit-shift with possibly negative shift"],
    ),
    (
        "bitvector_old_mut_ref_diagnostic",
        "test_old_not_supported",
        &["old"],
    ),
    (
        "bitvector_decreases_by_clause_currently_fail_closed",
        "bitvector_in_decreases_by / decreases_by boundary",
        &["decreases_by"],
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
        .unwrap_or_else(|| panic!("bitvector port should define {const_name}"));

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
    let array = referenced_array_const(file, "BITVECTOR_RS_FAIL_CLOSED_ERROR_PATTERNS");
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
    let array = referenced_array_const(file, "BITVECTOR_RS_EXPECTED_CASES");
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
            "duplicate bitvector metadata for {case_id}"
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

fn manifest_metadata() -> Vec<CaseMetadata> {
    let source =
        std::fs::read_to_string(verus_manifest_path()).expect("Verus manifest should be readable");
    let manifest: serde_json::Value =
        serde_json::from_str(&source).expect("Verus manifest should parse as JSON");
    let entries = manifest["entries"]
        .as_array()
        .expect("Verus manifest should contain entries");
    let row = entries
        .iter()
        .find(|entry| {
            entry["upstream_path"].as_str() == Some("source/rust_verify_test/tests/bitvector.rs")
        })
        .expect("Verus manifest should contain bitvector.rs row");

    row["expected_cases"]
        .as_array()
        .expect("bitvector.rs row should contain expected_cases")
        .iter()
        .map(|case| CaseMetadata {
            case_id: case["case_id"]
                .as_str()
                .expect("case should contain case_id")
                .to_string(),
            upstream_case_id: case["upstream_case_id"]
                .as_str()
                .expect("case should contain upstream_case_id")
                .to_string(),
            expected_verdict: case["expected_verdict"]
                .as_str()
                .expect("case should contain expected_verdict")
                .to_string(),
            min_obligations: case["min_obligations"]
                .as_u64()
                .expect("case should contain min_obligations")
                .try_into()
                .expect("min_obligations should fit usize"),
            expected_error_patterns: case["expected_error_patterns"]
                .as_array()
                .map(|patterns| {
                    patterns
                        .iter()
                        .map(|pattern| {
                            pattern
                                .as_str()
                                .expect("error pattern should be a string")
                                .to_string()
                        })
                        .collect()
                })
                .unwrap_or_default(),
        })
        .collect()
}

#[test]
fn bitvector_rs_expected_case_metadata_matches_manifest() {
    let source =
        std::fs::read_to_string(bitvector_port_path()).expect("bitvector port should be readable");
    let file = syn::parse_file(&source)
        .expect("bitvector port metadata should parse as ordinary Rust syntax");
    assert_eq!(metadata_entries(&file), manifest_metadata());
    assert!(
        source.contains("bitvector_rs_expected_cases"),
        "bitvector port should export expected-case metadata"
    );
    assert!(
        source.contains("bitvector_rs_fail_closed_error_patterns"),
        "bitvector port should export fail-closed error-pattern metadata"
    );
}

#[test]
fn bitvector_rs_verified_subset_verifies_from_file() {
    let path = bitvector_port_path();
    let path = path.to_str().expect("port path should be UTF-8");
    let mut failures = Vec::new();

    for (case, upstream_case) in VERIFIED_CASES {
        match verify_function_from_file(path, case) {
            Ok(VerifyResult::Verified) => {}
            Ok(result) => {
                failures.push(format!(
                    "{case} ({upstream_case}) should verify, got: {result:?}"
                ));
            }
            Err(err) => {
                failures.push(format!("{case} ({upstream_case}) should extract: {err}"));
            }
        }
    }

    assert!(
        failures.is_empty(),
        "verified bitvector cases failed:\n{}",
        failures.join("\n")
    );
}

fn assert_all_counterexamples(path: &str, cases: &[(&str, &str)]) {
    let mut failures = Vec::new();

    for (case, upstream_case) in cases {
        match verify_function_from_file(path, case) {
            Ok(VerifyResult::Counterexample { .. }) => {}
            Ok(result) => failures.push(format!(
                "{case} ({upstream_case}) should be rejected, got: {result:?}"
            )),
            Err(err) => failures.push(format!("{case} ({upstream_case}) should extract: {err}")),
        }
    }

    assert!(
        failures.is_empty(),
        "counterexample bitvector cases failed:\n{}",
        failures.join("\n")
    );
}

#[test]
fn bitvector_rs_counterexample_subset_is_rejected_from_file() {
    let path = bitvector_port_path();
    let path = path.to_str().expect("port path should be UTF-8");
    assert_all_counterexamples(path, COUNTEREXAMPLE_CASES);
}

#[test]
fn bitvector_rs_fail_closed_diagnostics_from_file() {
    let path = bitvector_port_path();
    let path = path.to_str().expect("port path should be UTF-8");

    for (case, upstream_case, expected_fragments) in FAIL_CLOSED_ERROR_CASES {
        let message = match verify_function_from_file(path, case) {
            Ok(VerifyResult::Error { message }) => message,
            Ok(result) => {
                panic!("{case} ({upstream_case}) should fail closed with Error, got: {result:?}");
            }
            Err(err) => err.to_string(),
        };
        for fragment in *expected_fragments {
            assert!(
                message.contains(fragment),
                "{case} ({upstream_case}) error should contain {fragment:?}, got: {message}",
            );
        }
    }
}

#[test]
fn bitvector_signed_i8_min_div_neg_one_checked_rust_fails_closed() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_parsed("x", "i8");
    ctx.declare_var_parsed("y", "i8");
    ctx.push_obligation(ProofObligation::assume("x_min", "x == -128"));
    ctx.push_obligation(ProofObligation::assume("y_neg1", "y == -1"));
    ctx.push_obligation(
        ProofObligation::assert("div_taut", "x / y == x / y")
            .with_solver_mode(SolverMode::BitVector),
    );

    let result = ctx.verify();
    assert!(
        matches!(
            result,
            VerifyResult::Counterexample { .. } | VerifyResult::Error { .. }
        ),
        "checked Rust i8::MIN / -1 must not verify; widened `int` math is the promoted case, got: {result:?}"
    );
}

#[test]
fn bitvector_unsigned_unconstrained_divisor_fails_closed() {
    let mut ctx = VerificationContext::new().with_overflow_checks();
    ctx.declare_var_parsed("x", "u32");
    ctx.declare_var_parsed("y", "u32");
    ctx.push_obligation(ProofObligation::assume("x_val", "x == 100"));
    ctx.push_obligation(
        ProofObligation::assert("div_taut", "x / y == x / y")
            .with_solver_mode(SolverMode::BitVector),
    );

    let result = ctx.verify();
    assert!(
        matches!(
            result,
            VerifyResult::Counterexample { .. } | VerifyResult::Error { .. }
        ),
        "u32 division by an unconstrained divisor must not verify; div-by-zero remains fail-closed, got: {result:?}"
    );
}
