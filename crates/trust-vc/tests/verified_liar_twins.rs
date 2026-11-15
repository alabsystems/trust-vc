// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Refuted twins for programs the syn lane answers `Verified` where an older
//! pin expected an error (decision TV-12 in `docs/decisions.md`).
//!
//! Each of these programs satisfies its specification, so `Verified` is the
//! right answer. The evidence that the lane reads them, rather than
//! proving everything near them, is here: each twin makes one small change to
//! a verified program so that it states something false, and must come back
//! as a counterexample.
//!
//! * integers `test_enum_to_int_overflow_wrap`: `v as u8` where `C` is 256.
//! * regression `regression_let_with_parens_issue260`: `let (x): usize = 0`.
//! * spec_derive `make_spec_type_hash_map_field_view_fails_closed_error`: a
//!   `HashMap` field's `view().contains_key(k)` compared with itself.
//! * z3_restart `upstream_order` (in `z3_restart_rs_trust_vc_regressions.rs`):
//!   a bit-vector `&` fact ahead of a `by(nonlinear_arith)` query.

use std::path::Path;
use trust_vc_core::{
    extract_verification_conditions_with_file_context, verify_function_from_file, VerifyResult,
};

fn port_path(file: &str) -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../evals/verus/ported")
        .join(file)
}

fn port_source(file: &str) -> String {
    std::fs::read_to_string(port_path(file))
        .unwrap_or_else(|err| panic!("{file} port should be readable: {err}"))
}

/// Verify `case` from `source`, reading the whole file as its context.
fn verify_case(source: &str, case: &str) -> VerifyResult {
    let file = syn::parse_file(source).expect("fixture should parse as Rust");
    let func = file
        .items
        .iter()
        .find_map(|item| match item {
            syn::Item::Fn(func) if func.sig.ident == case => Some(func),
            _ => None,
        })
        .unwrap_or_else(|| panic!("{case} should exist in the fixture"));
    match extract_verification_conditions_with_file_context(&file, func) {
        Ok(vc) => vc.verify(),
        Err(err) => VerifyResult::Error {
            message: err.to_string(),
        },
    }
}

fn expect_verified(source: &str, case: &str) {
    let result = verify_case(source, case);
    assert!(
        matches!(result, VerifyResult::Verified),
        "{case} states a true property and should verify, got: {result:?}"
    );
}

fn expect_refuted(source: &str, cases: &[&str]) {
    let failures: Vec<String> = cases
        .iter()
        .filter_map(|case| {
            let result = verify_case(source, case);
            (!matches!(result, VerifyResult::Counterexample { .. }))
                .then(|| format!("{case} states a false property, got: {result:?}"))
        })
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Appended to the integers port, whose `IntegerCastEnum` is `A`, `B = 255`
/// and the implicit successor `C = 256`.
const ENUM_TO_U8_TWINS: &str = r#"
#[trust_vc::ensures(result as usize == v as usize)]
fn overflow_wrap_untruncated_liar(v: IntegerCastEnum) -> u8 {
    v as u8
}

#[trust_vc::ensures(result == v as u8)]
fn overflow_wrap_off_by_one_liar(v: IntegerCastEnum) -> u8 {
    (v as u8).wrapping_add(1u8)
}

#[trust_vc::ensures(true)]
fn c_truncates_to_zero() {
    trust_vc::assert!(IntegerCastEnum::C as u8 == 0u8);
}

#[trust_vc::ensures(true)]
fn c_truncates_to_zero_liar() {
    trust_vc::assert!(IntegerCastEnum::C as u8 == 255u8);
}
"#;

#[test]
fn enum_to_u8_overflow_cast_verifies_from_the_integers_port() {
    let path = port_path("integers.rs");
    let result = verify_function_from_file(
        path.to_str().expect("integers port path should be UTF-8"),
        "test_enum_to_int_overflow_wrap",
    )
    .unwrap_or_else(|err| panic!("test_enum_to_int_overflow_wrap should extract: {err}"));
    assert!(
        matches!(result, VerifyResult::Verified),
        "test_enum_to_int_overflow_wrap should verify, got: {result:?}"
    );
}

#[test]
fn enum_to_u8_cast_truncates_and_its_liar_twins_are_refuted() {
    let mut source = port_source("integers.rs");
    source.push_str(ENUM_TO_U8_TWINS);
    expect_verified(&source, "c_truncates_to_zero");
    expect_refuted(
        &source,
        &[
            "overflow_wrap_untruncated_liar",
            "overflow_wrap_off_by_one_liar",
            "c_truncates_to_zero_liar",
        ],
    );
}

/// Appended to the regression port, beside `regression_let_with_parens_issue260`.
/// `upstream_g` is the failing half of upstream's case.
const PAREN_LET_TWINS: &str = r#"
#[trust_vc::ensures(true)]
fn upstream_g() {
    let (x): usize = 0usize;
    trust_vc::assert!(x == 1usize);
}

#[trust_vc::requires(x == 5usize)]
#[trust_vc::ensures(true)]
fn shadows_a_parameter_liar(x: usize) {
    let (x): usize = 0usize;
    trust_vc::assert!(x == 5usize);
}

#[trust_vc::ensures(true)]
fn ends_with_its_block_liar() {
    let x: usize = 1usize;
    {
        let (x): usize = 0usize;
    }
    trust_vc::assert!(x == 0usize);
}

#[trust_vc::ensures(true)]
fn mut_binding_is_assigned_liar() {
    let (mut x): usize = 0usize;
    x = 3usize;
    trust_vc::assert!(x == 0usize);
}

#[trust_vc::ensures(result == 0usize)]
fn binds_its_initializer_liar(y: usize) -> usize {
    let (x): usize = y;
    x
}
"#;

#[test]
fn paren_let_binding_liar_twins_are_refuted() {
    let mut source = port_source("regression.rs");
    source.push_str(PAREN_LET_TWINS);
    expect_refuted(
        &source,
        &[
            "upstream_g",
            "shadows_a_parameter_liar",
            "ends_with_its_block_liar",
            "mut_binding_is_assigned_liar",
            "binds_its_initializer_liar",
        ],
    );
}

/// Appended to the spec_derive port, whose `StructWithHashMap` has the field
/// `u: HashMap<u32, u32>`.
const HASH_MAP_FIELD_VIEW_TWINS: &str = r#"
fn hash_map_field_view_ne_liar(original: StructWithHashMap) {
    trust_vc::assert!(original.u.view().contains_key(3u32) != original.u.view().contains_key(3u32));
}

fn hash_map_field_view_contains_liar(original: StructWithHashMap) {
    trust_vc::assert!(original.u.view().contains_key(3u32));
}

fn hash_map_field_view_lacks_liar(original: StructWithHashMap) {
    trust_vc::assert!(!original.u.view().contains_key(3u32));
}

fn hash_map_field_view_other_key_liar(original: StructWithHashMap) {
    trust_vc::assert!(original.u.view().contains_key(3u32) == original.u.view().contains_key(4u32));
}
"#;

#[test]
fn hash_map_field_view_liar_twins_are_refuted() {
    let mut source = port_source("spec_derive.rs");
    source.push_str(HASH_MAP_FIELD_VIEW_TWINS);
    expect_refuted(
        &source,
        &[
            "hash_map_field_view_ne_liar",
            "hash_map_field_view_contains_liar",
            "hash_map_field_view_lacks_liar",
            "hash_map_field_view_other_key_liar",
        ],
    );
}

/// Upstream's statement order of `test_with_bitvec_nlarith`'s last three
/// statements, with one of them made false, or a false assert appended.
const BITVEC_FACT_BEFORE_NONLINEAR_TWINS: &str = r#"
use trust_vc_types::{int, Multiset};

#[trust_vc::verifier(spinoff_prover)]
#[trust_vc::requires(x < 0xfffu32)]
#[trust_vc::ensures(true)]
fn bit_vector_liar(x: u32, y: u32, z: u32) {
    trust_vc::assert_by_bit_vector!(!(x < 0xfffu32) || (x & y < 0xffu32));
    trust_vc::assert!(x & y < 0xfffu32);
    trust_vc::assert_by_nonlinear!(x * y * z == y * x * z);
}

#[trust_vc::verifier(spinoff_prover)]
#[trust_vc::requires(x < 0xfffu32)]
#[trust_vc::ensures(true)]
fn plain_assert_liar(x: u32, y: u32, z: u32) {
    trust_vc::assert_by_bit_vector!(!(x < 0xfffu32) || (x & y < 0xfffu32));
    trust_vc::assert!(x & y < 0xffu32);
    trust_vc::assert_by_nonlinear!(x * y * z == y * x * z);
}

#[trust_vc::verifier(spinoff_prover)]
#[trust_vc::requires(x < 0xfffu32)]
#[trust_vc::ensures(true)]
fn nonlinear_liar(x: u32, y: u32, z: u32) {
    trust_vc::assert_by_bit_vector!(!(x < 0xfffu32) || (x & y < 0xfffu32));
    trust_vc::assert!(x & y < 0xfffu32);
    trust_vc::assert_by_nonlinear!(x * y < 0xfffu32);
}

#[trust_vc::verifier(spinoff_prover)]
#[trust_vc::requires(x < 0xfffu32)]
#[trust_vc::ensures(true)]
fn context_not_inconsistent(x: u32, y: u32, z: u32) {
    trust_vc::assert_by_bit_vector!(!(x < 0xfffu32) || (x & y < 0xfffu32));
    trust_vc::assert!(x & y < 0xfffu32);
    trust_vc::assert_by_nonlinear!(x * y * z == y * x * z);
    trust_vc::assert!(false);
}
"#;

#[test]
fn bitvec_fact_before_nonlinear_query_liar_twins_are_refuted() {
    expect_refuted(
        BITVEC_FACT_BEFORE_NONLINEAR_TWINS,
        &[
            "bit_vector_liar",
            "plain_assert_liar",
            "nonlinear_liar",
            "context_not_inconsistent",
        ],
    );
}
