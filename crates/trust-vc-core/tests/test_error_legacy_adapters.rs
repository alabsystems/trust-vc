//! Regression tests for typed bridge errors and remaining legacy adapters.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod common;

use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};
use syn::{parse_str, ItemFn};
use trust_vc_core::verify_macro::{verify_markers_impl, verify_proof_impl};
use trust_vc_core::{
    clear_extern_contracts, extract_verification_conditions, register_extern_spec_from_call_site,
    register_extern_spec_from_source, verify_function_from_file, TrustVcError,
};

fn unique_test_dir(name: &str) -> PathBuf {
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time should be after unix epoch")
        .as_nanos();
    PathBuf::from("target")
        .join("test_error_legacy_adapters")
        .join(format!("{name}_{nonce}"))
}

#[test]
fn verify_function_from_file_returns_typed_read_error() {
    let missing = unique_test_dir("missing_verify").join("missing.rs");
    let error =
        verify_function_from_file(missing.to_str().expect("path should be utf-8"), "missing")
            .expect_err("missing source file should fail");

    match error {
        TrustVcError::Io { context, .. } => {
            assert_eq!(context, "read verification source file");
        }
        other => panic!("expected TrustVcError::Io for missing source file, got: {other:?}"),
    }
}

#[test]
fn extract_verification_conditions_returns_typed_return_error() {
    let code = r#"
        fn always_positive() -> i32 {
            let x = 42;
            x;
        }
    "#;

    let func = parse_str::<ItemFn>(code).expect("test function should parse");
    let error = extract_verification_conditions(&func)
        .expect_err("missing return expression should fail closed");

    match error {
        TrustVcError::Internal { context, detail } => {
            assert_eq!(context, "extract verification conditions");
            assert_eq!(
                detail,
                "Function 'always_positive' has return type but no detectable return expression — postconditions referencing `result` would be unsound"
            );
        }
        other => {
            panic!("expected TrustVcError::Internal for missing return expression, got: {other:?}")
        }
    }
}

#[test]
fn verify_markers_impl_preserves_legacy_result_message_shape() {
    common::with_clean_verification(|| {
        let test_dir = unique_test_dir("verify_markers");
        let test_file = test_dir.join("no_markers.rs");
        fs::create_dir_all(&test_dir).expect("should create marker test directory");
        fs::write(
            &test_file,
            r#"
                fn regular_function() {}
            "#,
        )
        .expect("should write marker test file");

        let error = verify_markers_impl(
            "test::module",
            test_file.to_str().expect("path should be utf-8"),
        )
        .expect_err("file without markers should fail");

        fs::remove_dir_all(&test_dir).ok();

        assert!(
            error.starts_with("✗ Verification error for test::module\n  Error: No trust_vc verification markers found"),
            "public adapter should keep the legacy result format, got: {error}"
        );
        assert!(
            !error.starts_with("marker verification:"),
            "public adapter should not leak TrustVcError context, got: {error}"
        );
    });
}

#[test]
fn verify_proof_impl_preserves_outer_context_prefix() {
    common::with_clean_verification(|| {
        let missing = unique_test_dir("verify_proof").join("missing.rs");
        let error = verify_proof_impl(
            "missing_proof",
            "test::module",
            missing.to_str().expect("path should be utf-8"),
        )
        .expect_err("missing proof source should fail");

        assert!(
            error.starts_with(&format!(
                "Error verifying test::module::missing_proof: Failed to read file {}: ",
                missing.display()
            )),
            "proof adapter should preserve legacy outer context, got: {error}"
        );
    });
}

#[test]
fn register_extern_spec_from_source_returns_typed_not_found_error() {
    clear_extern_contracts();

    let error = register_extern_spec_from_source(
        "register_mismatch.rs",
        r#"
            trust_vc::extern_spec! {
                impl std::vec::Vec::<T> {
                    fn pop(&mut self) -> Option<T>;
                }
            }
        "#,
        "Vec::<i32>::pop",
    )
    .expect_err("lexical mismatch should fail closed");

    match error {
        TrustVcError::Internal { context, detail } => {
            assert_eq!(context, "register extern_spec from source");
            assert!(
                detail.starts_with(
                    "no extern_spec for `Vec::<i32>::pop` found in `register_mismatch.rs`; lookup is file-local only"
                ),
                "typed error detail should preserve lookup guidance, got: {detail}"
            );
            assert!(
                detail.contains("external_spec!"),
                "typed error detail should mention the preferred alias spelling, got: {detail}"
            );
        }
        other => panic!(
            "expected TrustVcError::Internal for extern_spec lexical mismatch, got: {other:?}"
        ),
    }
}

#[test]
fn register_extern_spec_from_source_parse_error_mentions_both_spellings() {
    clear_extern_contracts();

    let error = register_extern_spec_from_source(
        "register_parse_error.rs",
        r#"
            trust_vc::external_spec! {
                nope
            }
        "#,
        "i32::abs",
    )
    .expect_err("invalid external_spec input should fail");

    match error {
        TrustVcError::Parse { context, .. } => {
            assert_eq!(context, "parse extern_spec! declaration from source text");
        }
        other => {
            panic!("expected TrustVcError::Parse for extern_spec parse failure, got: {other:?}")
        }
    }
}

#[test]
fn register_extern_spec_from_call_site_returns_typed_absolute_read_error() {
    clear_extern_contracts();

    let missing = std::env::current_dir()
        .expect("current dir should exist")
        .join(unique_test_dir("extern_call_site"))
        .join("missing.rs");
    let error = register_extern_spec_from_call_site(
        missing.to_str().expect("path should be utf-8"),
        Path::new(".")
            .to_str()
            .expect("relative path should be utf-8"),
        "i32::abs",
    )
    .expect_err("missing absolute call-site file should fail");

    match error {
        TrustVcError::Io { context, .. } => {
            assert_eq!(context, "read absolute call-site source");
        }
        other => {
            panic!("expected TrustVcError::Io for missing absolute call-site file, got: {other:?}")
        }
    }
}
