// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression coverage for #945 naming aliases.

use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::{clear_extern_contracts, register_extern_spec_from_manifest_scope};

trust_vc::external_spec! {
    impl<T> core::option::Option::<T> {
        #[requires(self.is_some())]
        fn unwrap(self) -> T;
    }
}

mod common;

struct ManifestFixture {
    cleanup_root: PathBuf,
    manifest_dir: PathBuf,
}

impl ManifestFixture {
    fn new(name: &str) -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system time should be after unix epoch")
            .as_nanos();
        let cleanup_root = PathBuf::from("target")
            .join("api_naming_aliases")
            .join(format!("{name}_{nonce}"));
        let manifest_dir = cleanup_root.join("crate");

        fs::create_dir_all(&manifest_dir).expect("should create manifest dir");
        fs::write(
            manifest_dir.join("Cargo.toml"),
            "[package]\nname = \"fixture\"\nversion = \"0.1.0\"\nedition = \"2021\"\n",
        )
        .expect("should write fixture manifest");

        Self {
            cleanup_root,
            manifest_dir,
        }
    }

    fn manifest_dir(&self) -> &Path {
        &self.manifest_dir
    }

    fn write(&self, relative_path: &str, source: &str) {
        let path = self.manifest_dir.join(relative_path);
        fs::create_dir_all(path.parent().expect("fixture file should have a parent"))
            .expect("should create fixture directories");
        fs::write(path, source).expect("should write fixture source");
    }
}

impl Drop for ManifestFixture {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.cleanup_root).ok();
    }
}

#[test]
fn test_assert_with_proof_alias_verifies_two_arg_form() {
    let result = common::verify_should_pass(|| {
        trust_vc::assert_with_proof!(2 + 2 == 4, {
            trust_vc::assert!(2 + 2 == 4);
        });
    });

    assert!(
        matches!(result, trust_vc_core::VerifyResult::Verified),
        "assert_with_proof! alias should verify like assert_by!, got: {result:?}"
    );
}

#[test]
fn test_assume_by_single_arg_works_as_assume() {
    let result = common::verify_should_pass(|| {
        trust_vc::assume_by!(2 + 2 == 4);
        trust_vc::assert!(2 + 2 == 4);
    });

    assert!(
        matches!(result, trust_vc_core::VerifyResult::Verified),
        "assume_by! single-arg should work as assume!, got: {result:?}"
    );
}

#[test]
fn test_assume_by_two_arg_scoped_assumption_verifies() {
    let result = common::verify_should_pass(|| {
        trust_vc::assume_by!(1 + 1 == 2, {
            trust_vc::assert!(1 + 1 == 2);
        });
    });

    assert!(
        matches!(result, trust_vc_core::VerifyResult::Verified),
        "assume_by! two-arg scoped form should verify, got: {result:?}"
    );
}

#[test]
fn test_external_spec_alias_registers_same_file_manifest_scope_contract() {
    common::with_clean_verification(|| {
        clear_extern_contracts();

        let fixture = ManifestFixture::new("external_spec_alias_same_file");
        fixture.write(
            "tests/call_site.rs",
            r#"
                trust_vc::external_spec! {
                    impl i32 {
                        #[requires(false)]
                        fn abs(self) -> i32;
                    }
                }
            "#,
        );

        register_extern_spec_from_manifest_scope(
            "tests/call_site.rs",
            fixture
                .manifest_dir()
                .to_str()
                .expect("manifest dir should be utf-8"),
            "i32::abs",
        )
        .expect("external_spec! alias should register from manifest scope");

        let result = VerificationPipeline::collect_from_macros().verify();
        assert!(
            matches!(result, trust_vc_core::VerifyResult::Counterexample { .. }),
            "same-file external_spec! requires(false) should reach verification, got: {result:?}"
        );
    });
}
