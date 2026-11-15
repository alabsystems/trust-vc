// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Source {
    root: PathBuf,
    file: PathBuf,
}
impl Source {
    fn new() -> Self {
        let root = std::env::temp_dir().join(format!(
            "trust-vc-normal-invocation-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&root).unwrap();
        let root = root.canonicalize().unwrap();
        let file = root.join("input.rs");
        std::fs::write(&file, "fn main() {}\n").unwrap();
        Self { root, file }
    }
    fn request(&self, options: &[&str]) -> Result<NormalInvocation, String> {
        let mut argv = vec![
            "--internal-test-mode".to_string(),
            "--crate-name=actual_client".to_string(),
            self.file.display().to_string(),
            "-o".into(),
            self.root.join("out.rmeta").display().to_string(),
        ];
        argv.extend(options.iter().map(|s| s.to_string()));
        NormalInvocation::derive("actual-rust-verify".into(), args::split(&argv).unwrap())
    }
    fn pin(&self) -> PinnedFile {
        PinnedFile {
            path: self.file.clone(),
            sha256: Sha256::digest(std::fs::read(&self.file).unwrap()).into(),
        }
    }
}
impl Drop for Source {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.root).unwrap();
    }
}

#[test]
fn one_actual_split_derives_native_vectors_and_nondefault_semantics() {
    let source = Source::new();
    let plan = source
        .request(&[
            "--no-external-by-default",
            "-V",
            "new-mut-ref",
            "--no-cheating",
            "--no-verify",
            "--rlimit",
            "0.75",
            "--multiple-errors",
            "3",
            "--no-auto-recommends-check",
        ])
        .unwrap();
    let split = plan.original().unwrap();
    assert_eq!(&plan.verify()[1..1 + split.rustc.len()], split.rustc);
    assert_eq!(&plan.erase()[1..1 + split.rustc.len()], split.rustc);
    assert!(!plan
        .verify()
        .iter()
        .any(|s| s == "new-mut-ref" || s == "--no-verify"));
    let options = plan.options();
    assert!(options.read.new_mut_ref && options.read.no_external_by_default);
    assert!(options.no_verify && options.no_cheating);
    assert_eq!(options.verify.rlimit, Some(Some(0.75)));
    assert_eq!(options.verify.multiple_errors, 3);
    assert!(!options.verify.auto_recommends);
    assert!(options.erase_args.as_deref() == Some(plan.erase()));
    plan.source_matches(&source.pin()).unwrap();
}

#[test]
fn invalid_options_never_fall_back_to_default_verification() {
    let source = Source::new();
    for options in [
        &["--rlimit", "0"][..],
        &["--rlimit", "NaN"],
        &["--multiple-errors", "bad"],
        &["--compile", "--no-erasure-check"],
    ] {
        assert!(source.request(options).is_err(), "{options:?}");
    }
}

#[test]
fn real_derivation_preserves_lifetime_and_compile_combinations() {
    let source = Source::new();
    for (flags, expected) in [
        (&[][..], (true, true, true)),
        (&["--no-erasure-check"][..], (true, true, false)),
        (&["--no-lifetime"][..], (false, false, false)),
        (&["--no-lifetime", "--compile"][..], (true, false, true)),
    ] {
        let plan = source.request(flags).unwrap();
        let options = plan.options();
        assert_eq!(
            (
                plan.expects_erase(),
                options.lifetime_check,
                options.erase_compile
            ),
            expected
        );
        assert_eq!(options.erase_args.is_some(), plan.expects_erase());
    }
}

#[test]
fn real_source_snapshot_rejects_changed_bytes_and_another_source() {
    let source = Source::new();
    let plan = source.request(&[]).unwrap();
    let original = source.pin();
    let other = Source::new();
    assert!(plan.source_matches(&other.pin()).is_err());
    std::fs::write(&source.file, "fn changed() {}\n").unwrap();
    assert!(plan.source_matches(&original).is_err());
    assert!(plan.source_matches(&source.pin()).is_err());
}

#[cfg(unix)]
#[test]
fn same_byte_source_alias_retarget_is_not_the_original_request() {
    let source = Source::new();
    let alias = source.root.join("alias.rs");
    std::os::unix::fs::symlink(&source.file, &alias).unwrap();
    let split = args::split(&[alias.display().to_string()]).unwrap();
    let plan = NormalInvocation::derive("actual-rust-verify".into(), split).unwrap();
    plan.source_matches(&source.pin()).unwrap();
    let duplicate = source.root.join("same.rs");
    std::fs::copy(&source.file, &duplicate).unwrap();
    std::fs::remove_file(&alias).unwrap();
    std::os::unix::fs::symlink(&duplicate, &alias).unwrap();
    assert!(plan.source_matches(&source.pin()).is_err());
}

#[test]
fn missing_input_can_receive_native_diagnostics_but_cannot_bind_an_owner() {
    let source = Source::new();
    let missing = source.root.join("absent.rs");
    let plan = NormalInvocation::derive(
        "actual-rust-verify".into(),
        args::split(&[missing.display().to_string()]).unwrap(),
    )
    .unwrap();
    assert!(plan.source_matches(&source.pin()).is_err());
    assert!(plan
        .verify()
        .iter()
        .any(|s| s == &missing.display().to_string()));
}

#[test]
fn nonregular_entry_is_not_pre_read_by_the_optional_snapshot() {
    let source = Source::new();
    let directory = source.root.join("stream.rs");
    std::fs::create_dir(&directory).unwrap();
    let plan = NormalInvocation::derive(
        "actual-rust-verify".into(),
        args::split(&[directory.display().to_string()]).unwrap(),
    )
    .unwrap();
    assert!(plan
        .source_matches(&source.pin())
        .unwrap_err()
        .contains("regular source file"));
    assert!(plan
        .verify()
        .iter()
        .any(|s| s == &directory.display().to_string()));
}
