// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::{
    checked_in_snapshot_diff, diff_snapshots, generate_api_surface_snapshot_from_manifest,
    PROTECTED_CRATES,
};
use std::fs;
use std::path::PathBuf;
use std::sync::{Mutex, OnceLock};
use std::time::{SystemTime, UNIX_EPOCH};

macro_rules! checked_in_snapshot_matches_test {
    ($name:ident, $protected:expr) => {
        #[test]
        fn $name() {
            let protected = $protected;
            let diff = with_api_surface_generation_lock(|| {
                checked_in_snapshot_diff(protected)
                    .expect("checked-in snapshot diff should succeed")
            });
            assert!(
                diff.is_empty(),
                "checked-in API surface drifted for {}:\n{}",
                protected.package_name(),
                diff.render(protected.package_name())
            );
        }
    };
}

checked_in_snapshot_matches_test!(
    checked_in_snapshot_matches_fresh_generation_for_trust_vc,
    PROTECTED_CRATES[0]
);
checked_in_snapshot_matches_test!(
    checked_in_snapshot_matches_fresh_generation_for_trust_vc_core,
    PROTECTED_CRATES[1]
);
checked_in_snapshot_matches_test!(
    checked_in_snapshot_matches_fresh_generation_for_trust_vc_types,
    PROTECTED_CRATES[2]
);
checked_in_snapshot_matches_test!(
    checked_in_snapshot_matches_fresh_generation_for_trust_vc_merge_contract,
    PROTECTED_CRATES[3]
);
checked_in_snapshot_matches_test!(
    checked_in_snapshot_matches_fresh_generation_for_trust_vc_merge_runner,
    PROTECTED_CRATES[4]
);
checked_in_snapshot_matches_test!(
    checked_in_snapshot_matches_fresh_generation_for_trust_vc_trust_engine,
    PROTECTED_CRATES[5]
);

#[test]
fn api_surface_generation_is_deterministic_for_temp_probe() {
    let temp_dir = unique_temp_dir("api-surface-determinism");
    fs::create_dir_all(&temp_dir).expect("temp dir should be creatable");
    fs::write(
        temp_dir.join("Cargo.toml"),
        "[package]\nname = \"api_probe_determinism\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[lib]\npath = \"lib.rs\"\n",
    )
    .expect("Cargo.toml should write");
    fs::write(
        temp_dir.join("lib.rs"),
        "pub struct Counter(u32);\nimpl Counter {\n    pub fn next(self) -> Self { Counter(self.0 + 1) }\n}\n",
    )
    .expect("lib.rs should write");

    let first = with_api_surface_generation_lock(|| {
        generate_api_surface_snapshot_from_manifest(
            "api_probe_determinism",
            &temp_dir.join("Cargo.toml"),
            &temp_dir.join("target"),
        )
        .expect("first snapshot generation should succeed")
    });
    let second = with_api_surface_generation_lock(|| {
        generate_api_surface_snapshot_from_manifest(
            "api_probe_determinism",
            &temp_dir.join("Cargo.toml"),
            &temp_dir.join("target"),
        )
        .expect("second snapshot generation should succeed")
    });
    assert_eq!(
        first.lines(),
        second.lines(),
        "API surface generation must be deterministic for temp probe"
    );

    let _ = fs::remove_dir_all(temp_dir);
}

#[test]
fn snapshot_diff_reports_removed_and_added_items() {
    let expected = vec![
        "struct trust_vc_types::Seq<T>".to_owned(),
        "fn trust_vc::proof()".to_owned(),
    ];
    let actual = vec![
        "struct trust_vc_types::Seq<T>".to_owned(),
        "fn trust_vc::broadcast()".to_owned(),
    ];
    let diff = diff_snapshots(&expected, &actual);
    assert_eq!(diff.removed(), &["fn trust_vc::proof()".to_owned()]);
    assert_eq!(diff.added(), &["fn trust_vc::broadcast()".to_owned()]);
}

#[test]
fn reexports_use_public_alias_paths() {
    let temp_dir = unique_temp_dir("api-surface-reexport");
    fs::create_dir_all(&temp_dir).expect("temp dir should be creatable");
    fs::write(
        temp_dir.join("Cargo.toml"),
        "[package]\nname = \"api_probe\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[lib]\npath = \"lib.rs\"\n",
    )
    .expect("Cargo.toml should write");
    fs::write(
        temp_dir.join("lib.rs"),
        "mod hidden {\n    pub struct Foo;\n    impl Foo {\n        pub fn make() -> Self { Foo }\n    }\n}\n\npub use hidden::Foo as PublicFoo;\n\npub struct Context;\nimpl Context {\n    pub fn verify(&self) -> PublicFoo { PublicFoo::make() }\n}\n",
    )
    .expect("lib.rs should write");

    let snapshot = generate_api_surface_snapshot_from_manifest(
        "api_probe",
        &temp_dir.join("Cargo.toml"),
        &temp_dir.join("target"),
    )
    .expect("temp crate API surface generation should succeed");

    assert!(snapshot
        .lines()
        .contains(&"pub use api_probe::PublicFoo = hidden::Foo".to_owned()));
    assert!(snapshot
        .lines()
        .contains(&"struct api_probe::PublicFoo".to_owned()));
    assert!(snapshot
        .lines()
        .contains(&"fn api_probe::PublicFoo::make() -> Self".to_owned()));
    assert!(snapshot
        .lines()
        .contains(&"fn api_probe::Context::verify(self: &Self) -> PublicFoo".to_owned()));
    assert!(
        !snapshot
            .lines()
            .iter()
            .filter(|line| !line.starts_with("pub use "))
            .any(|line| {
                line.contains("api_probe::hidden::Foo") || line.contains("hidden::Foo")
            }),
        "hidden definition paths should not leak into public surface output outside the alias declaration"
    );

    let _ = fs::remove_dir_all(temp_dir);
}

#[test]
fn external_reexports_are_recorded_without_requiring_local_item_details() {
    let temp_dir = unique_temp_dir("api-surface-external-reexport");
    fs::create_dir_all(&temp_dir).expect("temp dir should be creatable");
    fs::write(
        temp_dir.join("Cargo.toml"),
        "[package]\nname = \"api_probe_external\"\nversion = \"0.1.0\"\nedition = \"2021\"\n\n[lib]\npath = \"lib.rs\"\n",
    )
    .expect("Cargo.toml should write");
    fs::write(temp_dir.join("lib.rs"), "pub use std::num::NonZeroUsize;\n")
        .expect("lib.rs should write");

    let snapshot = generate_api_surface_snapshot_from_manifest(
        "api_probe_external",
        &temp_dir.join("Cargo.toml"),
        &temp_dir.join("target"),
    )
    .expect("temp crate API surface generation should succeed");

    assert!(snapshot.lines().iter().any(|line| {
        line.starts_with("pub use api_probe_external::NonZeroUsize = ")
            && line.contains("NonZeroUsize")
    }));

    let _ = fs::remove_dir_all(temp_dir);
}

fn unique_temp_dir(prefix: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("clock should be after UNIX_EPOCH")
        .as_nanos();
    std::env::temp_dir().join(format!("{prefix}-{}-{nanos}", std::process::id()))
}

fn with_api_surface_generation_lock<T>(f: impl FnOnce() -> T) -> T {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    // The lock only serializes API-surface generation; the guarded `()` carries
    // no invariant. Recover from poisoning so that one panicking test does not
    // cascade `PoisonError` into every other test sharing this lock.
    let _guard = LOCK
        .get_or_init(|| Mutex::new(()))
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    f()
}
