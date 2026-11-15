//! Genuine filesystem rejection before any builtin compiler can be launched.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);

#[test]
fn a_symlink_to_a_prebuilt_file_is_not_a_fresh_output() {
    let root = std::env::temp_dir().join(format!(
        "trust-vc-builtin-output-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&root).unwrap();
    let output = root.join("fresh");
    std::fs::create_dir(&output).unwrap();
    let output = output.canonicalize().unwrap();
    let outside = root.join("prebuilt.rlib");
    std::fs::write(&outside, b"external prebuilt bytes").unwrap();
    let entry = output.join("libverus_builtin.rlib");
    std::os::unix::fs::symlink(&outside, &entry).unwrap();
    assert!(entry.canonicalize().unwrap().is_file());
    assert!(output_artifact(&output, "libverus_builtin.rlib").is_err());
    std::fs::remove_file(&entry).unwrap();
    std::fs::write(&entry, b"actual regular output").unwrap();
    let file = output_artifact(&output, "libverus_builtin.rlib").unwrap();
    assert_eq!(file.path, entry);
    assert_eq!(file.sha256, digest(b"actual regular output"));
    std::fs::remove_dir_all(root).unwrap();
}

#[test]
fn a_forged_locked_archive_cannot_start_a_native_build() {
    let root = std::env::temp_dir().join(format!(
        "trust-vc-builtin-origin-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&root).unwrap();
    let source = root.join("source");
    std::fs::create_dir(&source).unwrap();
    std::fs::write(source.join("library.rs"), "// approved fixture\n").unwrap();
    let manifest = root.join("manifest.json");
    std::fs::write(
        &manifest,
        serde_json::to_vec(&serde_json::json!({
            "git_commit": "native-build-negative-control", "archive_sha256": "00".repeat(32),
            "files_sha256": {"library.rs": hexadecimal(digest(b"// approved fixture\n"))},
            "symlink_targets": {}
        }))
        .unwrap(),
    )
    .unwrap();
    let sources = Sources::load(
        &source,
        PinnedFile {
            sha256: digest(&std::fs::read(&manifest).unwrap()),
            path: manifest,
        },
        None,
    )
    .unwrap();
    let mut archives = Vec::new();
    for (name, _) in ARCHIVES {
        let path = root.join(name);
        std::fs::write(&path, "not the pinned archive").unwrap();
        archives.push(PinnedFile {
            path,
            sha256: digest(b"not the pinned archive"),
        });
    }
    let output = root.join("not-created");
    let driver = super::super::identity::loaded_driver().unwrap();
    let Err(error) = build(&sources, &archives, &output, &driver) else {
        panic!("forged payload cannot establish a build origin");
    };
    assert!(error.contains("archive checksum"), "{error}");
    assert!(
        !output.exists(),
        "validation must precede output creation/compiler invocation"
    );
    std::fs::remove_dir_all(root).unwrap();
}
