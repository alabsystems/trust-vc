// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Filesystem guards use ordinary data, never fake compiler artifacts or
//! a forged BuiltCohort/BuiltArtifact/metadata/permission token.

use super::*;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Temp(PathBuf);

impl Temp {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "client-search-data-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path.canonicalize().unwrap())
    }
    fn pin(&self, name: &str) -> PinnedFile {
        let path = self.0.join(name);
        std::fs::write(&path, b"ordinary path-guard test data").unwrap();
        PinnedFile {
            path,
            sha256: super::super::digest(b"ordinary path-guard test data"),
        }
    }
}

impl Drop for Temp {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            std::fs::remove_dir_all(&self.0).unwrap();
        }
    }
}

#[test]
fn link_guard_rejects_replacement_even_with_the_same_target_and_bytes() {
    let temp = Temp::new();
    let target = temp.pin("source.data");
    let origin_id = regular(&target).unwrap();
    let path = temp.0.join("link.data");
    std::os::unix::fs::symlink(&target.path, &path).unwrap();
    let link_id = FileId::of(&std::fs::symlink_metadata(&path).unwrap());
    check_link(&path, &target, link_id, origin_id).unwrap();
    std::fs::rename(&path, temp.0.join("retired.data")).unwrap();
    std::os::unix::fs::symlink(&target.path, &path).unwrap();
    assert!(check_link(&path, &target, link_id, origin_id).is_err());
}

#[test]
fn physical_file_guard_does_not_accept_a_symlink_to_identical_data() {
    let temp = Temp::new();
    let target = temp.pin("source.data");
    let copy = temp.pin("copy.data");
    regular(&copy).unwrap();
    std::fs::remove_file(&copy.path).unwrap();
    std::os::unix::fs::symlink(&target.path, &copy.path).unwrap();
    assert!(regular(&copy).is_err());
}

#[test]
fn closed_directory_guard_rejects_added_and_missing_entries() {
    let temp = Temp::new();
    temp.pin("first.data");
    let expected = BTreeSet::from([OsString::from("first.data")]);
    check_inventory(&temp.0, &expected).unwrap();
    let extra = temp.pin("extra.data");
    assert!(check_inventory(&temp.0, &expected).is_err());
    std::fs::remove_file(extra.path).unwrap();
    std::fs::remove_file(temp.0.join("first.data")).unwrap();
    assert!(check_inventory(&temp.0, &expected).is_err());
}

#[test]
fn link_guard_rejects_replaced_original_even_with_identical_bytes() {
    let temp = Temp::new();
    let target = temp.pin("source.data");
    let origin_id = regular(&target).unwrap();
    let path = temp.0.join("link.data");
    std::os::unix::fs::symlink(&target.path, &path).unwrap();
    let link_id = FileId::of(&std::fs::symlink_metadata(&path).unwrap());
    check_link(&path, &target, link_id, origin_id).unwrap();
    std::fs::rename(&target.path, temp.0.join("retired-source.data")).unwrap();
    let replacement = temp.pin("source.data");
    assert_eq!(replacement.sha256, target.sha256);
    assert!(check_link(&path, &target, link_id, origin_id).is_err());
}
