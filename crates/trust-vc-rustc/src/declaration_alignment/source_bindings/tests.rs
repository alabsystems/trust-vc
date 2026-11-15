// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::sync::atomic::{AtomicU64, Ordering};

use serde_json::json;

use super::*;

static NEXT: AtomicU64 = AtomicU64::new(0);

struct Temp(PathBuf);

impl Temp {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "trust-vc-source-bindings-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&path).expect("create new owned test directory");
        fs::create_dir(path.join("source")).unwrap();
        Self(path)
    }

    fn source(&self) -> PathBuf {
        self.0.join("source")
    }

    fn pinned(&self, name: &str, bytes: &[u8]) -> PinnedFile {
        let path = self.0.join(name);
        fs::write(&path, bytes).unwrap();
        PinnedFile {
            path,
            sha256: digest(bytes),
        }
    }

    fn manifest(&self, bytes: &[u8]) -> PinnedFile {
        fs::write(self.source().join("x.rs"), bytes).unwrap();
        self.pinned(
            "manifest.json",
            &serde_json::to_vec(&json!({
                "git_commit": "original-source", "files_sha256": {"x.rs": hex(digest(bytes))},
                "symlink_targets": {},
            }))
            .unwrap(),
        )
    }
}

impl Drop for Temp {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).expect("remove owned test directory");
    }
}

fn hex(digest: Digest) -> String {
    digest.iter().map(|b| format!("{b:02x}")).collect()
}

fn coordinates(temp: &Temp, bytes: &[u8], range: (u32, u32)) -> ObservedAnchor {
    ObservedAnchor {
        local_path: temp.source().join("x.rs").to_str().unwrap().into(),
        compiler_source_hash: format!("sha256={}", hex(digest(bytes))),
        original_file_len: u32::try_from(bytes.len()).unwrap(),
        bytes: range,
    }
}

#[test]
fn exact_manifest_bytes_supply_original_ranges_and_canonical_aliases() {
    let temp = Temp::new();
    let bytes = b"fn declared() {}\n";
    let manifest = temp.manifest(bytes);
    let sources = Sources::load(&temp.source(), manifest, None).unwrap();
    let mut anchor = coordinates(&temp, bytes, (3, 11));
    let bound = sources.anchor(&anchor).unwrap();
    assert_eq!(bound.relative_file, "x.rs");
    assert_eq!(bound.bytes, (3, 11));
    assert_eq!(bound.file_sha256, digest(bytes));
    anchor.local_path = temp
        .source()
        .canonicalize()
        .unwrap()
        .join("x.rs")
        .to_str()
        .unwrap()
        .into();
    assert_eq!(sources.anchor(&anchor).unwrap(), bound);
    sources.revalidate().unwrap();
}

#[test]
fn structured_anchors_and_input_identity_preserve_the_checked_bytes() {
    let temp = Temp::new();
    let bytes = "aλb\n".as_bytes();
    let manifest = temp.manifest(bytes);
    let expected_manifest = manifest.sha256;
    let sources = Sources::load(&temp.source(), manifest, None).unwrap();
    assert_eq!(
        sources.identity(),
        SourceIdentity {
            manifest_sha256: expected_manifest,
            compatibility: SourceCompatibility::Unmodified,
        }
    );
    let bound = sources.anchor(&coordinates(&temp, bytes, (1, 3))).unwrap();
    sources.validate_anchor(&bound).unwrap();
    for mutation in 0..5 {
        let mut changed = bound.clone();
        match mutation {
            0 => changed.file_sha256 = [0; 32],
            1 => changed.original_file_len += 1,
            2 => changed.bytes = (1, 2),
            3 => changed.bytes = (3, 30),
            _ => changed.relative_file = "../x.rs".into(),
        }
        assert!(sources.validate_anchor(&changed).is_err());
    }
}

#[test]
fn changed_extra_and_missing_source_files_fail_the_whole_graph() {
    for mutation in 0..3 {
        let temp = Temp::new();
        let manifest = temp.manifest(b"original");
        match mutation {
            0 => fs::write(temp.source().join("x.rs"), b"different").unwrap(),
            1 => fs::write(temp.source().join("extra.rs"), b"extra").unwrap(),
            _ => fs::remove_file(temp.source().join("x.rs")).unwrap(),
        }
        assert!(Sources::load(&temp.source(), manifest, None).is_err());
    }
}

#[test]
fn changed_disk_bytes_do_not_change_snapshot_or_pass_revalidation() {
    let temp = Temp::new();
    let bytes = b"original";
    let sources = Sources::load(&temp.source(), temp.manifest(bytes), None).unwrap();
    let anchor = coordinates(&temp, bytes, (0, 8));
    let before = sources.anchor(&anchor).unwrap();
    fs::write(temp.source().join("x.rs"), b"modified").unwrap();
    assert_eq!(sources.anchor(&anchor).unwrap(), before);
    assert!(sources.revalidate().is_err());
}

#[test]
fn foreign_hash_length_range_and_unicode_boundaries_stay_unbound() {
    let temp = Temp::new();
    let bytes = "aλb\n".as_bytes();
    let sources = Sources::load(&temp.source(), temp.manifest(bytes), None).unwrap();
    let valid = coordinates(&temp, bytes, (1, 3));
    assert!(sources.anchor(&valid).is_ok());
    for mutation in 0..6 {
        let mut anchor = valid.clone();
        match mutation {
            0 => anchor.compiler_source_hash = format!("sha256={}", "0".repeat(64)),
            1 => anchor.original_file_len += 1,
            2 => anchor.bytes = (2, 3),
            3 => anchor.bytes = (1, 99),
            4 => anchor.local_path = temp.0.join("unapproved.rs").to_str().unwrap().into(),
            _ => anchor.local_path = temp.source().join("../x.rs").to_str().unwrap().into(),
        }
        assert!(sources.anchor(&anchor).is_err());
    }
}

#[test]
fn manifest_path_traversal_is_rejected() {
    let temp = Temp::new();
    let manifest = temp.pinned(
        "manifest.json",
        &serde_json::to_vec(&json!({
            "files_sha256": {"../outside.rs": hex(digest(b"not read"))}, "symlink_targets": {},
        }))
        .unwrap(),
    );
    assert!(Sources::load(&temp.source(), manifest, None).is_err());
}

#[cfg(unix)]
#[test]
fn source_symlinks_do_not_read_an_unapproved_target() {
    let temp = Temp::new();
    let manifest = temp.manifest(b"original");
    fs::remove_file(temp.source().join("x.rs")).unwrap();
    std::os::unix::fs::symlink(
        temp.0.join("nonexistent-outside"),
        temp.source().join("x.rs"),
    )
    .unwrap();
    assert!(Sources::load(&temp.source(), manifest, None).is_err());
}

#[cfg(unix)]
#[test]
fn retargeting_the_approved_root_cannot_revalidate_a_different_graph() {
    let temp = Temp::new();
    let manifest = temp.manifest(b"original");
    let alias = temp.0.join("approved-root");
    std::os::unix::fs::symlink(temp.source(), &alias).unwrap();
    let sources = Sources::load(&alias, manifest, None).unwrap();
    sources.revalidate().unwrap();
    let other = temp.0.join("different-source");
    fs::create_dir(&other).unwrap();
    fs::write(other.join("x.rs"), b"different").unwrap();
    fs::remove_file(&alias).unwrap();
    std::os::unix::fs::symlink(other, alias).unwrap();
    assert!(sources.revalidate().is_err());
}

#[test]
fn absent_compatibility_base_fields_are_not_equal_source_identities() {
    for empty_strings in [false, true] {
        let temp = Temp::new();
        let manifest = temp.pinned(
            "manifest.json",
            &serde_json::to_vec(&json!({
                "git_commit": if empty_strings { json!("") } else { Value::Null },
                "files_sha256": {"x.rs": hex(digest(b"original"))}, "symlink_targets": {},
            }))
            .unwrap(),
        );
        fs::write(temp.source().join("x.rs"), b"patched").unwrap();
        let patch = temp.pinned("compat.patch", b"reviewed patch");
        let recipe = temp.pinned("compat.json", &serde_json::to_vec(&json!({
            "schema": "trust-vc.vstd-source-compat@1",
            "base_upstream_commit": if empty_strings { json!("") } else { Value::Null },
            "patch": "compat.patch", "patch_sha256": hex(patch.sha256), "affected_file": "x.rs",
            "original_file_sha256": hex(digest(b"original")), "patched_file_sha256": hex(digest(b"patched")),
        })).unwrap());
        assert!(Sources::load(
            &temp.source(),
            manifest,
            Some(CompatibilityInput { recipe, patch })
        )
        .is_err());
    }
}

#[test]
fn reviewed_compatibility_view_retains_original_and_patched_identity() {
    let temp = Temp::new();
    let original = b"original";
    let patched = b"patched";
    let manifest = temp.manifest(original);
    fs::write(temp.source().join("x.rs"), patched).unwrap();
    assert!(Sources::load(&temp.source(), manifest.clone(), None).is_err());
    let patch = temp.pinned("compat.patch", b"the exact reviewed patch bytes");
    let recipe = temp.pinned("compat.json", &serde_json::to_vec(&json!({
        "schema": "trust-vc.vstd-source-compat@1", "base_upstream_commit": "original-source",
        "patch": "compat.patch", "patch_sha256": hex(patch.sha256), "affected_file": "x.rs",
        "original_file_sha256": hex(digest(original)), "patched_file_sha256": hex(digest(patched)),
    })).unwrap());
    let sources = Sources::load(
        &temp.source(),
        manifest.clone(),
        Some(CompatibilityInput {
            recipe: recipe.clone(),
            patch: patch.clone(),
        }),
    )
    .unwrap();
    assert_eq!(
        sources.identity(),
        SourceIdentity {
            manifest_sha256: manifest.sha256,
            compatibility: SourceCompatibility::Applied {
                recipe_sha256: recipe.sha256,
                patch_sha256: patch.sha256,
            },
        }
    );
    assert_eq!(
        sources
            .anchor(&coordinates(&temp, patched, (0, 7)))
            .unwrap()
            .file_sha256,
        digest(patched)
    );
    fs::write(&patch.path, b"different patch").unwrap();
    assert!(sources.revalidate().is_err());
    assert!(Sources::load(
        &temp.source(),
        manifest,
        Some(CompatibilityInput { recipe, patch })
    )
    .is_err());
}

#[test]
fn metadata_bindings_require_exact_native_selection_and_preserve_changes() {
    let temp = Temp::new();
    // These are byte-binding fixtures, not claims of genuine compiler metadata.
    let file = temp.pinned("library.rmeta", b"selected metadata bytes");
    let metadata = Metadata::load([MetadataInput {
        stable_crate_id: 7,
        svh: 9,
        file: file.clone(),
    }])
    .unwrap();
    assert_eq!(metadata.selected(7, 9, &file.path).unwrap(), file.sha256);
    assert_eq!(metadata.digests(), BTreeSet::from([file.sha256]));
    assert_eq!(metadata.crate_ids(), BTreeSet::from([7]));
    assert!(metadata.selected(8, 9, &file.path).is_err());
    assert!(metadata.selected(7, 10, &file.path).is_err());
    assert!(metadata.selected(7, 9, &temp.0.join("unapproved")).is_err());
    metadata.revalidate().unwrap();
    fs::write(&file.path, b"changed metadata bytes").unwrap();
    assert!(metadata.revalidate().is_err());
}

#[test]
fn duplicate_native_metadata_ids_and_aliases_are_rejected() {
    let temp = Temp::new();
    let file = temp.pinned("library.rmeta", b"selected");
    let other = temp.pinned("other.rmeta", b"other");
    assert!(Metadata::load([
        MetadataInput {
            stable_crate_id: 7,
            svh: 9,
            file: file.clone()
        },
        MetadataInput {
            stable_crate_id: 7,
            svh: 10,
            file: other
        },
    ])
    .is_err());
    let alias = PinnedFile {
        path: file.path.canonicalize().unwrap(),
        sha256: file.sha256,
    };
    assert!(Metadata::load([
        MetadataInput {
            stable_crate_id: 7,
            svh: 9,
            file
        },
        MetadataInput {
            stable_crate_id: 8,
            svh: 9,
            file: alias
        },
    ])
    .is_err());
}

#[cfg(feature = "rustc")]
#[test]
fn native_md5_source_hash_uses_the_compilers_real_algorithm() {
    let temp = Temp::new();
    let bytes = b"abc";
    let sources = Sources::load(&temp.source(), temp.manifest(bytes), None).unwrap();
    let mut anchor = coordinates(&temp, bytes, (0, 3));
    anchor.compiler_source_hash = "md5=900150983cd24fb0d6963f7d28e17f72".into();
    assert!(sources.anchor(&anchor).is_ok());
}

// These are real filesystem byte-binding controls, not compiler artifacts or
// native-context/import capabilities. The original native client pair remains
// the discriminator for actual CStore collection and declaration admission.
#[cfg(unix)]
#[test]
fn native_selection_retains_only_its_captured_alias_and_canonical_target() {
    let temp = Temp::new();
    let file = temp.pinned("original.data", b"ordinary selection bytes");
    let canonical = file.path.canonicalize().unwrap();
    let alias = temp.0.join("selected.data");
    let other_alias = temp.0.join("unobserved.data");
    std::os::unix::fs::symlink(&canonical, &alias).unwrap();
    std::os::unix::fs::symlink(&canonical, &other_alias).unwrap();
    let metadata = Metadata::load_native_selections([(
        MetadataInput {
            stable_crate_id: 7,
            svh: 9,
            file: PinnedFile {
                path: alias.clone(),
                sha256: file.sha256,
            },
        },
        canonical.clone(),
    )])
    .unwrap();
    assert_eq!(metadata.selected(7, 9, &alias).unwrap(), file.sha256);
    assert_eq!(metadata.selected(7, 9, &canonical).unwrap(), file.sha256);
    assert!(metadata.selected(7, 9, &other_alias).is_err());
    assert!(metadata.selected(8, 9, &alias).is_err());
    assert!(metadata.selected(7, 10, &alias).is_err());
    metadata.revalidate().unwrap();
    // A rejected path is never canonicalized, even if it is a symlink loop.
    fs::remove_file(&other_alias).unwrap();
    std::os::unix::fs::symlink(&other_alias, &other_alias).unwrap();
    assert!(metadata.selected(7, 9, &other_alias).is_err());
}

#[cfg(unix)]
#[test]
fn native_selection_rejects_same_byte_retargeting_before_binding() {
    let temp = Temp::new();
    let file = temp.pinned("approved.data", b"same ordinary bytes");
    let other = temp.pinned("unapproved.data", b"same ordinary bytes");
    let approved = file.path.canonicalize().unwrap();
    let alias = temp.0.join("selected.data");
    std::os::unix::fs::symlink(other.path.canonicalize().unwrap(), &alias).unwrap();
    assert_eq!(file.sha256, other.sha256);
    assert!(Metadata::load_native_selections([(
        MetadataInput {
            stable_crate_id: 7,
            svh: 9,
            file: PinnedFile {
                path: alias,
                sha256: file.sha256
            },
        },
        approved
    )])
    .is_err());
}

#[cfg(unix)]
#[test]
fn native_selection_revalidation_refuses_a_stale_same_byte_alias_target() {
    let temp = Temp::new();
    let file = temp.pinned("approved.data", b"same ordinary bytes");
    let other = temp.pinned("unapproved.data", b"same ordinary bytes");
    let approved = file.path.canonicalize().unwrap();
    let alias = temp.0.join("selected.data");
    std::os::unix::fs::symlink(&approved, &alias).unwrap();
    let metadata = Metadata::load_native_selections([(
        MetadataInput {
            stable_crate_id: 7,
            svh: 9,
            file: PinnedFile {
                path: alias.clone(),
                sha256: file.sha256,
            },
        },
        approved,
    )])
    .unwrap();
    metadata.revalidate().unwrap();
    fs::remove_file(&alias).unwrap();
    std::os::unix::fs::symlink(other.path.canonicalize().unwrap(), &alias).unwrap();
    assert_eq!(file.sha256, other.sha256);
    assert!(metadata.revalidate().is_err());
}
