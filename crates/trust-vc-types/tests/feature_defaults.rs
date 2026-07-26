// trust-vc-types Cargo feature regression tests
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::fs;
use std::path::{Path, PathBuf};

fn load_manifest_at(manifest_path: &Path) -> String {
    fs::read_to_string(manifest_path)
        .unwrap_or_else(|err| panic!("failed to read {}: {err}", manifest_path.display()))
}

fn load_current_manifest() -> String {
    let manifest_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("Cargo.toml");
    load_manifest_at(&manifest_path)
}

fn load_workspace_crate_manifest(crate_name: &str) -> String {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let workspace_root = manifest_dir
        .parent()
        .and_then(Path::parent)
        .expect("crate directory should be under <workspace>/crates/<name>")
        .to_path_buf();
    let manifest_path = workspace_root
        .join("crates")
        .join(crate_name)
        .join("Cargo.toml");
    load_manifest_at(&manifest_path)
}

fn feature_value(manifest: &str, key: &str) -> Option<String> {
    let mut in_features_section = false;

    for raw_line in manifest.lines() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }

        if line.starts_with('[') && line.ends_with(']') {
            in_features_section = line == "[features]";
            continue;
        }

        if !in_features_section {
            continue;
        }

        if let Some((lhs, rhs)) = line.split_once('=') {
            if lhs.trim() == key {
                return Some(rhs.trim().to_owned());
            }
        }
    }

    None
}

#[test]
fn default_feature_is_empty() {
    let manifest = load_current_manifest();
    assert_eq!(feature_value(&manifest, "default").as_deref(), Some("[]"));
}

#[test]
fn trust_mc_feature_is_opt_in_and_forwarded_to_trust_vc() {
    let manifest = load_current_manifest();
    assert_eq!(
        feature_value(&manifest, "trust_mc").as_deref(),
        Some("[\"trust-vc/trust_mc\"]")
    );
}

#[test]
fn default_features_are_consistent_across_trust_vc_crates() {
    for crate_name in ["trust-vc", "trust-vc-core", "trust-vc-types"] {
        let manifest = load_workspace_crate_manifest(crate_name);
        assert_eq!(
            feature_value(&manifest, "default").as_deref(),
            Some("[]"),
            "crate {crate_name} should keep trust_mc opt-in by default"
        );
    }
}
