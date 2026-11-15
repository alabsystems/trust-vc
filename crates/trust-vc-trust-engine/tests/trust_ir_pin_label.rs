// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `TRUST_IR_BODY_TRUST_IR_PIN`, written into every body-lane binding and so
//! into every certificate's `unit_id`, names the trust-ir this workspace
//! locks, and the wire and bundle versions of the trust-ir it links; the
//! fixture READMEs name the same revision.
//!
//! The label is the pin the lane is measured against: a superproject that
//! patches in another trust-ir links that one, and its own IR cohort check
//! compares the two.

use std::path::{Path, PathBuf};

use trust_vc_trust_engine::TRUST_IR_BODY_TRUST_IR_PIN;

fn workspace_file(relative: &str) -> (PathBuf, String) {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(relative);
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    (path, text)
}

/// The `version` and git `rev` of the one `trust-ir` package in `lock`.
fn locked_trust_ir(lock: &str) -> (String, String) {
    let mut found = Vec::new();
    for package in lock.split("[[package]]").skip(1) {
        let field = |key: &str| {
            package.lines().find_map(|line| {
                line.strip_prefix(&format!("{key} = \""))
                    .and_then(|rest| rest.strip_suffix('"'))
                    .map(str::to_string)
            })
        };
        if field("name").as_deref() != Some("trust-ir") {
            continue;
        }
        let version = field("version").expect("a locked package has a version");
        let source = field("source").expect("trust-ir is a git dependency");
        let rev = source
            .rsplit_once('#')
            .map(|(_, rev)| rev.to_string())
            .expect("a git source names its commit after '#'");
        found.push((version, rev));
    }
    assert_eq!(
        found.len(),
        1,
        "one trust-ir package in Cargo.lock: {found:?}"
    );
    found.remove(0)
}

#[test]
fn the_trust_ir_pin_label_names_the_locked_and_linked_trust_ir() {
    let (_, lock) = workspace_file("../../Cargo.lock");
    let (version, rev) = locked_trust_ir(&lock);
    assert_eq!(rev.len(), 40, "a full commit id: {rev}");
    let expected = format!(
        "trust-ir {version}@{rev} bin v{}",
        trust_ir::binary::VERSION
    );
    assert_eq!(
        TRUST_IR_BODY_TRUST_IR_PIN, expected,
        "update TRUST_IR_BODY_TRUST_IR_PIN with the pin move"
    );

    let (path, body) = workspace_file("fixtures/trust_ir_body/README.md");
    let pin = format!("trust-ir `{version}@{rev}`");
    let versions = format!(
        "(binary format v{}, bundle schema v{})",
        trust_ir::binary::VERSION,
        trust_ir::request::NATIVE_VERIFICATION_BUNDLE_SCHEMA_VERSION
    );
    assert!(
        body.contains(&pin) && body.contains(&versions),
        "{} names {pin} {versions}",
        path.display()
    );
    let (path, native) = workspace_file("fixtures/trust_ir_native/README.md");
    let pin = format!("rev `{rev}`");
    let schema = format!(
        "bundle schema {}",
        trust_ir::request::NATIVE_VERIFICATION_BUNDLE_SCHEMA_VERSION
    );
    assert!(
        native.contains(&pin) && native.contains(&schema),
        "{} names {pin}, {schema}",
        path.display()
    );
}
