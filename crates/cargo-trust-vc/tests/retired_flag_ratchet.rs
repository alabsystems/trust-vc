// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::path::PathBuf;

/// Helper-binary compiles must use the compiler's sole live verification
/// selector. Keep this source-level ratchet separate from the helper tests so
/// it can diagnose a resurrected spelling before any child compiler runs.
#[test]
fn integration_helpers_do_not_resurrect_retired_verification_selector() {
    let crate_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let tests_dir = crate_dir.join("tests");
    let retired = ["-Zno-", "trust-verify"].concat();
    let mut offenders = Vec::new();

    for entry in std::fs::read_dir(&tests_dir).expect("read cargo-trust-vc tests directory") {
        let path = entry.expect("read cargo-trust-vc test entry").path();
        if path.extension().and_then(std::ffi::OsStr::to_str) != Some("rs") {
            continue;
        }
        let source = std::fs::read_to_string(&path).expect("read cargo-trust-vc test source");
        if source.contains(&retired) {
            offenders.push(path);
        }
    }

    assert!(
        offenders.is_empty(),
        "retired compiler verification selector returned in helper sources: {offenders:?}"
    );

    let evidence_source = std::fs::read_to_string(crate_dir.join("src/evidence.rs"))
        .expect("read evidence runner source");
    assert!(
        !evidence_source.contains(&retired),
        "evidence-runner toolchain guidance resurrected the retired selector"
    );
}
