// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Executable guards for narrow collection corpus scout ports.
//!
//! These tests intentionally do not claim full Verus collection parity. They
//! prove that the listed upstream-derived slices execute through TrustVc while
//! the global manifest keeps the corresponding source files fail-closed.

use std::path::PathBuf;
use trust_vc_core::{verify_function_from_file, VerifyResult};

fn port_path(file: &str) -> PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join(format!("../../evals/verus/ported/{file}"))
}

#[test]
fn sets_rs_len_positive_and_counterexample_subsets_execute_from_file() {
    let path = port_path("sets.rs");
    let path = path.to_str().expect("sets port path should be UTF-8");

    let result = verify_function_from_file(path, "test_len")
        .unwrap_or_else(|err| panic!("sets.rs test_len should extract: {err}"));
    assert!(
        matches!(result, VerifyResult::Verified),
        "sets.rs test_len should verify, got: {result:?}"
    );

    let result = verify_function_from_file(path, "test_len_fails")
        .unwrap_or_else(|err| panic!("sets.rs test_len_fails should extract: {err}"));
    assert!(
        matches!(result, VerifyResult::Counterexample { .. }),
        "sets.rs test_len_fails should be rejected, got: {result:?}"
    );
}
