// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use trust_vc_core::{verify_function_from_file, VerifyResult};
fn fx(n: &str) -> String {
    format!("{}/tests/data/{n}", env!("CARGO_MANIFEST_DIR"))
}
#[test]
fn reflexive_neq_not_verified() {
    let v = verify_function_from_file(
        &fx("datatype_self_neq_probe.rs"),
        "reflexive_datatype_neq_under_hyp_must_not_verify",
    );
    eprintln!("[T] {v:?}");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: reflexive a!=a"
    );
}
#[test]
fn true_neq_still_verifies() {
    let v = verify_function_from_file(
        &fx("datatype_self_neq_probe.rs"),
        "true_datatype_neq_under_hyp_verifies",
    );
    eprintln!("[C] {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "control should verify: {v:?}"
    );
}
