// SPDX-License-Identifier: Apache-2.0
use trust_vc_core::{verify_function_from_file, VerifyResult};
fn fx(n: &str) -> String {
    format!("{}/tests/data/{n}", env!("CARGO_MANIFEST_DIR"))
}
fn nv(f: &str) {
    let v = verify_function_from_file(&fx("match_encoder_probe.rs"), f);
    eprintln!("[T] {f} => {v:?}");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: {f}"
    );
}
#[test]
fn guard_not_ignored() {
    nv("guard_must_not_be_ignored");
}
#[test]
fn non_exhaustive() {
    nv("non_exhaustive_must_not_assume");
}
#[test]
fn overlapping() {
    nv("overlapping_first_match_wins");
}
#[test]
fn guard_pos() {
    let v = verify_function_from_file(&fx("match_encoder_probe.rs"), "guard_positive");
    eprintln!("[C] guard_positive => {v:?}");
}
