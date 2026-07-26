// SPDX-License-Identifier: Apache-2.0
use trust_vc_core::{verify_function_from_file, VerifyResult};
fn fx(n: &str) -> String {
    format!("{}/tests/data/{n}", env!("CARGO_MANIFEST_DIR"))
}
fn v(f: &str) -> Result<VerifyResult, String> {
    verify_function_from_file(&fx("if_let_desugar_probe.rs"), f).map_err(|e| e.to_string())
}
#[test]
fn if_let_desugar_positive_verifies() {
    let r = v("if_let_expr_verifies");
    eprintln!("[POS] {r:?}");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "positive if-let should verify: {r:?}"
    );
}
#[test]
fn if_let_desugar_never_assumes_match() {
    let r = v("if_let_expr_must_not_assume_match");
    eprintln!("[CRUX] {r:?}");
    assert!(
        !matches!(r, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: if-let assumed the match succeeds"
    );
}
#[test]
fn if_let_desugar_both_arms_verify() {
    let r = v("if_let_expr_both_arms_verify");
    eprintln!("[BOTH] {r:?}");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "both-arms postcondition should verify: {r:?}"
    );
}
#[test]
fn if_let_chain_stays_fail_closed() {
    let r = v("if_let_chain_must_stay_blocked");
    eprintln!("[CHAIN] {r:?}");
    assert!(
        !matches!(r, Ok(VerifyResult::Verified)),
        "let-chain must not be desugared/verified: {r:?}"
    );
}
