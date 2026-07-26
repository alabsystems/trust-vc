// SPDX-License-Identifier: Apache-2.0
use trust_vc_core::{verify_function_from_file, VerifyResult};
fn fx(n: &str) -> String {
    format!("{}/tests/data/{n}", env!("CARGO_MANIFEST_DIR"))
}
#[test]
fn if_let_assertions_must_not_be_dropped() {
    for f in [
        "if_let_then_assert_false_must_not_verify",
        "if_let_else_reachable_assert_false_must_not_verify",
    ] {
        let v = verify_function_from_file(&fx("if_let_soundness_probe.rs"), f);
        eprintln!("[IFLET] {f} => {v:?}");
        assert!(
            !matches!(v, Ok(VerifyResult::Verified)),
            "FALSE-VERIFY: if-let assertion dropped in {f}"
        );
    }
}
