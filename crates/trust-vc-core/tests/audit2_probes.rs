// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Regression probes from soundness-audit round 2 (overflow surface). Both were
//! confirmed false-verifies (arith safety obligation dropped) and are now fixed:
//! return-position overflow (collect_value_position_arith_exprs Expr::Return arm)
//! and match-arm-guard div0 (visit_expr_match guard instrumentation). Targets MUST
//! fail closed; controls MUST verify.
use trust_vc_core::{verify_function_from_file, VerifyResult};
fn fx(n: &str) -> String {
    format!("{}/tests/data/{n}", env!("CARGO_MANIFEST_DIR"))
}
fn nv(file: &str, f: &str) {
    let v = verify_function_from_file(&fx(file), f);
    eprintln!("[T] {f} => {v:?}");
    assert!(
        !matches!(v, Ok(VerifyResult::Verified)),
        "FALSE-VERIFY: {f}"
    );
}
fn ok(file: &str, f: &str) {
    let v = verify_function_from_file(&fx(file), f);
    eprintln!("[C] {f} => {v:?}");
    assert!(
        matches!(v, Ok(VerifyResult::Verified)),
        "control should verify: {f} => {v:?}"
    );
}
#[test]
fn return_position_overflow_checked() {
    nv("arith_return_overflow_probe.rs", "overflow_in_return");
    ok("arith_return_overflow_probe.rs", "bounded_mul_tail");
}
#[test]
fn match_guard_div0_checked() {
    nv("arith_match_guard_probe.rs", "div0_in_match_guard");
    ok("arith_match_guard_probe.rs", "safe_div_tail");
}
