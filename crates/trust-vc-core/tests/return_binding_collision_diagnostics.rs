// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Verus-parity diagnostics for the return-value-binding/parameter name
//! collision family (diagnostic-parity foundation slice 2, FAMILY A).
//!
//! Upstream the check is PURELY SYNTACTIC and fires at macro expansion
//! (`builtin_macros/src/syntax.rs` `check_return_idents` /
//! `check_verus_return_idents`): every identifier bound by the return
//! pattern is intersected with every identifier bound by a typed-parameter
//! pattern (nested patterns included; the `self` receiver skipped), and any
//! overlap is a compile error. Upstream witnesses (message must be contained
//! VERBATIM — the evidence gate matches expected_error_patterns by
//! substring):
//!   * basic.rs `test_ensures_ret_val_collision`:
//!     `fn f(k: u32, n: u32) -> ((_, n): (u32, u32)) ensures n <= k`
//!     — "return value name collides with a parameter name".
//!   * basic.rs `test_fail_return_value_parameter_same_name`:
//!     `fn foo(x: u64) -> (x: bool) ensures x || !x` — same message.
//!
//! The rule is general (keyed on the language shape, never on names) and
//! reject-only: both witness shapes already errored in trust-vc with an
//! internal "Variable 'x' already declared" message, so no legality changes —
//! only the message gains upstream parity. Negative controls pin the legal
//! twins: non-colliding bindings, the implicit `result` variable (upstream
//! has NO implicit binder, so a param literally named `result` must not get
//! the collision message), and the shared-reference returns-CONDITION reading
//! (legal Verus `returns x` clause).

use std::fs;
use std::path::Path;
use trust_vc_core::{TrustVcResult, VerifyResult};

const COLLISION_MSG: &str = "return value name collides with a parameter name";

fn verify(code: &str, name: &str) -> TrustVcResult<VerifyResult> {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let dir = Path::new("target/return_binding_collision_diagnostics");
    fs::create_dir_all(dir).unwrap();
    let mut h = DefaultHasher::new();
    code.hash(&mut h);
    let f = dir.join(format!("{name}_{:016x}.rs", h.finish()));
    fs::write(&f, code).unwrap();
    trust_vc_core::verify_function_from_file(f.to_str().unwrap(), name)
}

/// The error message returned (empty string if the call did not error).
fn err_message(r: &TrustVcResult<VerifyResult>) -> String {
    match r {
        Err(e) => e.to_string(),
        Ok(VerifyResult::Error { message }) => message.clone(),
        _ => String::new(),
    }
}

// ---------------------------------------------------------------------------
// Positive cases: colliding bindings get the upstream message
// ---------------------------------------------------------------------------

#[test]
fn returns_attr_binding_colliding_with_param_is_rejected() {
    // Upstream basic.rs test_fail_return_value_parameter_same_name:
    // `fn foo(x: u64) -> (x: bool) ensures x || !x` (attr spelling).
    let code = r#"
#[trust_vc::ensures(x || !x)]
#[trust_vc::returns(x)]
fn foo(x: u64) -> bool {
    x > 10
}
"#;
    let r = verify(code, "foo");
    assert!(
        err_message(&r).contains(COLLISION_MSG),
        "colliding #[returns] binding must be rejected with the upstream message, got {r:?}"
    );
}

#[test]
fn contract_returns_clause_colliding_with_param_is_rejected() {
    // Same upstream witness, contract-clause spelling.
    let code = r#"
#[trust_vc::contract(ensures(x || !x), returns(x))]
fn foo(x: u64) -> bool {
    x > 10
}
"#;
    let r = verify(code, "foo");
    assert!(
        err_message(&r).contains(COLLISION_MSG),
        "colliding contract returns() clause must be rejected with the upstream message, got {r:?}"
    );
}

#[test]
fn tuple_returns_binding_colliding_with_param_is_rejected() {
    // Upstream basic.rs test_ensures_ret_val_collision:
    // `fn f(k: u32, n: u32) -> ((_, n): (u32, u32)) ensures n <= k`.
    // The collision scan runs BEFORE the tuple-unsupported rejection so the
    // upstream message wins.
    let code = r#"
#[trust_vc::ensures(true)]
#[trust_vc::returns((a, n))]
fn f(k: u32, n: u32) -> (u32, u32) {
    (42, k / 2)
}
"#;
    let r = verify(code, "f");
    assert!(
        err_message(&r).contains(COLLISION_MSG),
        "colliding tuple #[returns] binding must be rejected with the upstream message, got {r:?}"
    );
}

#[test]
fn returns_binding_colliding_with_nested_pattern_param_is_rejected() {
    // Upstream collects idents from typed-param patterns NESTED included
    // (check_return_idents walks the full pattern).
    let code = r#"
#[trust_vc::ensures(true)]
#[trust_vc::returns(b)]
fn g((a, b): (u32, u32)) -> u32 {
    a
}
"#;
    let r = verify(code, "g");
    assert!(
        err_message(&r).contains(COLLISION_MSG),
        "binding colliding with a nested-pattern param ident must be rejected, got {r:?}"
    );
}

// ---------------------------------------------------------------------------
// Negative controls: legal twins stay accepted / keep their existing path
// ---------------------------------------------------------------------------

#[test]
fn non_colliding_returns_binding_stays_verified() {
    let code = r#"
#[trust_vc::ensures(r == x)]
#[trust_vc::returns(r)]
fn id(x: u64) -> u64 {
    x
}
"#;
    let r = verify(code, "id");
    assert!(
        !err_message(&r).contains(COLLISION_MSG),
        "non-colliding binding must not fire the collision rule, got {r:?}"
    );
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "non-colliding returns binding must keep verifying, got {r:?}"
    );
}

#[test]
fn non_colliding_tuple_returns_keeps_tuple_unsupported_message() {
    // Without a collision the tuple shape keeps its existing (fail-closed)
    // tuple-unsupported rejection — the collision message must NOT appear.
    let code = r#"
#[trust_vc::ensures(true)]
#[trust_vc::returns((a, b))]
fn f(k: u32, n: u32) -> (u32, u32) {
    (1, 2)
}
"#;
    let r = verify(code, "f");
    let msg = err_message(&r);
    assert!(
        !msg.contains(COLLISION_MSG),
        "non-colliding tuple binding must not fire the collision rule, got {r:?}"
    );
    assert!(
        msg.contains("tuple #[returns] bindings are not supported"),
        "non-colliding tuple binding must keep the tuple-unsupported rejection, got {r:?}"
    );
}

#[test]
fn param_named_result_without_returns_binding_is_not_flagged() {
    // Upstream has NO implicit return binder: a parameter literally named
    // `result` (with no explicit returns binding) never carries the
    // collision message. trust-vc's internal `result` variable is a surface
    // difference; whatever its existing behavior, the collision message must
    // not leak onto it.
    let code = r#"
#[trust_vc::ensures(true)]
fn f(result: u64) -> u64 {
    result
}
"#;
    let r = verify(code, "f");
    assert!(
        !err_message(&r).contains(COLLISION_MSG),
        "implicit `result` variable must not get the explicit-collision message, got {r:?}"
    );
}

#[test]
fn shared_reference_returns_condition_is_not_flagged() {
    // `#[returns(x)]` where `x` is a shared-reference param and the return
    // type is a shared reference takes the returns-CONDITION path (legal
    // Verus `returns x` postcondition clause) — NOT a binding; the collision
    // rule must not fire.
    let code = r#"
#[trust_vc::ensures(true)]
#[trust_vc::returns(x)]
fn f(x: &u64) -> &u64 {
    x
}
"#;
    let r = verify(code, "f");
    assert!(
        !err_message(&r).contains(COLLISION_MSG),
        "shared-reference returns-condition must not fire the collision rule, got {r:?}"
    );
}
