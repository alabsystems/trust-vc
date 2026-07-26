// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Verus-parity diagnostics for the mode/spec-context misuse family
//! (upstream basic.rs / modes.rs) plus the destructuring-assignment
//! fail-close.
//!
//! Upstream witnesses (messages must be contained VERBATIM in the diagnostic;
//! the evidence gate matches expected_error_patterns by substring):
//!   * basic.rs `test_init_spec_param_fail_2`: `spec fn test1(x: u64) { x = 5; }`
//!     — "assignment is not allowed inside pure context"
//!     (also modes.rs `spec_let_decl_init_fail`: `let x: u64; x = 23;` in spec).
//!   * basic.rs `test_init_spec_param_fail_1`: `proof fn test1(x: u64) { x = 5; }`
//!     — "variable `x` is not marked mutable".
//!   * basic.rs `test_mut_param_spec_fail`: `spec fn f(mut x: i32) -> i32;`
//!     — "mut argument not allowed for spec functions".
//!   * basic.rs `test_mut_self_disallowed`: exec `fn test(mut self)` —
//!     "The verifier does not yet support the following Rust feature: mut self".
//!   * basic.rs `destructuring_assignment_unsupported`: `(a, b) = (1, 2);` —
//!     "The verifier does not yet support the following Rust feature:
//!     destructuring assignment". trust-vc previously DROPPED the assignment
//!     silently (stale values: `(a, b) = (1, 2); assert!(a == 0)` verified).
//!
//! Every rule is general (fires on the language shape, never on names) and
//! reject-only. The negative controls below pin the legal twins: mut params in
//! exec/proof fns, exec assignments and deferred init, `let`-destructuring
//! bindings, `&mut self`, shadowed params, and sibling (non-target) `mut self`
//! builder methods.

use std::fs;
use std::path::Path;
use trust_vc_core::{TrustVcResult, VerifyResult};

fn verify(code: &str, name: &str) -> TrustVcResult<VerifyResult> {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let dir = Path::new("target/mode_spec_context_diagnostics");
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
// 1. "assignment is not allowed inside pure context" (spec-mode body)
// ---------------------------------------------------------------------------

#[test]
fn spec_param_assignment_is_rejected_with_pure_context_message() {
    // Upstream basic.rs test_init_spec_param_fail_2 (verbatim shape).
    let code = r#"
#[trust_vc::spec]
#[trust_vc::ensures(true)]
fn test1(x: u64) {
    x = 5;
}
"#;
    let r = verify(code, "test1");
    assert!(
        err_message(&r).contains("assignment is not allowed inside pure context"),
        "spec param assignment must be rejected with the upstream message, got {r:?}"
    );
}

#[test]
fn spec_deferred_init_assignment_is_rejected_with_pure_context_message() {
    // Upstream modes.rs spec_let_decl_init_fail (Rust-valid deferred init).
    let code = r#"
#[trust_vc::spec]
#[trust_vc::ensures(true)]
fn test1() -> u64 {
    let x: u64;
    x = 23;
    x
}
"#;
    let r = verify(code, "test1");
    assert!(
        err_message(&r).contains("assignment is not allowed inside pure context"),
        "spec deferred-init assignment must be rejected, got {r:?}"
    );
}

#[test]
fn spec_let_mut_local_assignment_is_rejected_with_pure_context_message() {
    // Assignment to a `let mut` LOCAL in a spec body also errors upstream.
    let code = r#"
#[trust_vc::spec]
#[trust_vc::ensures(true)]
fn test1() -> u64 {
    let mut x: u64 = 1;
    x = 23;
    x
}
"#;
    let r = verify(code, "test1");
    assert!(
        err_message(&r).contains("assignment is not allowed inside pure context"),
        "spec let-mut assignment must be rejected, got {r:?}"
    );
}

#[test]
fn spec_compound_assignment_is_rejected_with_pure_context_message() {
    let code = r#"
#[trust_vc::spec]
#[trust_vc::ensures(true)]
fn test1() -> u64 {
    let mut x: u64 = 1;
    x += 2;
    x
}
"#;
    let r = verify(code, "test1");
    assert!(
        err_message(&r).contains("assignment is not allowed inside pure context"),
        "spec compound assignment must be rejected, got {r:?}"
    );
}

#[test]
fn exec_deferred_init_assignment_stays_accepted() {
    // Upstream basic.rs test_decl_init_let_pass: exec deferred init is legal.
    let code = r#"
#[trust_vc::ensures(true)]
fn test1() {
    let x: u64;
    x = 23;
    let _ = x;
}
"#;
    let r = verify(code, "test1");
    assert!(
        !err_message(&r).contains("pure context"),
        "exec deferred init must not hit the pure-context rule, got {r:?}"
    );
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "exec deferred init must keep verifying, got {r:?}"
    );
}

#[test]
fn exec_mut_param_assignment_stays_verified() {
    let code = r#"
#[trust_vc::ensures(result == 6)]
fn bump(mut x: u64) -> u64 {
    x = 6;
    x
}
"#;
    let r = verify(code, "bump");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "exec mut-param assignment must keep verifying, got {r:?}"
    );
}

#[test]
fn spec_body_without_assignment_is_unaffected() {
    let code = r#"
#[trust_vc::spec]
#[trust_vc::ensures(true)]
fn le(x: u64, y: u64) -> bool {
    x <= y
}
"#;
    let r = verify(code, "le");
    assert!(
        !err_message(&r).contains("pure context"),
        "comparison-only spec body must not fire the pure-context rule, got {r:?}"
    );
}

// ---------------------------------------------------------------------------
// 2. "variable `x` is not marked mutable" (proof-mode non-mut param)
// ---------------------------------------------------------------------------

#[test]
fn proof_non_mut_param_assignment_is_rejected_with_not_marked_mutable() {
    // Upstream basic.rs test_init_spec_param_fail_1 (verbatim shape).
    let code = r#"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn test1(x: u64) {
    x = 5;
}
"#;
    let r = verify(code, "test1");
    assert!(
        err_message(&r).contains("variable `x` is not marked mutable"),
        "proof non-mut-param assignment must be rejected with the upstream message, got {r:?}"
    );
}

#[test]
fn proof_non_mut_param_compound_assignment_is_rejected() {
    let code = r#"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn test1(y: u64) {
    y += 1;
}
"#;
    let r = verify(code, "test1");
    assert!(
        err_message(&r).contains("variable `y` is not marked mutable"),
        "proof non-mut-param compound assignment must be rejected (interpolated name), got {r:?}"
    );
}

#[test]
fn proof_mut_param_compound_assignment_stays_accepted() {
    // Upstream basic.rs test3: `proof fn test3(mut x: int) { x += 1; }` is legal.
    let code = r#"
use trust_vc_types::int;
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn test3(mut x: int) {
    x += 1;
}
"#;
    let r = verify(code, "test3");
    assert!(
        !err_message(&r).contains("not marked mutable"),
        "proof mut-param assignment is legal and must not fire, got {r:?}"
    );
}

#[test]
fn proof_let_mut_local_assignment_stays_accepted() {
    let code = r#"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn locals() {
    let mut observed: u64 = 1;
    observed = 2;
    trust_vc::assert!(observed == 2);
}
"#;
    let r = verify(code, "locals");
    assert!(
        !err_message(&r).contains("not marked mutable"),
        "proof let-mut local assignment is legal and must not fire, got {r:?}"
    );
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "proof let-mut local assignment must keep verifying, got {r:?}"
    );
}

#[test]
fn proof_shadowed_param_assignment_does_not_fire() {
    // `let mut x = x;` rebinds the name: the later assignment targets the
    // local, not the parameter.
    let code = r#"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn shadowed(x: u64) {
    let mut x = x;
    x = 5;
    trust_vc::assert!(x == 5);
}
"#;
    let r = verify(code, "shadowed");
    assert!(
        !err_message(&r).contains("not marked mutable"),
        "shadowed param assignment must not fire the non-mut-param rule, got {r:?}"
    );
}

#[test]
fn exec_non_mut_param_assignment_is_not_flagged_by_proof_rule() {
    // Rust itself rejects this (rust-error channel, not a VIR diagnostic);
    // the proof-mode rule must not fire on exec functions.
    let code = r#"
#[trust_vc::ensures(true)]
fn test1(x: u64) {
    x = 5;
    let _ = x;
}
"#;
    let r = verify(code, "test1");
    assert!(
        !err_message(&r).contains("not marked mutable"),
        "exec fn must not hit the proof-mode non-mut-param rule, got {r:?}"
    );
}

// ---------------------------------------------------------------------------
// 3. "mut argument not allowed for spec functions"
// ---------------------------------------------------------------------------

#[test]
fn spec_mut_param_is_rejected_with_upstream_message() {
    // Upstream basic.rs test_mut_param_spec_fail (body added: syn free fns
    // need one; the rule is signature-only so the witness is equivalent).
    let code = r#"
#[trust_vc::spec]
#[trust_vc::ensures(true)]
fn f(mut x: i32) -> i32 {
    x
}
"#;
    let r = verify(code, "f");
    assert!(
        err_message(&r).contains("mut argument not allowed for spec functions"),
        "spec mut param must be rejected with the upstream message, got {r:?}"
    );
}

#[test]
fn exec_and_proof_mut_params_are_not_flagged_by_spec_rule() {
    let exec_code = r#"
#[trust_vc::ensures(result >= 1)]
fn f(mut x: u64) -> u64 {
    x = 1;
    x
}
"#;
    let r = verify(exec_code, "f");
    assert!(
        !err_message(&r).contains("mut argument not allowed"),
        "exec mut param is legal, got {r:?}"
    );

    let proof_code = r#"
#[trust_vc::proof]
#[trust_vc::ensures(true)]
fn g(mut x: u64) {
    x = 1;
    let _ = x;
}
"#;
    let r = verify(proof_code, "g");
    assert!(
        !err_message(&r).contains("mut argument not allowed"),
        "proof mut param is legal, got {r:?}"
    );
}

// ---------------------------------------------------------------------------
// 4. "The verifier does not yet support the following Rust feature: mut self"
// ---------------------------------------------------------------------------

#[test]
fn by_value_mut_self_is_rejected_with_upstream_message() {
    // Upstream basic.rs test_mut_self_disallowed (verbatim shape).
    let code = r#"
struct T {}

impl T {
    #[trust_vc::ensures(true)]
    fn test(mut self) {
        self = T {};
    }
}
"#;
    let r = verify(code, "test");
    assert!(
        err_message(&r)
            .contains("The verifier does not yet support the following Rust feature: mut self"),
        "by-value mut self must be rejected with the upstream message, got {r:?}"
    );
}

#[test]
fn ref_mut_self_is_not_flagged_as_mut_self() {
    // `&mut self` is ImplicitSelfKind::RefMut upstream — legal.
    let code = r#"
struct C {
    v: u64,
}

impl C {
    #[trust_vc::ensures(true)]
    fn bump(&mut self) {}
}
"#;
    let r = verify(code, "bump");
    assert!(
        !err_message(&r).contains("mut self"),
        "&mut self must not hit the mut-self rule, got {r:?}"
    );
}

#[test]
fn sibling_mut_self_builder_does_not_reject_the_target_fn() {
    // The rule applies only to the function under extraction: an unannotated
    // `mut self` builder elsewhere in the file must not affect the target.
    let code = r#"
struct B {
    v: u64,
}

impl B {
    fn with_v(mut self, v: u64) -> Self {
        self.v = v;
        self
    }
}

#[trust_vc::ensures(result == 3)]
fn target() -> u64 {
    3
}
"#;
    let r = verify(code, "target");
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "sibling mut-self builder must not reject the extraction target, got {r:?}"
    );
}

// ---------------------------------------------------------------------------
// 5. destructuring assignment fail-close
// ---------------------------------------------------------------------------

#[test]
fn tuple_destructuring_assignment_is_rejected_with_upstream_message() {
    // Upstream basic.rs destructuring_assignment_unsupported (verbatim shape).
    let code = r#"
#[trust_vc::ensures(true)]
fn test() {
    let mut a = 0;
    let mut b = 0;
    (a, b) = (1, 2);
    let _ = (a, b);
}
"#;
    let r = verify(code, "test");
    assert!(
        err_message(&r).contains(
            "The verifier does not yet support the following Rust feature: destructuring assignment"
        ),
        "tuple destructuring assignment must be rejected with the upstream message, got {r:?}"
    );
}

#[test]
fn destructuring_assignment_no_longer_verifies_stale_values() {
    // FAITHFULNESS/SOUNDNESS witness: this exact program VERIFIED before the
    // fix (the assignment was silently dropped, so `a == 0` held in the model).
    let code = r#"
#[trust_vc::ensures(true)]
fn test() {
    let mut a = 0;
    let mut b = 0;
    (a, b) = (1, 2);
    trust_vc::assert!(a == 0);
}
"#;
    let r = verify(code, "test");
    assert!(
        !matches!(r, Ok(VerifyResult::Verified)),
        "stale-value destructuring program must no longer verify, got {r:?}"
    );
    assert!(
        err_message(&r).contains("destructuring assignment"),
        "stale-value destructuring program must be rejected, got {r:?}"
    );
}

#[test]
fn array_destructuring_assignment_is_rejected() {
    let code = r#"
#[trust_vc::ensures(true)]
fn test() {
    let mut a = 0;
    let mut b = 0;
    [a, b] = [1, 2];
    let _ = (a, b);
}
"#;
    let r = verify(code, "test");
    assert!(
        err_message(&r).contains("destructuring assignment"),
        "array destructuring assignment must be rejected, got {r:?}"
    );
}

#[test]
fn let_tuple_destructuring_binding_keeps_working() {
    // `let (a, b) = ..` is a BINDING (Stmt::Local), not a destructuring
    // assignment — it must keep its existing behavior.
    let code = r#"
#[trust_vc::ensures(true)]
fn test() {
    let (a, b) = (1u64, 2u64);
    trust_vc::assert!(a == 1);
    trust_vc::assert!(b == 2);
}
"#;
    let r = verify(code, "test");
    assert!(
        !err_message(&r).contains("destructuring assignment"),
        "let-destructuring must not be rejected, got {r:?}"
    );
    assert!(
        matches!(r, Ok(VerifyResult::Verified)),
        "let-destructuring must keep verifying, got {r:?}"
    );
}

#[test]
fn underscore_discard_assignment_is_not_flagged() {
    // `_ = expr` is an Expr::Infer LHS — deliberately left on its existing
    // path (unwitnessed upstream), must not hit the destructuring rule.
    let code = r#"
#[trust_vc::ensures(true)]
fn test() {
    let a = 1u64;
    _ = a;
}
"#;
    let r = verify(code, "test");
    assert!(
        !err_message(&r).contains("destructuring assignment"),
        "`_ = expr` must not hit the destructuring rule, got {r:?}"
    );
}
