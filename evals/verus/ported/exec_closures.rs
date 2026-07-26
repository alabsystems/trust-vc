// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Focused partial executable TrustVc evidence for upstream Verus
// `source/rust_verify_test/tests/exec_closures.rs`.
//
// This file intentionally keeps the upstream row as an unsupported gap. The
// verified and counterexample cases express closure-like pre/post reasoning
// through ordinary TrustVc function contracts and helper calls, covering the
// simplest 0/1/2-argument executable closure obligations plus call-site
// requires/ensures, mutable assignment of call results, and sub-expression call
// shapes. Direct source-level executable closure calls still fail closed below.
// Full upstream parity still requires closure-local requires/ensures metadata,
// `f.requires`/`f.ensures` reflection, direct closure calls, closure capture,
// Fn/FnOnce/FnMut parameter passing, loops, old-state interaction, mode and
// capture diagnostics, and exact diagnostic parity.

#![allow(dead_code)]

pub type ExecClosuresRsExpectedCase = (&'static str, &'static str, &'static str, usize);
pub type ExecClosuresRsExpectedErrorPatterns = (&'static str, &'static [&'static str]);
pub type ExecClosuresRsFailClosedErrorPatterns = ExecClosuresRsExpectedErrorPatterns;

pub const EXEC_CLOSURES_RS_EXPECTED_CASES: &[ExecClosuresRsExpectedCase] = &[
    (
        "exec_closure_zero_arg_contract_verified",
        "",
        "verified",
        1,
    ),
    (
        "exec_closure_one_arg_contract_verified",
        "basic_test",
        "verified",
        1,
    ),
    (
        "exec_closure_two_arg_contract_verified",
        "basic_test_2_args",
        "verified",
        1,
    ),
    (
        "exec_closure_helper_application_verified",
        "",
        "verified",
        1,
    ),
    (
        "exec_closure_call_assignment_contract_verified",
        "",
        "verified",
        1,
    ),
    (
        "exec_closure_call_as_sub_expression_contract_verified",
        "",
        "verified",
        1,
    ),
    (
        "exec_closure_zero_arg_bad_ensures_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "exec_closure_one_arg_bad_ensures_counterexample",
        "test_ensures_fail",
        "counterexample",
        1,
    ),
    (
        "exec_closure_one_arg_bad_ensures_return_stmt_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "exec_closure_two_arg_bad_ensures_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "exec_closure_two_arg_bad_ensures_return_stmt_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "exec_closure_helper_bad_call_requires_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "exec_closure_helper_bad_call_ensures_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "exec_closure_call_assignment_false_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "exec_closure_call_as_sub_expression_requires_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "exec_closure_direct_application_currently_errors",
        "basic_test",
        "verified",
        1,
    ),
    (
        "exec_closure_zero_arg_direct_application_currently_errors",
        "",
        "verified",
        1,
    ),
    (
        "exec_closure_requires_reflection_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "exec_closure_ensures_reflection_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "exec_closure_contract_macro_direct_application_currently_errors",
        "basic_test",
        "verified",
        1,
    ),
    (
        "exec_closure_fn_trait_bound_application_is_deterministic_verified",
        "",
        "verified",
        1,
    ),
    (
        "exec_closure_fn_trait_bound_callee_ensures_verified",
        "",
        "verified",
        1,
    ),
    (
        "exec_closure_fn_trait_bound_pass_site_roundtrip_verified",
        "",
        "verified",
        1,
    ),
    (
        "exec_closure_fn_trait_bound_pass_site_requires_violation_counterexample",
        "",
        "counterexample",
        1,
    ),
    (
        "exec_closure_capture_application_currently_errors",
        "",
        "error",
        0,
    ),
    (
        "exec_closure_mutable_capture_application_currently_errors",
        "",
        "error",
        0,
    ),
];

pub const EXEC_CLOSURES_RS_EXPECTED_ERROR_PATTERNS: &[ExecClosuresRsExpectedErrorPatterns] = &[
    (
        "exec_closure_requires_reflection_currently_errors",
        &["requires"],
    ),
    (
        "exec_closure_ensures_reflection_currently_errors",
        &["ensures"],
    ),
    (
        "exec_closure_capture_application_currently_errors",
        &["unknown return type for function 'f'"],
    ),
    (
        "exec_closure_mutable_capture_application_currently_errors",
        &["unknown return type for function 'f'"],
    ),
];

pub const EXEC_CLOSURES_RS_FAIL_CLOSED_ERROR_PATTERNS: &[ExecClosuresRsFailClosedErrorPatterns] =
    EXEC_CLOSURES_RS_EXPECTED_ERROR_PATTERNS;

pub fn exec_closures_rs_expected_cases() -> &'static [ExecClosuresRsExpectedCase] {
    EXEC_CLOSURES_RS_EXPECTED_CASES
}

pub fn exec_closures_rs_expected_error_patterns(
) -> &'static [ExecClosuresRsExpectedErrorPatterns] {
    EXEC_CLOSURES_RS_EXPECTED_ERROR_PATTERNS
}

pub fn exec_closures_rs_fail_closed_error_patterns(
) -> &'static [ExecClosuresRsFailClosedErrorPatterns] {
    EXEC_CLOSURES_RS_FAIL_CLOSED_ERROR_PATTERNS
}

#[trust_vc::contract(
    ensures(z == 7u64),
    returns(z),
)]
fn exec_closure_zero_arg_contract_verified() -> u64 {
    7u64
}

#[trust_vc::contract(
    requires(y == 2u64),
    ensures(z == 2u64),
    returns(z),
)]
fn exec_closure_one_arg_contract_verified(y: u64) -> u64 {
    y
}

#[trust_vc::contract(
    requires(x == y),
    ensures(z == x),
    returns(z),
)]
fn exec_closure_two_arg_contract_verified(x: u64, y: u64) -> u64 {
    y
}

#[trust_vc::contract(
    requires(y == 2u64),
    ensures(z == y),
    returns(z),
)]
fn exec_closure_call_contract_helper(y: u64) -> u64 {
    y
}

#[trust_vc::ensures(true)]
fn exec_closure_helper_application_verified() {
    let observed = exec_closure_call_contract_helper(2u64);
    trust_vc::assert!(observed == 2u64);
}

#[trust_vc::contract(
    requires(input == 5u64 || input == 7u64),
    ensures(result == input),
    returns(result),
)]
fn exec_closure_identity_assignment_helper(input: u64) -> u64 {
    input
}

#[trust_vc::ensures(true)]
fn exec_closure_call_assignment_contract_verified(flag: bool) {
    let mut observed = exec_closure_identity_assignment_helper(5u64);
    trust_vc::assert!(observed == 5u64);

    if flag {
        observed = exec_closure_identity_assignment_helper(7u64);
        trust_vc::assert!(observed == 7u64);
    }
}

#[trust_vc::contract(
    ensures(result == 20u64),
    returns(result),
)]
fn exec_closure_twenty_helper() -> u64 {
    20u64
}

#[trust_vc::requires(input == 20u64)]
fn exec_closure_requires_twenty(input: u64) {
    trust_vc::assert!(input == 20u64);
}

#[trust_vc::requires(input == 21u64)]
fn exec_closure_requires_twenty_one(input: u64) {
    trust_vc::assert!(input == 21u64);
}

#[trust_vc::ensures(true)]
fn exec_closure_call_as_sub_expression_contract_verified() {
    exec_closure_requires_twenty(exec_closure_twenty_helper());
}

#[trust_vc::contract(
    ensures(z == 8u64),
    returns(z),
)]
fn exec_closure_zero_arg_bad_ensures_counterexample() -> u64 {
    7u64
}

#[trust_vc::contract(
    requires(y == 2u64),
    ensures(z == 3u64),
    returns(z),
)]
fn exec_closure_one_arg_bad_ensures_counterexample(y: u64) -> u64 {
    y
}

#[trust_vc::contract(
    requires(y == 2u64),
    ensures(z == 3u64),
    returns(z),
)]
fn exec_closure_one_arg_bad_ensures_return_stmt_counterexample(y: u64) -> u64 {
    return y;
}

#[trust_vc::contract(
    requires(x == y),
    ensures(z == x),
    returns(z),
)]
fn exec_closure_two_arg_bad_ensures_counterexample(x: u64, y: u64) -> u64 {
    0u64
}

#[trust_vc::contract(
    requires(y == 2u64),
    ensures(z == 3u64),
    returns(z),
)]
fn exec_closure_two_arg_bad_ensures_return_stmt_counterexample(x: u64, y: u64) -> u64 {
    return x;
}

#[trust_vc::ensures(true)]
fn exec_closure_helper_bad_call_requires_counterexample() {
    let _ = exec_closure_call_contract_helper(3u64);
}

#[trust_vc::ensures(true)]
fn exec_closure_helper_bad_call_ensures_counterexample() {
    let observed = exec_closure_call_contract_helper(2u64);
    trust_vc::assert!(observed == 3u64);
}

#[trust_vc::ensures(true)]
fn exec_closure_call_assignment_false_counterexample(flag: bool) {
    let mut observed = exec_closure_identity_assignment_helper(5u64);
    trust_vc::assert!(observed == 5u64);

    if flag {
        observed = exec_closure_identity_assignment_helper(7u64);
        trust_vc::assert!(observed == 8u64);
    }
}

#[trust_vc::ensures(true)]
fn exec_closure_call_as_sub_expression_requires_counterexample() {
    exec_closure_requires_twenty_one(exec_closure_twenty_helper());
}

// FLIP (bare-closure inline): a bare capture-free local closure applied by name
// is now INLINED at the call site — `f(2)` models as its body `2`, so the true
// `assert!(f(2) == 2)` VERIFIES (formerly fail-closed "unknown return type for
// function 'f'"). Historical `_currently_errors` case-id retained for stable
// upstream/manifest mapping.
#[trust_vc::ensures(true)]
fn exec_closure_direct_application_currently_errors() {
    let f = |y: u64| -> u64 { y };
    trust_vc::assert!(f(2u64) == 2u64);
}

// FLIP (bare-closure inline): a ZERO-ARG capture-free closure inlines too —
// `f()` models as its body `7`, so `assert!(f() == 7)` VERIFIES.
#[trust_vc::ensures(true)]
fn exec_closure_zero_arg_direct_application_currently_errors() {
    let f = || -> u64 { 7u64 };
    trust_vc::assert!(f() == 7u64);
}

#[trust_vc::ensures(true)]
fn exec_closure_requires_reflection_currently_errors() {
    let f = |y: u64| -> u64 { y };
    trust_vc::assert!(f.requires((2u64,)));
}

#[trust_vc::ensures(true)]
fn exec_closure_ensures_reflection_currently_errors() {
    let f = |y: u64| -> u64 { y };
    trust_vc::assert!(!f.ensures((2u64,), 3u64));
}

#[trust_vc::ensures(true)]
fn exec_closure_contract_macro_direct_application_currently_errors() {
    let f = trust_vc::closure!(
        |y: u64| -> u64
        requires(y == 2u64)
        ensures(|z: u64| z == 2u64)
        y
    );
    trust_vc::assert!(f(2u64) == 2u64);
}

// INCREMENT 1 (Fn-bound closure typing foundation) FLIP: an `F: Fn(u64) -> u64`
// value parameter is typed as a first-class `SpecFn(u64, u64)`, so `f(3)` lowers
// to the opaque, CONGRUENT `spec_fn_apply` UF. `Fn` captures immutably ⇒ it is
// DETERMINISTIC across calls, so equal arguments give the equal result — a SOUND,
// non-tautological property. The result stays otherwise unconstrained (a concrete
// pin like `f(3) == 3` still counterexamples; `FnMut`/`FnOnce` stay fail-closed).
// Formerly a fail-closed "Undefined function: f" error.
#[trust_vc::ensures(true)]
fn exec_closure_fn_trait_bound_application_is_deterministic_verified<F: Fn(u64) -> u64>(f: F) {
    let a = f(3u64);
    let b = f(3u64);
    trust_vc::assert!(a == b);
}

// INCREMENT 2a (Fn-bound closure dispatch, callee-side obligation model): an
// `F: Fn(u64) -> u64` value parameter can now USE the closure's own spec. At the
// call `f(a)` the callee-side seam emits the SOUND conditional assume
// `call_requires%(f, a) ==> call_ensures%(f, a, f(a))` over the OPAQUE reflection
// UFs, binding the real returned `spec_fn_apply(f, a)` term. A callee that
// ESTABLISHES the precondition (`requires f.requires((a,))`, an assumed
// `call_requires%`) can therefore discharge a postcondition written over the
// closure's own ensures (`ensures f.ensures((a,), result)`) — the callee proves
// the VALID CONDITIONAL "IF f.requires(a) THEN f.ensures(a, result)", sound for
// ANY closure satisfying `F: Fn`. The ensures stays OPAQUE (a concrete pin like
// `f(a) == 5` still counterexamples) and a callee that OMITS the requires cannot
// use the ensures (fails closed). See the adversarial suite
// `trust-vc-core/tests/fn_bound_closure_obligation_soundness.rs`.
#[trust_vc::contract(
    requires(f.requires((a,))),
    ensures(f.ensures((a,), result)),
    returns(result),
)]
fn exec_closure_fn_trait_bound_callee_ensures_verified<F: Fn(u64) -> u64>(f: F, a: u64) -> u64 {
    f(a)
}

// INCREMENT 2b (Fn-bound closure dispatch, cross-boundary PASS-SITE linkage): a
// caller passes a concrete `trust_vc::closure!` literal `c` (requires `x < 10`,
// ensures `r == x + 1`) into the reflecting callee above. At the pass site
// `g(c, 5)` the callee's `f.requires((a,))` / `f.ensures((a,), result)` clauses
// substitute to `c.requires((5,))` / `c.ensures((5,), g(c, 5))`, which lower to
// the OPAQUE reflection UFs `call_requires%` / `call_ensures%`. The pass-site
// linkage emits the DEFINITIONAL ground facts tying those UF applications to
// `c`'s own concrete, arg-substituted spec, so the caller PROVES the callee's
// prove-`requires` (from `c`'s `5 < 10`) and USES the callee's assumed `ensures`
// (`c`'s `y == 6`). The linkage fires ONLY for a registered closure literal (a
// re-passed Fn-bound param has no def-side and stays fail-closed), and the
// closure's def-side is independently checked at its `let c = …`. See the
// adversarial suite `trust-vc-core/tests/fn_bound_closure_pass_site_soundness.rs`.
#[trust_vc::ensures(true)]
fn exec_closure_fn_trait_bound_pass_site_roundtrip_verified() {
    let c = trust_vc::closure!(
        |x: u64| -> u64
        requires(x < 10u64)
        ensures(|r: u64| r == x + 1u64)
        x + 1u64
    );
    let y = exec_closure_fn_trait_bound_callee_ensures_verified(c, 5u64);
    trust_vc::assert!(y == 6u64);
}

// INCREMENT 2b requires-violation companion: the same closure `c` (requires
// `x < 10`) is passed with the argument `50`, so the pass-site linkage pins
// `call_requires%(c, (50,)) == (50 < 10) == false`, making the callee's
// prove-`requires` obligation false. A counterexample — the pass-site linkage is
// LOAD-BEARING and does not admit a precondition-violating call.
#[trust_vc::ensures(true)]
fn exec_closure_fn_trait_bound_pass_site_requires_violation_counterexample() {
    let c = trust_vc::closure!(
        |x: u64| -> u64
        requires(x < 10u64)
        ensures(|r: u64| r == x + 1u64)
        x + 1u64
    );
    let y = exec_closure_fn_trait_bound_callee_ensures_verified(c, 50u64);
    trust_vc::assert!(y == 51u64);
}

#[trust_vc::ensures(true)]
fn exec_closure_capture_application_currently_errors() {
    let captured = true;
    let f = |flag: bool| -> bool { flag && captured };
    trust_vc::assert!(f(true));
}

#[trust_vc::ensures(true)]
fn exec_closure_mutable_capture_application_currently_errors() {
    let mut captured = 1u64;
    let mut f = |next: u64| -> u64 {
        captured = next;
        captured
    };
    let observed = f(2u64);
    trust_vc::assert!(observed == 2u64 && captured == 2u64);
}
