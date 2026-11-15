// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
// Fixtures for the Phase C part 2 DIRECT-APPLICATION adversarial soundness suite
// (`closure_direct_application_soundness.rs`). Verified via
// verify_function_from_file, cache-OFF.
//
// DIRECT APPLICATION `f(args..)` of a KNOWN LOCAL `trust_vc::closure!` literal
// (any arity, over modelable value sorts) lowers to the OPAQUE, DISJOINT
// `spec_fn_apply` UF the `.call` method path already uses. At the call site the
// extraction seam PROVES `f.requires(args..)` (an obligation) and ASSUMES
// `f.ensures(args.., f(args..))` binding the REAL returned term. The assumed
// ensures is ONLY ever the def-side-CHECKED written clause: a lying closure's
// independent def-side obligation COUNTEREXAMPLES and poisons the whole function,
// so the call-site assume can never rescue an unchecked ensures. The zero-arg and
// two-arg applications (D9) were deferred while the seam was unary-only; H6
// widened it to every arity, because a deferred LOWERING error never
// fires on an unused result and the n-ary requires went unproven.

// ---------------------------------------------------------------------------
// D1 ACCEPTANCE / flip: unary closure!, requires satisfied, ensures genuinely
// assumable, assert reads the identical `spec_fn_apply` term. MUST VERIFY.
// (This is the exact shape the old reflection probe7 pinned as "still deferred".)
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn d1_direct_application_verified() {
    let f = trust_vc::closure!(
        |y: u64| -> u64
        requires(y == 2u64)
        ensures(|z: u64| z == y)
        y
    );
    let t = f(2u64);
    trust_vc::assert!(t == 2u64);
}

// ---------------------------------------------------------------------------
// D1b ACCEPTANCE, assert-EMBEDDED application: `assert!(f(2) == 2)` with the
// call directly inside the assert condition (no `let` temporary). Exercises the
// assert/assume-condition seam. MUST VERIFY. (This is the exact shape of the
// flipped corpus row `exec_closure_contract_macro_direct_application`.)
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn d1b_assert_embedded_application_verified() {
    let f = trust_vc::closure!(
        |y: u64| -> u64
        requires(y == 2u64)
        ensures(|z: u64| z == 2u64)
        y
    );
    trust_vc::assert!(f(2u64) == 2u64);
}

// ---------------------------------------------------------------------------
// D2b CARDINAL, assert-EMBEDDED lying body: same lie as D2 but with the call
// directly inside the assert. The def-side COUNTEREXAMPLES and poisons the
// parent regardless of the call-site assume. MUST NOT verify.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn d2b_assert_embedded_unchecked_ensures_cx() {
    let f = trust_vc::closure!(
        |y: u64| -> u64
        requires(true)
        ensures(|z: u64| z == 100u64)
        y
    );
    trust_vc::assert!(f(3u64) == 100u64);
}

// ---------------------------------------------------------------------------
// D2 CARDINAL unchecked-ensures-at-call-site (lying body): body `y` does NOT
// establish `ensures(z == 100)`, so the co-emitted def-side obligation
// COUNTEREXAMPLES and poisons the parent; the call-site assume `f(3) == 100`
// NEVER rescues it. A `Verified` here is the cardinal false-verify. MUST NOT
// verify.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn d2_cardinal_unchecked_ensures_cx() {
    let f = trust_vc::closure!(
        |y: u64| -> u64
        requires(true)
        ensures(|z: u64| z == 100u64)
        y
    );
    let t = f(3u64);
    trust_vc::assert!(t == 100u64);
}

// ---------------------------------------------------------------------------
// D3 consume-ensures counterexample (valid body, over-strong claim / mutation-
// sensitive): def-side-VALID (`ensures(z == 2)`, body `y` under `requires(y ==
// 2)`), but the assume pins ONLY `f(2) == 2`, so the perturbed assert `t == 3`
// COUNTEREXAMPLES (upstream test_call_ensures_fail). MUST NOT verify.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn d3_consume_ensures_cx() {
    let f = trust_vc::closure!(
        |y: u64| -> u64
        requires(y == 2u64)
        ensures(|z: u64| z == 2u64)
        y
    );
    let t = f(2u64);
    trust_vc::assert!(t == 3u64);
}

// ---------------------------------------------------------------------------
// D4 bad-call-requires: the argument `3` violates `requires(y == 2)`, so the
// call-site prove-requires obligation `3 == 2` COUNTEREXAMPLES (upstream
// test_call_requires_fail). MUST NOT verify.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn d4_bad_call_requires_cx() {
    let f = trust_vc::closure!(
        |y: u64| -> u64
        requires(y == 2u64)
        ensures(|z: u64| z == y)
        y
    );
    let _t = f(3u64);
}

// ---------------------------------------------------------------------------
// D5 vacuous-requires still blocks at the call site. The def-side is a
// VacuousTruth-PASS (`false => E`), but the call-site prove-requires asserts
// `false` and COUNTEREXAMPLES; the ensures is never reached. MUST NOT verify.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn d5_vacuous_requires_blocks_cx() {
    let f = trust_vc::closure!(
        |y: u64| -> u64
        requires(false)
        ensures(|z: u64| z == 0u64)
        0u64
    );
    let t = f(0u64);
    trust_vc::assert!(t == 0u64);
}

// ---------------------------------------------------------------------------
// D6 capture stays fail-closed. The capture guard fires BEFORE any reflection
// registration, so `f` is never SpecFn-typed, the relaxed lowering guard never
// fires, and extraction fails closed. MUST NOT verify.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn d6_capture_stays_fail_closed() {
    let c = 5u64;
    let f = trust_vc::closure!(
        |y: u64| -> u64
        requires(true)
        ensures(|z: u64| z == c)
        c
    );
    let t = f(0u64);
    trust_vc::assert!(t == 5u64);
}

// ---------------------------------------------------------------------------
// D7 bare-literal application stays fail-closed. A bare Rust closure is never
// declare_var_typed, so `env.lookup("f") == None`, the relaxed guard never
// fires, and lowering fails closed. Proves the relaxation is scoped to
// registered closure! literals only. MUST NOT verify.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn d7_bare_literal_stays_fail_closed() {
    let f = |y: u64| -> u64 { y };
    let t = f(2u64);
    trust_vc::assert!(t == 2u64);
}

// ---------------------------------------------------------------------------
// D8 loop-body drop discipline. The assume-ensures is DROPPED inside a loop
// body (via `add_helper_contract_obligations`), so the in-loop assert cannot be
// discharged (no verified-by-leak). MUST NOT verify. A `Verified` here means the
// call-ensures assume leaked out of the loop (a soundness break).
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn d8_loop_body_drop_fails_closed() {
    let mut i = 0u64;
    while i < 3u64 {
        let f = trust_vc::closure!(
            |y: u64| -> u64
            requires(y == 2u64)
            ensures(|z: u64| z == y)
            y
        );
        let t = f(2u64);
        trust_vc::assert!(t == 2u64);
        i = i + 1u64;
    }
}

// ---------------------------------------------------------------------------
// D9a zero-arg application (H6: the seam is no longer unary-only). A TRUE claim
// over the def-side-checked ensures. MUST VERIFY. Before H6 it was deferred
// (not verified) — and a zero-arg application whose result went unused proved
// no requires at all.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn d9a_zero_arg_application_verified() {
    let f = trust_vc::closure!(
        || -> u64
        requires(true)
        ensures(|z: u64| z == 7u64)
        7u64
    );
    let t = f();
    trust_vc::assert!(t == 7u64);
}

// D9a liar twin: the assumed ensures pins `t == 7`, so `t == 8` counterexamples.
#[trust_vc::ensures(true)]
fn d9a_zero_arg_liar_cx() {
    let f = trust_vc::closure!(
        || -> u64
        requires(true)
        ensures(|z: u64| z == 7u64)
        7u64
    );
    let t = f();
    trust_vc::assert!(t == 8u64);
}

// D9a requires twin: the zero-arg call-site requires is PROVEN (and fails).
#[trust_vc::ensures(true)]
fn d9a_zero_arg_requires_false_cx() {
    let f = trust_vc::closure!(
        || -> u64
        requires(false)
        ensures(|z: u64| z == 7u64)
        7u64
    );
    let _t = f();
}

// ---------------------------------------------------------------------------
// D9b two-arg application (H6). A TRUE claim. MUST VERIFY.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn d9b_two_arg_application_verified() {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u64
        requires(true)
        ensures(|z: u64| z == 7u64)
        7u64
    );
    let t = f(1u64, 2u64);
    trust_vc::assert!(t == 7u64);
}

// D9b liar twin: `t == 8` counterexamples.
#[trust_vc::ensures(true)]
fn d9b_two_arg_liar_cx() {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u64
        requires(true)
        ensures(|z: u64| z == 7u64)
        7u64
    );
    let t = f(1u64, 2u64);
    trust_vc::assert!(t == 8u64);
}

// D9b requires twin: `requires(a == b)` at `(1, 2)` counterexamples on the
// call-site prove-requires obligation.
#[trust_vc::ensures(true)]
fn d9b_two_arg_bad_requires_cx() {
    let f = trust_vc::closure!(
        |a: u64, b: u64| -> u64
        requires(a == b)
        ensures(|z: u64| z == 7u64)
        7u64
    );
    let _t = f(1u64, 2u64);
}

// ---------------------------------------------------------------------------
// D10 unmodelable-param deferred. A parameter type with no modelable SMT sort
// (`ProofPerm`) registers NO reflection contract and its def-side rejects the
// unmodelable parameter, so `f(..)` cannot resolve. MUST NOT verify.
// ---------------------------------------------------------------------------
#[trust_vc::ensures(true)]
fn d10_unmodelable_param_deferred() {
    let f = trust_vc::closure!(
        |y: ProofPerm| -> u64
        requires(true)
        ensures(|z: u64| z == 0u64)
        0u64
    );
    let t = f(0u64);
    trust_vc::assert!(t == 0u64);
}
