//! Generality + soundness coverage for the datatype-valued match-result
//! tester/selector distribution fix (see `match_encode::bind_datatype_match_result`).
//!
//! Under the native-`Sort::Datatype` migration, ay resolves a selector/tester only
//! on a *syntactic* constructor argument (or a datatype *variable* via the
//! reconstruction lemma) — NOT on an `ite(...)` tree of constructor leaves. A
//! symbolic `match` returning a datatype therefore left the result's selectors
//! under-constrained, so a closure-result `Option`/`Result`/user-enum value could
//! be picked inconsistent with the taken arm's constructor body.
//!
//! These tests prove the fix generalizes across datatype-valued closure-result
//! shapes (not just `Option::and_then`) and that it only adds *sound* constraints:
//! a deliberately-wrong body still counterexamples.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::ir::TrustVcType;

/// GENERALITY 1 — different result datatype (`Result`, not `Option`) with an
/// *arithmetic* Ok-carrier built from the symbolic scrutinee's payload. Mirrors
/// the `and_then` shape but proves the distribution works for any datatype:
/// `opt.ok_or_else(...)` lowers to `match opt { Some(x) => Ok(x), None => Err(99) }`,
/// and the per-branch structural equality requires `Ok_0(res)` to resolve to `x`.
#[test]
fn ok_or_else_symbolic_result_carrier_resolves_per_branch() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("opt", TrustVcType::parse_or_opaque("Option<u32>"));
    ctx.push_obligation(ProofObligation::assert(
        "ok_or_else_result_branches",
        "{ let res: Result<u32, u32> = opt.ok_or_else(|| -> u32 { 99u32 }); \
           match opt { Some(x) => res == Ok::<u32, u32>(x), None => res == Err::<u32, u32>(99u32) } }",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Result-valued symbolic match result must resolve its Ok/Err selector per branch",
    );
}

/// GENERALITY 2 — a hand-written `match` returning `Option<u32>` whose Some arm
/// wraps a *non-trivial* arithmetic expression over the scrutinee payload
/// (`Some(x * 2 + 3)`). The outer match field-projects the result; the Some-arm
/// selector `Some_0(res)` must equal `x*2+3`. This exercises the distribution
/// directly through the IR match encoder rather than a specific combinator.
#[test]
fn symbolic_match_option_arith_body_selector_resolves() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("opt", TrustVcType::parse_or_opaque("Option<u32>"));
    // Constrain the payload so the inner arithmetic cannot overflow u32.
    ctx.push_obligation(ProofObligation::assume(
        "payload_small",
        "match opt { Some(x) => x < 1000u32, None => true }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "symbolic_match_arith_branches",
        "{ let res: Option<u32> = match opt { Some(x) => Some(x * 2u32 + 3u32), None => Option::<u32>::None }; \
           match opt { Some(x) => res == Some(x * 2u32 + 3u32), None => res == Option::<u32>::None } }",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "hand-written symbolic Option match with arithmetic body must resolve per branch",
    );
}

/// GENERALITY 3 — `Option::and_then` whose closure returns `None` in one path
/// and `Some(..)` in another via a nested `if`, so the closure result is itself
/// an `ite` tree of constructor leaves *inside* the outer match `ite`. The fix
/// must distribute selectors/testers through the *nested* ite tree, not just a
/// single level.
#[test]
fn and_then_nested_ite_closure_result_resolves() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("opt", TrustVcType::parse_or_opaque("Option<u32>"));
    ctx.push_obligation(ProofObligation::assume(
        "payload_small",
        "match opt { Some(x) => x < 1000u32, None => true }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "and_then_nested_ite_branches",
        "{ let res: Option<u32> = opt.and_then(|x: u32| -> Option<u32> { \
              if x < 10u32 { Option::<u32>::None } else { Some(x + 1u32) } }); \
           match opt { \
              Some(x) => res == (if x < 10u32 { Option::<u32>::None } else { Some(x + 1u32) }), \
              None => res == Option::<u32>::None } }",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "and_then with a nested if-else closure result must resolve through the nested ite tree",
    );
}

/// SOUNDNESS — a deliberately WRONG `and_then` body (`Some(x + 2)`) asserted
/// equal to `Some(x + 1)` MUST counterexample. The distribution fix only adds
/// sound equalities; it can never make a false obligation verify.
#[test]
fn and_then_wrong_body_still_counterexamples() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("opt", TrustVcType::parse_or_opaque("Option<u32>"));
    ctx.push_obligation(ProofObligation::assume(
        "payload_small",
        "match opt { Some(x) => x < 1000u32, None => true }",
    ));
    // Closure actually computes x + 2, but the contract claims x + 1.
    ctx.push_obligation(ProofObligation::assert(
        "and_then_wrong_body",
        "{ let res: Option<u32> = opt.and_then(|x: u32| -> Option<u32> { Some(x + 2u32) }); \
           match opt { Some(x) => res == Some(x + 1u32), None => res == Option::<u32>::None } }",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "a wrong and_then body must still counterexample — the fix adds only sound constraints",
    );
}

/// SOUNDNESS 2 — wrong *constructor* in the Some branch (`None` body asserted to
/// equal `Some(x+1)`) must counterexample. Guards against the distribution
/// collapsing a tester incorrectly.
#[test]
fn and_then_wrong_constructor_still_counterexamples() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("opt", TrustVcType::parse_or_opaque("Option<u32>"));
    ctx.push_obligation(ProofObligation::assume(
        "payload_small",
        "match opt { Some(x) => x < 1000u32, None => true }",
    ));
    // Closure always returns None, but the contract claims Some(x + 1) on the Some branch.
    ctx.push_obligation(ProofObligation::assert(
        "and_then_wrong_ctor",
        "{ let res: Option<u32> = opt.and_then(|_x: u32| -> Option<u32> { Option::<u32>::None }); \
           match opt { Some(x) => res == Some(x + 1u32), None => res == Option::<u32>::None } }",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "a wrong constructor in the Some branch must still counterexample",
    );
}
