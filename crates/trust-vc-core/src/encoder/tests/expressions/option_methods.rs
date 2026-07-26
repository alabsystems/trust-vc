//! Option method expression encoding tests.

use super::*;
use crate::ir::TrustVcType;

#[test]
fn option_ok_or_else_some_verifies_ok_payload() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "option_ok_or_else_some_payload",
        "{ let opt: Option<u32> = Some(42u32); opt.ok_or_else(|| 0u32) } == Ok::<u32, u32>(42u32)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Option::ok_or_else on Some should produce Ok");
}

#[test]
fn option_ok_or_else_none_verifies_err_payload() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "option_ok_or_else_none_payload",
        "{ let opt: Option<u32> = None; opt.ok_or_else(|| -> u32 { 99u32 }) } == Err::<u32, u32>(99u32)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Option::ok_or_else on None should produce Err");
}

#[test]
fn option_ok_or_else_verifies_contract_equivalent_branches() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("opt", TrustVcType::parse_or_opaque("Option<u32>"));
    ctx.push_obligation(ProofObligation::assert(
        "option_ok_or_else_contract_equiv",
        "{ let res: Result<u32, u32> = opt.ok_or_else(|| -> u32 { 99u32 }); \
           match opt { Some(x) => res == Ok::<u32, u32>(x), None => res == Err::<u32, u32>(99u32) } }",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Option::ok_or_else should encode Ok/Err branch semantics for contract-style closures",
    );
}

#[test]
fn option_and_then_some_verifies_closure_result() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "option_and_then_some_payload",
        "{ let opt: Option<u32> = Some(2u32); opt.and_then(|x: u32| -> Option<u32> { Some(x + 1u32) }) } == Some(3u32)",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Option::and_then on Some should use closure body");
}

#[test]
fn option_and_then_none_verifies_none_result() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "option_and_then_none_payload",
        "{ let opt: Option<u32> = None; opt.and_then(|x: u32| -> Option<u32> { Some(x + 1u32) }) } == Option::<u32>::None",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Option::and_then on None should stay None");
}

#[test]
fn option_and_then_verifies_contract_equivalent_branches() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("opt", TrustVcType::parse_or_opaque("Option<u32>"));
    ctx.push_obligation(ProofObligation::assume(
        "and_then_closure_requires",
        "match opt { Some(x) => x < 1000u32, None => true }",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "option_and_then_contract_equiv",
        "{ let res: Option<u32> = opt.and_then(|x: u32| -> Option<u32> { Some(x + 1u32) }); \
           match opt { Some(x) => res == Some(x + 1u32), None => res == Option::<u32>::None } }",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Option::and_then should encode closure requires/ensures equivalent branch semantics",
    );
}

#[test]
fn option_unwrap_or_else_none_verifies_fallback() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "option_unwrap_or_else_none_payload",
        "{ let opt: Option<u32> = None; opt.unwrap_or_else(|| -> u32 { 99u32 }) } == 99u32",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Option::unwrap_or_else on None should use fallback closure",
    );
}

#[test]
fn option_unwrap_or_else_verifies_contract_equivalent_branches() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("opt", TrustVcType::parse_or_opaque("Option<u32>"));
    ctx.push_obligation(ProofObligation::assert(
        "option_unwrap_or_else_contract_equiv",
        "{ let val: u32 = opt.unwrap_or_else(|| -> u32 { 99u32 }); \
           match opt { Some(x) => val == x, None => val == 99u32 } }",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Option::unwrap_or_else should encode value/fallback branch semantics for contract-style closures",
    );
}
