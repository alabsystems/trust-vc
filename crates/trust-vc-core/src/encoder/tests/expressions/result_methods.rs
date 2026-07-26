//! Result method expression encoding tests.

use super::*;
use crate::ir::{StructDef, TrustVcType};
use crate::ir_expr::TrustVcExpr;
use crate::prepared_context::prepare_context;

fn register_custom_err(ctx: &mut VerificationContext) {
    ctx.register_struct_type(StructDef::new(
        "CustomErr",
        vec![("error_code".to_string(), TrustVcType::Int { width: 32 })],
    ));
}

fn register_qualified_custom_err(ctx: &mut VerificationContext) {
    ctx.register_struct_type(StructDef::new(
        "errors::CustomErr",
        vec![("error_code".to_string(), TrustVcType::Int { width: 32 })],
    ));
}

#[test]
fn result_unwrap_direct_ok_verifies_payload() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "result_unwrap_ok_payload",
        "Result::<i8, i32>::Ok(1i8).unwrap() == 1i8",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Result::unwrap on direct Ok should expose payload");
}

#[test]
fn result_expect_direct_ok_verifies_payload() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "result_expect_ok_payload",
        "Result::<u32, i32>::Ok(7u32).expect(\"expected Ok\") == 7u32",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Result::expect on direct Ok should expose payload");
}

#[test]
fn result_unwrap_known_local_ok_verifies_payload() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "result_unwrap_local_ok_payload",
        "{ let ok_result = Result::<i8, i32>::Ok(1i8); ok_result.unwrap() == 1i8 }",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Result::unwrap on a known local Ok should expose payload",
    );
}

#[test]
fn result_expect_known_local_ok_verifies_payload() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "result_expect_local_ok_payload",
        "{ let ok_result = Result::<u32, i32>::Ok(7u32); ok_result.expect(\"expected Ok\") == 7u32 }",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Result::expect on a known local Ok should expose payload",
    );
}

#[test]
fn result_unwrap_err_direct_custom_err_verifies_payload() {
    let mut ctx = VerificationContext::new();
    register_custom_err(&mut ctx);
    ctx.push_obligation(ProofObligation::assert(
        "result_unwrap_err_custom_payload",
        "Result::<i8, CustomErr>::Err(CustomErr { error_code: -1i32 }).unwrap_err() == (CustomErr { error_code: -1i32 })",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Result::unwrap_err on direct custom Err should expose payload",
    );
}

#[test]
fn result_unwrap_err_known_local_custom_err_verifies_payload() {
    let mut ctx = VerificationContext::new();
    register_custom_err(&mut ctx);
    ctx.push_obligation(ProofObligation::assert(
        "result_unwrap_err_local_custom_payload",
        "{ let err_result = Result::<i8, CustomErr>::Err(CustomErr { error_code: -1i32 }); err_result.unwrap_err() == (CustomErr { error_code: -1i32 }) }",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Result::unwrap_err on a known local custom Err should expose payload",
    );
}

#[test]
fn result_verus_variant_tests_verify() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "result_verus_is_ok",
        "Result::<i8, i32>::Ok(1i8) is Ok",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "result_verus_is_err",
        "Result::<i8, i32>::Err(-1i32) is Err",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(&result, "Verus Result `is Ok`/`is Err` should verify");
}

#[test]
fn result_verus_wrong_variant_tests_are_counterexamples() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "result_verus_ok_is_err",
        "Result::<i8, i32>::Ok(1i8) is Err",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "direct Ok cannot satisfy `is Err`");

    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "result_verus_err_is_ok",
        "Result::<i8, i32>::Err(-1i32) is Ok",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "direct Err cannot satisfy `is Ok`");
}

#[test]
fn result_extracted_wrong_variant_tests_are_counterexamples() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "result_extracted_ok_is_err",
        "(Result :: < i32, i32 > :: Ok(1i32)).is_err()",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "extracted direct Ok cannot satisfy Result::is_err");

    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "result_extracted_err_is_ok",
        "(Result :: < i32, i32 > :: Err(-1i32)).is_ok()",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "extracted direct Err cannot satisfy Result::is_ok");
}

#[test]
fn result_extracted_custom_wrong_variant_prepares_to_false() {
    let mut ctx = VerificationContext::new();
    register_custom_err(&mut ctx);
    ctx.push_obligation(ProofObligation::assert(
        "result_extracted_ok_is_err",
        "(Result :: < i32, CustomErr > :: Ok(1i32)).is_err()",
    ));

    let prepared = prepare_context(&ctx).expect("extracted Result condition should prepare");
    assert_eq!(prepared.obligations[0].expr, TrustVcExpr::BoolLit(false));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "extracted custom Ok should return Counterexample for Result::is_err",
    );
}

#[test]
fn result_verus_custom_wrong_variant_is_counterexample() {
    let mut ctx = VerificationContext::new();
    register_custom_err(&mut ctx);
    ctx.push_obligation(ProofObligation::assert(
        "result_verus_custom_err_is_ok",
        "Result::<i8, CustomErr>::Err(CustomErr { error_code: -1i32 }) is Ok",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(&result, "custom Err cannot satisfy Verus Result `is Ok`");
}

#[test]
fn result_custom_datatype_constant_false_is_counterexample() {
    let mut ctx = VerificationContext::new();
    register_custom_err(&mut ctx);
    ctx.push_obligation(ProofObligation::assert(
        "custom_datatype_constant_false",
        "false",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "constant false with a registered custom datatype should bypass solver unknowns",
    );
}

#[test]
fn result_verus_ok_projection_direct_verifies_payload() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "result_verus_ok_projection_payload",
        "Result::<i8, i32>::Ok(1i8)->Ok_0 == 1i8",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Verus Result Ok_0 projection should expose payload",
    );
}

#[test]
fn result_verus_direct_projection_wrong_payload_is_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "result_verus_ok_projection_wrong_payload",
        "Result::<i8, i32>::Ok(1i8)->Ok_0 == 2i8",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "Verus Result Ok_0 projection should not prove the wrong payload",
    );
}

#[test]
fn result_extracted_direct_projection_wrong_payload_is_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "result_extracted_err_projection_wrong_payload",
        ":: trust_vc_core :: __trust_vc_result_err_0(Result :: < i8, i32 > :: Err(-1i32)) == 0i32",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "extracted Result Err_0 projection should not prove the wrong payload",
    );
}

#[test]
fn result_verus_err_projection_known_local_verifies_payload() {
    let mut ctx = VerificationContext::new();
    register_custom_err(&mut ctx);
    ctx.push_obligation(ProofObligation::assert(
        "result_verus_err_projection_local_custom_payload",
        "{ let err_result = Result::<i8, CustomErr>::Err(CustomErr { error_code: -1i32 }); \
           err_result is Err && err_result->Err_0 == (CustomErr { error_code: -1i32 }) }",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Verus Result Err_0 projection should expose custom Err payload",
    );
}

#[test]
fn result_verus_err_projection_wrong_payload_is_counterexample() {
    let mut ctx = VerificationContext::new();
    register_custom_err(&mut ctx);
    ctx.push_obligation(ProofObligation::assert(
        "result_verus_err_projection_wrong_custom_payload",
        "Result::<i8, CustomErr>::Err(CustomErr { error_code: -1i32 })->Err_0 \
            == (CustomErr { error_code: 0i32 })",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Verus Result Err_0 projection should not prove the wrong payload",
    );
}

#[test]
fn result_unwrap_err_qualified_custom_err_verifies_payload() {
    let mut ctx = VerificationContext::new();
    register_qualified_custom_err(&mut ctx);
    ctx.push_obligation(ProofObligation::assert(
        "result_unwrap_err_qualified_custom_payload",
        "Result::<i8, errors::CustomErr>::Err(errors::CustomErr { error_code: -1i32 }).unwrap_err()
            == (errors::CustomErr { error_code: -1i32 })",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_verified(
        &result,
        "Result::unwrap_err should preserve qualified custom Err payloads",
    );
}

#[test]
fn result_unwrap_err_wrong_custom_payload_is_counterexample() {
    let mut ctx = VerificationContext::new();
    register_custom_err(&mut ctx);
    ctx.push_obligation(ProofObligation::assert(
        "result_unwrap_err_wrong_custom_payload",
        "Result::<i8, CustomErr>::Err(CustomErr { error_code: -1i32 }).unwrap_err() == (CustomErr { error_code: 0i32 })",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Result::unwrap_err on custom Err should not prove the wrong payload",
    );
}

#[test]
fn result_unwrap_err_wrong_i32_payload_is_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "result_unwrap_err_wrong_i32_payload",
        "Result::<i8, i32>::Err(-1i32).unwrap_err() == 0i32",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_counterexample(
        &result,
        "Result::unwrap_err on primitive Err should not prove the wrong payload",
    );
}

#[test]
fn result_unwrap_err_direct_ok_is_rejected() {
    let mut ctx = VerificationContext::new();
    register_custom_err(&mut ctx);
    ctx.push_obligation(ProofObligation::assert(
        "result_unwrap_err_ok",
        "Result::<i8, CustomErr>::Ok(1i8).unwrap_err() == (CustomErr { error_code: -1i32 })",
    ));

    let result = AYEncoder::verify(&ctx);
    match result {
        VerifyResult::Error { message } => assert!(
            message.contains("Result::unwrap_err requires a receiver known to be Err"),
            "error should mention known-Err requirement, got: {message}",
        ),
        other => panic!(
            "expected Error for Result::unwrap_err on Ok, got: {:?}",
            other
        ),
    }
}

#[test]
fn result_unwrap_wrong_payload_is_counterexample() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "result_unwrap_wrong_payload",
        "Result::<i8, i32>::Ok(1i8).unwrap() == 2i8",
    ));

    let result = AYEncoder::verify(&ctx);
    expect_fail_closed(
        &result,
        "Result::unwrap on Ok should not prove the wrong payload",
    );
}

#[test]
fn result_unwrap_direct_err_is_rejected() {
    let mut ctx = VerificationContext::new();
    ctx.push_obligation(ProofObligation::assert(
        "result_unwrap_err",
        "Result::<i8, i32>::Err(-1i32).unwrap() == 1i8",
    ));

    let result = AYEncoder::verify(&ctx);
    match result {
        VerifyResult::Error { message } => assert!(
            message.contains("Result::unwrap requires a receiver known to be Ok"),
            "error should mention known-Ok requirement, got: {message}",
        ),
        other => panic!("expected Error for Result::unwrap on Err, got: {:?}", other),
    }
}
