// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Basic trait registration, postcondition axioms, and prepare_context transport.

use super::*;

#[test]
fn test_register_trait_declares_method_ufs_and_is_idempotent() {
    let mut encoder = AYEncoder::new();
    let decl = counter_trait_decl();

    let before_assertions = encoder.solver.assertions().len();
    let encoding = encoder
        .register_trait(&decl)
        .expect("trait registration should succeed");
    let after_first = encoder.solver.assertions().len();
    let cached = encoder
        .register_trait(&decl)
        .expect("re-registering the same trait should reuse the cache");
    let after_second = encoder.solver.assertions().len();

    assert_eq!(encoding.name, "CounterSpec");
    assert!(encoding.method_fns.contains_key("value"));
    assert!(encoding.method_fns.contains_key("grant"));
    assert_eq!(encoding.method_fns.len(), 2);
    assert_eq!(cached.method_fns.len(), 2);
    assert!(
        after_first > before_assertions,
        "first registration should add quantified trait axioms"
    );
    assert_eq!(
        after_first, after_second,
        "cached registration should not add duplicate axioms"
    );
    assert!(
        encoder.fn_ctx.functions.contains_key("CounterSpec__value"),
        "trait method UFs should be registered in the function table"
    );
    assert_eq!(
        encoder.fn_ctx.return_types.get("CounterSpec__grant"),
        Some(&TrustVcType::Bool)
    );
}

#[test]
fn test_trait_postcondition_axiom_constrains_method_result_when_precondition_holds() {
    let mut encoder = AYEncoder::new();
    let decl = counter_trait_decl();
    encoder
        .register_trait(&decl)
        .expect("trait registration should succeed");

    let poly = Sort::Uninterpreted("Poly".to_string());
    let self_term = encoder.solver.declare_const("trait_self", poly);
    let token = encoder.solver.bool_const(true);
    let truth = encoder.solver.bool_const(true);
    let lie = encoder.solver.bool_const(false);
    let value_fn = encoder
        .fn_ctx
        .functions
        .get("CounterSpec__value")
        .expect("value UF should be registered")
        .clone();
    let grant_fn = encoder
        .fn_ctx
        .functions
        .get("CounterSpec__grant")
        .expect("grant UF should be registered")
        .clone();

    let value = encoder
        .solver
        .try_apply(&value_fn, &[self_term])
        .expect("value application should encode");
    let grant = encoder
        .solver
        .try_apply(&grant_fn, &[self_term, token])
        .expect("grant application should encode");
    let value_is_true = encoder
        .solver
        .try_eq(value, truth)
        .expect("value equality should encode");
    let grant_is_false = encoder
        .solver
        .try_eq(grant, lie)
        .expect("bad result equality should encode");

    encoder
        .solver
        .try_assert_term(value_is_true)
        .expect("value equality should assert");
    encoder
        .solver
        .try_assert_term(grant_is_false)
        .expect("bad result equality should assert");

    assert!(
        encoder.solver.try_check_sat().unwrap().is_unsat(),
        "grant(self, true) == false should be unsat when the precondition holds and the postcondition requires result"
    );
}

#[test]
fn test_trait_postcondition_axiom_is_guarded_by_precondition() {
    let mut encoder = AYEncoder::new();
    let decl = counter_trait_decl();
    encoder
        .register_trait(&decl)
        .expect("trait registration should succeed");

    let poly = Sort::Uninterpreted("Poly".to_string());
    let self_term = encoder.solver.declare_const("trait_self", poly);
    let token = encoder.solver.bool_const(true);
    let truth = encoder.solver.bool_const(true);
    let falsity = encoder.solver.bool_const(false);
    let value_fn = encoder
        .fn_ctx
        .functions
        .get("CounterSpec__value")
        .expect("value UF should be registered")
        .clone();
    let grant_fn = encoder
        .fn_ctx
        .functions
        .get("CounterSpec__grant")
        .expect("grant UF should be registered")
        .clone();

    let value = encoder
        .solver
        .try_apply(&value_fn, &[self_term])
        .expect("value application should encode");
    let grant = encoder
        .solver
        .try_apply(&grant_fn, &[self_term, token])
        .expect("grant application should encode");
    let value_is_false = encoder
        .solver
        .try_eq(value, falsity)
        .expect("value equality should encode");
    let grant_is_false = encoder
        .solver
        .try_eq(grant, falsity)
        .expect("result equality should encode");
    let token_is_true = encoder
        .solver
        .try_eq(token, truth)
        .expect("token equality should encode");

    encoder
        .solver
        .try_assert_term(value_is_false)
        .expect("value equality should assert");
    encoder
        .solver
        .try_assert_term(grant_is_false)
        .expect("result equality should assert");
    encoder
        .solver
        .try_assert_term(token_is_true)
        .expect("token equality should assert");

    let result = encoder.solver.try_check_sat().unwrap();
    assert!(
        result.is_sat() || result.is_unknown(),
        "false preconditions should disable the postcondition axiom or fail closed: {:?}",
        result.result()
    );
}

#[test]
fn test_setup_from_prepared_registers_transported_trait_decls() {
    let mut ctx = crate::vc::VerificationContext::new();
    ctx.push_obligation(crate::vc::ProofObligation::assert("trivial", "true"));
    ctx.register_trait_decl(counter_trait_decl());

    let prepared =
        crate::prepared_context::prepare_context(&ctx).expect("prepare_context should succeed");
    let slices =
        crate::encoder::verification::VerificationSlices::new(&prepared, &[], &[], &[], &[], &[]);
    let encoder = AYEncoder::setup_from_prepared(&slices, false, None)
        .expect("setup_from_prepared should register transported trait metadata");

    assert!(
        encoder.fn_ctx.functions.contains_key("CounterSpec__grant"),
        "setup_from_prepared should register trait methods from prepared context"
    );
    assert!(
        encoder.trait_encoding("CounterSpec").is_some(),
        "transported trait declarations should populate encoder trait cache"
    );
}

#[test]
fn test_verification_pipeline_round_trips_trait_bound_method_call() {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    let type_param = TrustVcType::TypeParam("T".to_string());
    ctx.declare_var_typed("counter", type_param.clone());
    ctx.function_context = Some(crate::vc::FunctionContext {
        name: "lemma".to_string(),
        params: vec![("counter".to_string(), type_param)],
        return_type: TrustVcType::Bool,
        is_recursive: false,
        mode: crate::mode::FunctionMode::Spec,
        trait_bounds: vec![TraitBound {
            type_param: "T".to_string(),
            trait_name: "CounterSpec".to_string(),
        }],
    });
    ctx.register_trait_decl(counter_trait_decl());
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "excluded_middle",
        "counter.grant(true) || !counter.grant(true)",
    ));

    let result = pipeline.verify();
    expect_verified(
        &result,
        "verification pipeline should lower, encode, and verify trait-bound method calls",
    );
}
