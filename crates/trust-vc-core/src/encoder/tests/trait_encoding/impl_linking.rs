// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Per-impl linking axiom tests, prepare_context transport for impls,
//! and helper function trait bounds.

use super::*;

#[test]
fn test_register_trait_impl_emits_linking_axiom() {
    let mut encoder = AYEncoder::new();
    encoder
        .register_trait(&simple_trait_decl())
        .expect("trait registration should succeed");

    // Register concrete impl function: BoolImpl__get_value(Bool) -> Bool
    let bool_sort = Sort::Bool;
    let impl_fn = encoder
        .solver
        .try_declare_fun(
            "BoolImpl__get_value",
            std::slice::from_ref(&bool_sort),
            bool_sort.clone(),
        )
        .expect("impl function declaration should succeed");
    encoder
        .fn_ctx
        .functions
        .insert("BoolImpl__get_value".to_string(), impl_fn);
    encoder
        .fn_ctx
        .return_types
        .insert("BoolImpl__get_value".to_string(), TrustVcType::Bool);
    encoder
        .fn_ctx
        .param_types
        .insert("BoolImpl__get_value".to_string(), vec![TrustVcType::Bool]);

    let before = encoder.solver.assertions().len();
    encoder
        .register_trait_impl(&simple_impl_decl())
        .expect("trait impl registration should succeed");
    let after = encoder.solver.assertions().len();

    assert!(
        after > before,
        "register_trait_impl should add linking axioms"
    );
}

#[test]
fn test_impl_linking_axiom_chains_trait_uf_to_concrete_function() {
    let mut encoder = AYEncoder::new();
    encoder
        .register_trait(&simple_trait_decl())
        .expect("trait registration should succeed");

    // Concrete function always returns true: BoolImpl__get_value(x) == true
    let bool_sort = Sort::Bool;
    let impl_fn = encoder
        .solver
        .try_declare_fun(
            "BoolImpl__get_value",
            std::slice::from_ref(&bool_sort),
            bool_sort.clone(),
        )
        .expect("impl function declaration should succeed");
    encoder
        .fn_ctx
        .functions
        .insert("BoolImpl__get_value".to_string(), impl_fn.clone());
    encoder
        .fn_ctx
        .return_types
        .insert("BoolImpl__get_value".to_string(), TrustVcType::Bool);
    encoder
        .fn_ctx
        .param_types
        .insert("BoolImpl__get_value".to_string(), vec![TrustVcType::Bool]);

    // Assert concrete function always returns true
    let x = encoder.solver.declare_const("x_impl", bool_sort.clone());
    let impl_result = encoder
        .solver
        .try_apply(&impl_fn, &[x])
        .expect("apply should succeed");
    let truth = encoder.solver.bool_const(true);
    let impl_always_true = encoder
        .solver
        .try_eq(impl_result, truth)
        .expect("eq should succeed");
    let forall = encoder
        .solver
        .try_forall_with_triggers(&[x], impl_always_true, &[&[impl_result]])
        .expect("forall should succeed");
    encoder
        .solver
        .try_assert_term(forall)
        .expect("assert should succeed");

    // Register impl linking axiom
    encoder
        .register_trait_impl(&simple_impl_decl())
        .expect("trait impl registration should succeed");

    // The trait method on a boxed Bool value should also return true
    let box_fn = encoder
        .box_fn_for_type(&TrustVcType::Bool)
        .cloned()
        .expect("Box_Bool should be declared by register_trait_impl");

    let test_val = encoder.solver.declare_const("test_val", bool_sort);
    let boxed_val = encoder
        .solver
        .try_apply(&box_fn, &[test_val])
        .expect("box should succeed");
    let trait_fn = encoder
        .fn_ctx
        .functions
        .get("Valued__get_value")
        .expect("trait UF should exist")
        .clone();
    let trait_result = encoder
        .solver
        .try_apply(&trait_fn, &[boxed_val])
        .expect("trait apply should succeed");

    // Assert the trait result is false — should be unsat because linking
    // axiom chains: Valued__get_value(Box_Bool(v)) == BoolImpl__get_value(v) == true
    let falsity = encoder.solver.bool_const(false);
    let is_false = encoder
        .solver
        .try_eq(trait_result, falsity)
        .expect("eq should succeed");
    encoder
        .solver
        .try_assert_term(is_false)
        .expect("assert should succeed");

    assert!(
        encoder.solver.try_check_sat().unwrap().is_unsat(),
        "linking axiom should chain trait UF through Box to concrete function"
    );
}

#[test]
fn test_setup_from_prepared_registers_transported_trait_impls() {
    let mut ctx = crate::vc::VerificationContext::new();
    ctx.push_obligation(crate::vc::ProofObligation::assert("trivial", "true"));
    ctx.register_trait_decl(simple_trait_decl());

    // Register the concrete impl function as a typed helper so it gets a
    // FunctionContext registration in setup_from_prepared.
    ctx.declare_helper_function_typed(
        "BoolImpl__get_value",
        TrustVcType::Bool,
        vec![("self".to_string(), TrustVcType::Bool)],
    );
    ctx.register_trait_impl(simple_impl_decl());

    let prepared =
        crate::prepared_context::prepare_context(&ctx).expect("prepare_context should succeed");

    assert_eq!(
        prepared.trait_impl_decls.len(),
        1,
        "trait impl decls should be transported through prepare_context"
    );

    let slices =
        crate::encoder::verification::VerificationSlices::new(&prepared, &[], &[], &[], &[], &[]);
    let encoder = AYEncoder::setup_from_prepared(&slices, false, None)
        .expect("setup_from_prepared should register trait impls");

    assert!(
        encoder.box_fn_for_type(&TrustVcType::Bool).is_some(),
        "Box_Bool should be declared by impl registration in setup"
    );
}

#[test]
fn test_helper_function_trait_bounds_survive_prepare_context() {
    let mut ctx = crate::vc::VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::TypeParam("T".to_string()));
    ctx.register_trait_decl(counter_trait_decl());
    ctx.push_obligation(crate::vc::ProofObligation::assert("trivial", "true"));

    ctx.declare_helper_function_typed_with_bounds(
        "helper_fn",
        TrustVcType::Bool,
        vec![("x".to_string(), TrustVcType::TypeParam("T".to_string()))],
        vec![TraitBound {
            type_param: "T".to_string(),
            trait_name: "CounterSpec".to_string(),
        }],
    );

    let prepared =
        crate::prepared_context::prepare_context(&ctx).expect("prepare_context should succeed");

    assert_eq!(prepared.helper_function_contexts.len(), 1);
    assert_eq!(
        prepared.helper_function_contexts[0].trait_bounds.len(),
        1,
        "trait bounds should survive prepare_context, not be dropped to vec![]"
    );
    assert_eq!(
        prepared.helper_function_contexts[0].trait_bounds[0].trait_name,
        "CounterSpec"
    );
}

#[test]
fn test_verification_pipeline_chains_helper_trait_bound_call_through_impl_axiom() {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    let type_param = TrustVcType::TypeParam("T".to_string());
    ctx.declare_var_typed("x", type_param.clone());
    ctx.declare_var_typed("self", TrustVcType::Bool);
    ctx.declare_var_typed("flag", TrustVcType::Bool);
    ctx.register_trait_decl(simple_trait_decl());
    ctx.register_trait_impl(simple_impl_decl());
    ctx.declare_helper_function_typed_with_bounds(
        "generic_get",
        TrustVcType::Bool,
        vec![("x".to_string(), type_param)],
        vec![TraitBound {
            type_param: "T".to_string(),
            trait_name: "Valued".to_string(),
        }],
    );
    // Receiver param must be named "self" so the conformance checker's
    // rename map correctly grounds the body axiom onto __trust_vc_impl_self.
    ctx.declare_helper_function_typed(
        "BoolImpl__get_value",
        TrustVcType::Bool,
        vec![("self".to_string(), TrustVcType::Bool)],
    );
    ctx.push_obligation(
        crate::vc::ProofObligation::broadcast_assume(
            "__body_axiom_generic_get",
            "generic_get(x) == x.get_value()",
        )
        .with_bound_vars(vec!["x".to_string()])
        .with_trigger_patterns(vec![vec!["generic_get(x)".to_string()]]),
    );
    ctx.push_obligation(
        crate::vc::ProofObligation::broadcast_assume(
            "__body_axiom_BoolImpl__get_value",
            "BoolImpl__get_value(self) == true",
        )
        .with_bound_vars(vec!["self".to_string()])
        .with_trigger_patterns(vec![vec!["BoolImpl__get_value(self)".to_string()]]),
    );
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "concrete_call",
        "generic_get(flag)",
    ));

    let result = pipeline.verify();
    expect_verified(&result, "concrete call should chain through generic helper body axiom, trait UF, impl linking axiom, and concrete body axiom");
}
