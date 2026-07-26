// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression tests for inductive-step setup parity with the main prepared
//! encoder bootstrap. Part of #2552.

use trust_vc_core::ir::{
    CompareOp, StructDef, TraitBound, TraitDecl, TraitImplDecl, TraitMethodDecl, TrustVcExpr,
    TrustVcType,
};
use trust_vc_core::mode::FunctionMode;
use trust_vc_core::vc::{FunctionContext, ProofObligation, VerificationContext};
use trust_vc_core::verification_bridge::VerificationPipeline;
use trust_vc_core::VerifyResult;

mod common;

fn verify_context(context: VerificationContext) -> VerifyResult {
    common::with_clean_verification(|| {
        let mut pipeline = VerificationPipeline::new();
        pipeline.replace_context(context);
        pipeline.verify()
    })
}

fn slice6_trait_decl() -> TraitDecl {
    TraitDecl::new(
        "Slice6Valued",
        vec![TraitMethodDecl::new(
            "get_value",
            vec![],
            TrustVcType::Bool,
            vec![],
            vec!["result".to_string()],
            false,
            None,
        )],
    )
}

fn counter_struct() -> StructDef {
    StructDef::new(
        "Counter",
        vec![
            ("count".to_string(), TrustVcType::Uint { width: 32 }),
            ("max".to_string(), TrustVcType::Uint { width: 32 }),
        ],
    )
}

fn counter_invariant() -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: CompareOp::Le,
        left: Box::new(TrustVcExpr::Var {
            name: "count".to_string(),
            ty: TrustVcType::Uint { width: 32 },
        }),
        right: Box::new(TrustVcExpr::Var {
            name: "max".to_string(),
            ty: TrustVcType::Uint { width: 32 },
        }),
    }
}

#[test]
fn test_havoc_all_inductive_step_registers_trait_helper_bootstrap() {
    let mut ctx = VerificationContext::new();
    let type_param = TrustVcType::TypeParam("T".to_string());
    ctx.declare_var_typed("value", type_param.clone());
    ctx.declare_var_typed("self", TrustVcType::Bool);
    ctx.set_function_context(
        FunctionContext::new(
            "lemma",
            vec![("value".to_string(), type_param.clone())],
            TrustVcType::Bool,
            FunctionMode::Spec,
        )
        .with_trait_bounds(vec![TraitBound::new("T", "Slice6Valued")]),
    );
    ctx.register_trait_decl(slice6_trait_decl());
    ctx.register_trait_impl(TraitImplDecl::new(
        "Slice6Valued",
        TrustVcType::Bool,
        vec![("get_value".to_string(), "Slice6BoolImpl__good".to_string())],
    ));
    ctx.declare_helper_function_typed(
        "Slice6BoolImpl__good",
        TrustVcType::Bool,
        vec![("self".to_string(), TrustVcType::Bool)],
    );
    ctx.push_obligation(
        ProofObligation::broadcast_assume(
            "__body_axiom_Slice6BoolImpl__good",
            "Slice6BoolImpl__good(self) == true",
        )
        .with_bound_vars(vec!["self".to_string()])
        .with_trigger_patterns(vec![vec!["Slice6BoolImpl__good(self)".to_string()]]),
    );
    ctx.push_obligation(ProofObligation::loop_invariant(
        "trait_value_stable",
        "value.get_value()",
    ));
    ctx.push_obligation(ProofObligation::assert(
        "trait_value_post",
        "value.get_value()",
    ));

    let result = verify_context(ctx);
    assert_eq!(
        result,
        VerifyResult::Verified,
        "trait/helper bootstrap should survive the havoc-all inductive-step path: {:?}",
        result
    );
}

#[test]
fn test_frame_condition_inductive_step_registers_struct_and_type_invariant() {
    let mut ctx = VerificationContext::new();
    let counter = counter_struct();
    ctx.declare_var_typed("c", counter.to_datatype_type());
    ctx.declare_var_typed("i", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.register_struct_type(counter);
    ctx.set_type_invariant("Counter", counter_invariant());
    ctx.push_obligation(ProofObligation::loop_invariant(
        "counter_stable",
        "c.count <= c.max",
    ));
    ctx.set_loop_modified_vars("counter_stable", vec!["i".to_string()]);
    ctx.push_obligation(ProofObligation::assert("counter_post", "c.count <= c.max"));

    let result = verify_context(ctx);
    assert_eq!(
        result,
        VerifyResult::Verified,
        "struct/type-invariant bootstrap should survive the frame-condition inductive-step path: {:?}",
        result
    );
}
