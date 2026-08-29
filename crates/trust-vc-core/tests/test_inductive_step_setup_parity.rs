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

/// A type invariant may be ASSUMED for a PARAMETER: the caller had to build the
/// value, so the callee inherits the obligation as a fact. `c` is declared as a
/// parameter of the function under verification, which is what entitles the
/// encoder to assert `inv_Counter(c)`.
#[test]
fn test_frame_condition_inductive_step_registers_struct_and_type_invariant() {
    let mut ctx = VerificationContext::new();
    let counter = counter_struct();
    ctx.declare_var_typed("c", counter.to_datatype_type());
    ctx.declare_var_typed("i", trust_vc_core::ir::TrustVcType::parse_or_opaque("i32"));
    ctx.set_function_context(FunctionContext::new(
        "uses_counter",
        vec![("c".to_string(), counter.to_datatype_type())],
        TrustVcType::Bool,
        FunctionMode::Proof,
    ));
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

/// THE LIAR PIN for the type-invariant surface.
///
/// `c` is NOT a parameter — it is an ordinary variable, i.e. a value this
/// function itself would have constructed. Nothing has ESTABLISHED its
/// invariant, so `inv_Counter(c)` must not be assumed and `c.count <= c.max`
/// must not be provable. Asserting it for free was a latent cardinal
/// false-verify: a locally built value violating its invariant contradicts the
/// `inv_T(x) <==> body(x)` defining axiom and proves anything.
///
/// This is the discriminator against
/// [`test_frame_condition_inductive_step_registers_struct_and_type_invariant`]:
/// the two contexts differ ONLY in whether `c` is a declared parameter.
#[test]
fn type_invariant_is_not_assumed_for_a_non_parameter_value() {
    let mut ctx = VerificationContext::new();
    let counter = counter_struct();
    ctx.declare_var_typed("c", counter.to_datatype_type());
    ctx.register_struct_type(counter);
    ctx.set_type_invariant("Counter", counter_invariant());
    ctx.push_obligation(ProofObligation::assert("counter_post", "c.count <= c.max"));

    let result = verify_context(ctx);
    assert_ne!(
        result,
        VerifyResult::Verified,
        "a non-parameter value's type invariant must NOT be assumed for free: \
         nothing established it, so `c.count <= c.max` is unproven"
    );
}

/// The surface's only producer is `pub`, so this hole is one wiring call away
/// from being live. Pin that no PRODUCTION source file calls it — the guard
/// above is what makes the surface safe to wire, and this test is what makes a
/// future wiring visible in review.
#[test]
fn set_type_invariant_has_no_production_caller() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates/ dir")
        .to_path_buf();
    let mut callers = Vec::new();
    let mut stack = vec![root];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                if path.file_name().is_some_and(|n| n == "target") {
                    continue;
                }
                stack.push(path);
                continue;
            }
            if path.extension().is_none_or(|ext| ext != "rs") {
                continue;
            }
            // Only `src/` counts as production; `tests/` and `src/**/tests*`
            // are where the surface is legitimately exercised.
            let as_str = path.to_string_lossy().replace('\\', "/");
            if !as_str.contains("/src/") || as_str.contains("test") {
                continue;
            }
            let Ok(text) = std::fs::read_to_string(&path) else {
                continue;
            };
            for line in text.lines() {
                let line = line.trim();
                if line.contains(".set_type_invariant(") && !line.starts_with("///") {
                    callers.push(format!("{as_str}: {line}"));
                }
            }
        }
    }
    assert!(
        callers.is_empty(),
        "`set_type_invariant` gained a production caller. The type-invariant \
         surface asserts `inv_T(v)` as a FREE axiom and there is still no \
         ESTABLISHMENT obligation at construction sites — wiring it requires \
         adding that obligation first. Callers found: {callers:#?}"
    );
}
