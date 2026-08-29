//! Additional Slice 6 trait-conformance regressions.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashMap;

use crate::encoder::tests::{expect_counterexample, expect_verified};
use crate::encoder::VerifyResult;
use crate::ir::{StructDef, TraitDecl, TraitImplDecl, TraitMethodDecl, TrustVcType};
use crate::prepared_context::{prepare_context, PreparedVerificationContext};
use crate::vc::{ProofObligation, VerificationMode};

use super::tests::{
    add_body_axiom, pipeline_conformance_verdict, valued_impl_decl, valued_trait_decl,
};
use crate::encoder::tests::conformance_verdict;

/// Trait `Valued2 { #[ensures(result == 5)] fn get(&self) -> u32 }` whose self
/// receiver is a user struct rather than a built-in type. Mirrors the context
/// `extract_verification_conditions_with_file_context` produces for
/// `#[trait_spec] trait Valued2 { ... }`: a parameterless (besides `self`)
/// method with a non-trivial `ensures`.
fn struct_valued_trait_decl() -> TraitDecl {
    TraitDecl {
        name: "Slice6StructValued".to_string(),
        methods: vec![TraitMethodDecl {
            name: "get".to_string(),
            params: vec![],
            return_type: TrustVcType::Uint { width: 32 },
            requires: vec![],
            ensures: vec!["result == 5".to_string()],
            has_default: false,
            default_body: None,
            default_ensures: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    }
}

/// Trait-impl registration exactly as the proc-macro `parse_trait_impl_decl`
/// emits it for `#[trait_impl] impl Slice6StructValued for Counter` — the self
/// type is resolved WITHOUT the struct registry, so it lands as
/// `Opaque("Counter")` even though `Counter` is a registered struct. This is
/// the shape that previously caused `verify_trait_conformance` to SKIP the
/// impl entirely.
fn struct_valued_opaque_impl_decl(concrete_fn_name: &str) -> TraitImplDecl {
    TraitImplDecl {
        inherent_shadowed_methods: Default::default(),
        trait_name: "Slice6StructValued".to_string(),
        concrete_type: TrustVcType::Opaque("Counter".to_string()),
        method_bindings: vec![("get".to_string(), concrete_fn_name.to_string())],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    }
}

/// Builds the prepared context that `extract_verification_conditions_with_file_context`
/// produces for a user struct + trait-impl: `struct Counter;` registered in
/// `struct_types`, the trait-impl `concrete_type` left `Opaque("Counter")`, the
/// concrete impl-method body axiom (`Counter__get(self) == body_value`), and a
/// trivially-true user goal so the only real obligation is impl conformance.
fn prepared_struct_conformance_context(
    concrete_fn_name: &str,
    body_value: &str,
) -> PreparedVerificationContext {
    let counter_ty = StructDef::new("Counter", vec![]).to_datatype_type();
    let mut ctx = crate::vc::VerificationContext::new();
    // `struct Counter;` — the registry entry that lets prepare_context resolve
    // the Opaque concrete type back to the encodable Datatype sort.
    ctx.register_struct_type(StructDef::new("Counter", vec![]));
    ctx.register_trait_decl(struct_valued_trait_decl());
    ctx.register_trait_impl(struct_valued_opaque_impl_decl(concrete_fn_name));
    ctx.declare_var_typed("self", counter_ty.clone());
    // Concrete impl method `fn get(&self) -> u32 { body_value }`, modeled as a
    // u32-returning UF over the Counter Datatype receiver plus the body axiom
    // pinning its value. `add_body_axiom` hardcodes a Bool return, so register
    // the typed helper directly to match the trait's `u32` return type.
    ctx.declare_helper_function_typed(
        concrete_fn_name,
        TrustVcType::Uint { width: 32 },
        vec![("self".to_string(), counter_ty)],
    );
    ctx.push_obligation(
        ProofObligation::broadcast_assume(
            format!("__body_axiom_{concrete_fn_name}"),
            format!("{concrete_fn_name}(self) == {body_value}"),
        )
        .with_bound_vars(vec!["self".to_string()])
        .with_trigger_patterns(vec![vec![format!("{concrete_fn_name}(self)")]])
        .with_opaque(true),
    );
    ctx.push_obligation(ProofObligation::assert("user_goal", "true"));
    prepare_context(&ctx).expect("struct conformance context should prepare")
}

/// Faithfulness fix: a user-struct trait impl whose body SATISFIES the trait's
/// `ensures(result == 5)` must now have conformance actually RUN (the Opaque
/// concrete type is resolved to the registered `Counter` Datatype) and DISCHARGE
/// — Verified, not silently skipped. This is the conforming half of the
/// adversarial pair; on its own it cannot prove enforcement (an unsound skip
/// also yields Verified), so the non-conforming sibling below is mandatory.
#[test]
fn test_trait_conformance_runs_for_conforming_user_struct_impl() {
    let prepared = prepared_struct_conformance_context("Counter__get_good", "5");
    // Pre-condition for the test to be meaningful: the Opaque concrete type was
    // resolved to a Datatype, so conformance is NOT skipped via contains_opaque.
    assert!(
        prepared
            .trait_impl_decls
            .iter()
            .all(|d| !d.concrete_type.contains_opaque()),
        "prepare_context must resolve the Opaque user-struct concrete type to a Datatype so \
         conformance is not skipped; got {:?}",
        prepared.trait_impl_decls
    );
    let result = conformance_verdict(&prepared);
    expect_verified(
        &result,
        "conformance must run AND discharge for a conforming user-struct trait impl",
    );
}

/// ADVERSARIAL probe the prior unsound attempt omitted: same user-struct impl,
/// but the body returns 6, violating the trait's `ensures(result == 5)`.
///
/// SOUNDNESS-CRITICAL: with the Opaque concrete type resolved to the registered
/// `Counter` Datatype, conformance now RUNS and must NOT verify this impl —
/// before the fix it was silently SKIPPED via `contains_opaque()` and the impl
/// passed as Verified, exactly the faithfulness hole this change closes (Verus
/// rejects this impl).
///
/// The verdict here is a fail-closed `Unknown` rather than a crisp
/// `Counterexample`: with a built-in self (e.g. `bool`) the SAME shape yields a
/// `Counterexample` with a model, but a `Datatype` self carries quantified
/// constructor/selector/tester axioms (carrier `Sort::Int`) that ay's
/// quantifier engine cannot fully instantiate during SAT/model construction, so
/// it returns `Unknown ((incomplete quantifier-...))`. That is an ay
/// model-construction incompleteness over datatype axioms, NOT a trust-vc
/// soundness hole — the impl is correctly NOT accepted. Closing the gap to a
/// crisp counterexample is ay-side work. The assertion below pins the only
/// property that matters for faithfulness: a non-conforming impl is never
/// Verified and never silently skipped.
#[test]
fn test_trait_conformance_rejects_nonconforming_user_struct_impl() {
    let prepared = prepared_struct_conformance_context("Counter__get_bad", "6");
    assert!(
        prepared
            .trait_impl_decls
            .iter()
            .all(|d| !d.concrete_type.contains_opaque()),
        "prepare_context must resolve the Opaque user-struct concrete type to a Datatype; \
         got {:?}",
        prepared.trait_impl_decls
    );
    let result = conformance_verdict(&prepared);
    assert!(
        !result.is_verified(),
        "SOUNDNESS: a non-conforming user-struct trait impl (body returns 6, ensures requires 5) \
         must NOT verify — conformance must run and reject it, not silently skip. Got: {result:?}",
    );
    // Either a crisp counterexample (ideal) or a fail-closed Unknown attributed
    // to THIS conformance obligation (current ay datatype-model behavior). An
    // encoding `Error` or an unrelated obligation name would mean conformance
    // never actually exercised the impl, which would be a regression.
    match &result {
        VerifyResult::Counterexample {
            obligation_name, ..
        }
        | VerifyResult::Unknown {
            reason: obligation_name,
            ..
        } => assert!(
            obligation_name.contains("Slice6StructValued::get for Counter"),
            "non-Verified verdict must be attributed to the Counter conformance obligation; \
             got: {result:?}",
        ),
        other => panic!(
            "conformance must produce a Counterexample or fail-closed Unknown for the \
             non-conforming Counter impl, got: {other:?}",
        ),
    }
}

fn valued_u64_impl_decl(concrete_fn_name: &str) -> TraitImplDecl {
    TraitImplDecl {
        inherent_shadowed_methods: Default::default(),
        trait_name: "Slice6Valued".to_string(),
        concrete_type: TrustVcType::Uint { width: 64 },
        method_bindings: vec![("get_value".to_string(), concrete_fn_name.to_string())],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    }
}

fn helper_delegation_trait_decl() -> TraitDecl {
    TraitDecl {
        name: "Slice6HelperDelegation".to_string(),
        methods: vec![TraitMethodDecl {
            name: "check".to_string(),
            params: vec![],
            return_type: TrustVcType::Bool,
            requires: vec![],
            ensures: vec!["result".to_string()],
            has_default: false,
            default_body: None,
            default_ensures: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    }
}

fn helper_delegation_impl_decl(concrete_fn_name: &str) -> TraitImplDecl {
    TraitImplDecl {
        inherent_shadowed_methods: Default::default(),
        trait_name: "Slice6HelperDelegation".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![("check".to_string(), concrete_fn_name.to_string())],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    }
}

fn prepared_valued_impl_context(
    concrete_type: TrustVcType,
    impl_decl: TraitImplDecl,
    concrete_fn_name: &str,
    condition: &str,
) -> PreparedVerificationContext {
    let mut ctx = crate::vc::VerificationContext::new();
    ctx.register_trait_decl(valued_trait_decl());
    ctx.register_trait_impl(impl_decl);
    ctx.push_obligation(ProofObligation::assert("user_goal", "true"));
    ctx.declare_var_typed("self", concrete_type.clone());
    add_body_axiom(
        &mut ctx,
        concrete_fn_name,
        condition,
        vec![("self", concrete_type)],
        vec!["self"],
        &format!("{concrete_fn_name}(self)"),
        true,
    );
    prepare_context(&ctx).expect("valued impl context should prepare")
}

fn merge_prepared_contexts(
    prepared_contexts: Vec<PreparedVerificationContext>,
    trait_decl: TraitDecl,
    trait_impl_decls: Vec<TraitImplDecl>,
) -> PreparedVerificationContext {
    let mut prepared_iter = prepared_contexts.into_iter();
    let mut combined = prepared_iter
        .next()
        .expect("multi-impl regression requires at least one prepared context");
    let mut obligations = std::mem::take(&mut combined.obligations);
    let mut revealed_fns = std::mem::take(&mut combined.revealed_fns);
    let mut helper_function_contexts = std::mem::take(&mut combined.helper_function_contexts);
    if let Some(function_context) = combined.function_context.take() {
        helper_function_contexts.push(function_context);
    }

    for prepared in prepared_iter {
        obligations.extend(prepared.obligations);
        revealed_fns.extend(prepared.revealed_fns);
        if let Some(function_context) = prepared.function_context {
            helper_function_contexts.push(function_context);
        }
        helper_function_contexts.extend(prepared.helper_function_contexts);
    }

    combined.obligations = obligations;
    combined.variables = Vec::new();
    combined.function_context = None;
    combined.trait_decls = vec![trait_decl];
    combined.trait_impl_decls = trait_impl_decls;
    combined.verification_mode = VerificationMode::BodyLevel;
    combined.overflow_behavior = crate::vc::OverflowBehavior::Allow;
    combined.div0_behavior = crate::vc::Div0Behavior::default();
    combined.bitshift_behavior = crate::vc::BitshiftBehavior::default();
    combined.assert_by_scopes = HashMap::new();
    combined.forall_bound_vars = HashMap::new();
    combined.loop_guards = HashMap::new();
    combined.loop_modified_vars = HashMap::new();
    combined.has_collection_context = false;
    combined.revealed_fns = revealed_fns;
    combined.helper_function_contexts = helper_function_contexts;
    combined.struct_types = Vec::new();
    combined.type_invariants = HashMap::new();
    combined
}

#[test]
fn test_trait_conformance_uses_helper_body_axiom() {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    ctx.declare_var_typed("self", TrustVcType::Bool);
    ctx.register_trait_decl(helper_delegation_trait_decl());
    ctx.register_trait_impl(helper_delegation_impl_decl("Slice6BoolImpl__delegates"));
    ctx.declare_helper_function_typed(
        "Slice6Helper__truth",
        TrustVcType::Bool,
        vec![("self".to_string(), TrustVcType::Bool)],
    );
    ctx.push_obligation(
        ProofObligation::broadcast_assume(
            "__body_axiom_Slice6Helper__truth",
            "Slice6Helper__truth(self) == true",
        )
        .with_bound_vars(vec!["self".to_string()])
        .with_trigger_patterns(vec![vec!["Slice6Helper__truth(self)".to_string()]]),
    );
    add_body_axiom(
        ctx,
        "Slice6BoolImpl__delegates",
        "Slice6BoolImpl__delegates(self) == Slice6Helper__truth(self)",
        vec![("self", TrustVcType::Bool)],
        vec!["self"],
        "Slice6BoolImpl__delegates(self)",
        true,
    );
    ctx.push_obligation(ProofObligation::assert("user_goal", "true"));

    let result = pipeline_conformance_verdict(&pipeline);
    expect_verified(
        &result,
        "trait conformance should import helper body axioms that the impl body depends on",
    );
}

#[test]
fn test_trait_conformance_checks_multiple_impls() {
    let bool_impl_name = "Slice6BoolImpl__good_multi";
    let u64_impl_name = "Slice6U64Impl__bad_multi";
    let bool_prepared = prepared_valued_impl_context(
        TrustVcType::Bool,
        valued_impl_decl(bool_impl_name),
        bool_impl_name,
        "Slice6BoolImpl__good_multi(self) == true",
    );
    let u64_prepared = prepared_valued_impl_context(
        TrustVcType::Uint { width: 64 },
        valued_u64_impl_decl(u64_impl_name),
        u64_impl_name,
        "Slice6U64Impl__bad_multi(self) == false",
    );
    let combined = merge_prepared_contexts(
        vec![bool_prepared, u64_prepared],
        valued_trait_decl(),
        vec![
            valued_impl_decl(bool_impl_name),
            valued_u64_impl_decl(u64_impl_name),
        ],
    );

    let result = conformance_verdict(&combined);
    expect_counterexample(
        &result,
        "trait conformance should continue into later impls and report the failing one",
    );
    if let VerifyResult::Counterexample {
        obligation_name, ..
    } = &result
    {
        assert_eq!(
            obligation_name,
            "trait impl conformance Slice6Valued::get_value for u64"
        );
    }
}

/// ATTRIBUTION: `verify_prepared` (a FUNCTION's verdict) no longer folds in
/// other impls' conformance — but every impl is still CHECKED, and the failing
/// one is still REPORTED on its own obligation.
///
/// The soundness content is unchanged and is asserted below in full: the
/// non-conforming `u64` impl (body `false` against `ensures(result)`) is refuted,
/// named by its own conformance obligation, while the conforming `bool` sibling
/// passes. Only the blast radius moved: the file's unrelated `user_goal` is no
/// longer sunk by it. Folding it into every function's verdict is what made
/// upstream trait files unportable (see
/// the internal conformance-attribution design note).
#[test]
fn test_verify_prepared_checks_multiple_impls() {
    let bool_impl_name = "Slice6BoolImpl__good_multi_prepared";
    let u64_impl_name = "Slice6U64Impl__bad_multi_prepared";
    let bool_prepared = prepared_valued_impl_context(
        TrustVcType::Bool,
        valued_impl_decl(bool_impl_name),
        bool_impl_name,
        "Slice6BoolImpl__good_multi_prepared(self) == true",
    );
    let u64_prepared = prepared_valued_impl_context(
        TrustVcType::Uint { width: 64 },
        valued_u64_impl_decl(u64_impl_name),
        u64_impl_name,
        "Slice6U64Impl__bad_multi_prepared(self) == false",
    );
    let combined = merge_prepared_contexts(
        vec![bool_prepared, u64_prepared],
        valued_trait_decl(),
        vec![
            valued_impl_decl(bool_impl_name),
            valued_u64_impl_decl(u64_impl_name),
        ],
    );

    // The FUNCTION's own obligations discharge: it is not sunk by an impl it has
    // nothing to do with.
    expect_verified(
        &crate::encoder::AYEncoder::verify_prepared(&combined),
        "attribution: a function's verdict must not inherit another impl's conformance",
    );

    // ...and conformance still continues into LATER impls and reports the failing
    // one — the check itself is untouched.
    let result = conformance_verdict(&combined);
    expect_counterexample(
        &result,
        "conformance should continue into later impls and report the failing one",
    );
    if let VerifyResult::Counterexample {
        obligation_name, ..
    } = &result
    {
        assert_eq!(
            obligation_name,
            "trait impl conformance Slice6Valued::get_value for u64"
        );
    }
}
