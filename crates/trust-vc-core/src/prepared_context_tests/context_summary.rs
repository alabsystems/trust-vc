//! Prepared-context summary-field tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashMap;

use super::super::*;
use crate::ir::{TraitDecl, TraitImplDecl, TraitMethodDecl, TrustVcType};
use crate::ir_expr::{CollectionOp, CompareOp, TrustVcExpr};
use crate::vc::ProofObligation;

#[test]
fn test_has_collection_context_includes_assert_by_scopes() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.declare_var_typed(
        "s",
        TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })),
    );
    ctx.add_assert_by(
        "ab_test",
        "x > 0",
        vec![crate::vc::ProofObligation::assume(
            "seq_bound",
            "s.len() == 3",
        )],
    );

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");
    assert!(
        prepared.has_collection_context,
        "has_collection_context must be true when assert_by scoped obligations reference collections",
    );
}

#[test]
fn test_has_collection_context_from_assert_by_scopes_only() {
    let non_collection_expr = TrustVcExpr::Compare {
        op: CompareOp::Gt,
        left: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::Int { width: 32 },
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 0,
            ty: TrustVcType::Int { width: 32 },
        }),
    };
    let collection_expr = TrustVcExpr::CollectionOp {
        op: CollectionOp::Len,
        receiver: Box::new(TrustVcExpr::Var {
            name: "s".to_string(),
            ty: TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })),
        }),
        receiver_name: Some("s".to_string()),
        args: vec![],
        ty: TrustVcType::Uint { width: 64 },
    };

    let main_obligation = PreparedObligation {
        name: "main".to_string(),
        kind: ObligationKind::Assert,
        location: None,
        condition_origin: crate::vc::ConditionOrigin::LoweredFromCondition,
        bound_vars: None,
        trigger_patterns: None,
        prepared_triggers: None,
        solver_mode: None,
        is_opaque: false,
        is_inline: false,
        broadcast_group: None,
        invariant_namespace: None,

        trigger_inference_mode: None,
        broadcast_guard: None,
        raw_broadcast_guard_count: 0,
        step_meta: None,
        condition: "x > 0".to_string(),
        expr: non_collection_expr,
    };
    let scoped_obligation = PreparedObligation {
        name: "seq_len".to_string(),
        kind: ObligationKind::Assume,
        location: None,
        condition_origin: crate::vc::ConditionOrigin::LoweredFromCondition,
        bound_vars: None,
        trigger_patterns: None,
        prepared_triggers: None,
        solver_mode: None,
        is_opaque: false,
        is_inline: false,
        broadcast_group: None,
        invariant_namespace: None,

        trigger_inference_mode: None,
        broadcast_guard: None,
        raw_broadcast_guard_count: 0,
        step_meta: None,
        condition: "s.len()".to_string(),
        expr: collection_expr,
    };

    let mut assert_by_scopes = HashMap::new();
    assert_by_scopes.insert("ab_scope".to_string(), vec![scoped_obligation]);

    let variables = [VariableDecl {
        bounded_len: false,
        name: "x".to_string(),
        ty: TrustVcType::Int { width: 32 },
    }];
    let obligations = [main_obligation];

    let has_collection_from_vars = variables.iter().any(|variable| variable.ty.is_collection());
    let has_collection_from_obligations = obligations
        .iter()
        .any(|obligation| obligation.expr.references_collection());
    let has_collection_from_assert_by = assert_by_scopes.values().any(|scope| {
        scope
            .iter()
            .any(|obligation| obligation.expr.references_collection())
    });

    assert!(!has_collection_from_vars, "sanity: no collection variables");
    assert!(
        !has_collection_from_obligations,
        "sanity: no collection main obligations"
    );
    assert!(
        has_collection_from_assert_by,
        "assert_by_scopes must be checked for collection references (#2354)"
    );
}

#[test]
fn test_has_collection_context_false_when_no_collections() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assert("check", "x > 0"));

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");
    assert!(
        !prepared.has_collection_context,
        "has_collection_context must be false for pure integer context",
    );
}

#[test]
fn test_prepare_context_preserves_default_demand_inline_config() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assert("check", "x > 0"));

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");

    assert_eq!(
        prepared.demand_inline,
        crate::vc::DemandInlineConfig::new(),
        "prepare_context must preserve the default demand-inline retry policy",
    );
}

#[test]
fn test_prepare_context_preserves_custom_demand_inline_config() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assert("check", "x > 0"));
    ctx.set_demand_inline_enabled(false);
    ctx.set_demand_inline_depth(2);
    ctx.set_demand_inline_max_callees(7);

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");

    assert_eq!(
        prepared.demand_inline,
        crate::vc::DemandInlineConfig::new()
            .with_enabled(false)
            .with_depth_bound(2)
            .with_max_callees(7),
        "prepare_context must carry explicit demand-inline overrides into the prepared context",
    );
}

/// Regression test for #2425: concrete impl methods referenced by TraitImplDecl
/// must appear in helper_function_contexts even when NOT in helper_functions_typed.
/// This is the integration pipeline path — trait_registry adds impl decls but does
/// not add concrete methods to helper_functions_typed.
#[test]
fn test_synthesize_impl_method_contexts_from_trait_impl_decl() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assert("check", "x > 0"));

    ctx.register_trait_decl(TraitDecl {
        name: "Valued".to_string(),
        methods: vec![TraitMethodDecl {
            name: "get_value".to_string(),
            params: vec![],
            return_type: TrustVcType::Int { width: 32 },
            requires: vec![],
            ensures: vec!["result >= 0".to_string()],
            has_default: false,
            default_body: None,
            default_ensures: Vec::new(),
            generic_params: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    });

    // Register impl WITHOUT adding concrete fn to helper_functions_typed.
    // This matches the real pipeline (trait_registry::apply_registered_traits_to_context).
    ctx.register_trait_impl(TraitImplDecl {
        inherent_shadowed_methods: Default::default(),
        impl_group: Default::default(),
        trait_name: "Valued".to_string(),
        concrete_type: TrustVcType::Int { width: 32 },
        method_bindings: vec![("get_value".to_string(), "IntImpl__get_value".to_string())],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    });

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");

    let synthesized = prepared
        .helper_function_contexts
        .iter()
        .find(|fc| fc.name == "IntImpl__get_value");
    assert!(
        synthesized.is_some(),
        "synthesize_impl_method_contexts must produce FunctionContext for concrete impl method (#2425)"
    );

    let fc = synthesized.unwrap();
    assert_eq!(fc.params.len(), 1, "should have self param");
    assert_eq!(fc.params[0].0, "self");
    assert_eq!(fc.params[0].1, TrustVcType::Int { width: 32 });
    assert_eq!(fc.return_type, TrustVcType::Int { width: 32 });
}

/// Regression test (assoc_type_impls): a trait method param typed `Self::X`
/// must be normalized to the impl's `type X = T` binding when the impl-method
/// context is synthesized. Without the normalization the synthesized context
/// carries `Opaque("Self::X")` and `record_function_context_metadata` fails the
/// WHOLE file closed ("Unsupported param type ...: Self::Output"), sinking
/// unrelated functions. Exposed by ee0962e (user-struct concrete-type resolve
/// un-skipping such impls); root cause is the missing projection normalization.
#[test]
fn test_synthesize_impl_method_contexts_resolves_assoc_type_projections() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assert("check", "x > 0"));

    ctx.register_trait_decl(TraitDecl {
        name: "OutputPredicate".to_string(),
        methods: vec![TraitMethodDecl {
            name: "accepts".to_string(),
            params: vec![(
                "output".to_string(),
                TrustVcType::Opaque("Self::Output".to_string()),
            )],
            return_type: TrustVcType::Bool,
            requires: vec![],
            ensures: vec![],
            has_default: false,
            default_body: None,
            default_ensures: Vec::new(),
            generic_params: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    });

    ctx.register_trait_impl(
        TraitImplDecl::new(
            "OutputPredicate",
            TrustVcType::Int { width: 32 },
            vec![("accepts".to_string(), "IntImpl__accepts".to_string())],
        )
        .with_assoc_type_bindings(vec![("Output".to_string(), TrustVcType::MathInt)]),
    );

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");
    let fc = prepared
        .helper_function_contexts
        .iter()
        .find(|fc| fc.name == "IntImpl__accepts")
        .expect("impl method context must be synthesized");
    assert_eq!(fc.params.len(), 2, "self + output params");
    assert_eq!(
        fc.params[1].1,
        TrustVcType::MathInt,
        "Self::Output must be normalized to the impl's `type Output = int` binding"
    );
}

/// An UNRESOLVABLE projection (no matching binding) must stay Opaque so the
/// registration guard keeps failing closed — resolution never invents a type.
#[test]
fn test_resolve_assoc_projections_leaves_unbound_projection_opaque() {
    let decl = TraitImplDecl::new("T", TrustVcType::Bool, Vec::new())
        .with_assoc_type_bindings(vec![("Output".to_string(), TrustVcType::MathInt)]);
    assert_eq!(
        decl.resolve_assoc_projections(&TrustVcType::Opaque("Self::Other".to_string())),
        TrustVcType::Opaque("Self::Other".to_string())
    );
    // Nested container resolution.
    assert_eq!(
        decl.resolve_assoc_projections(&TrustVcType::Seq(Box::new(TrustVcType::Opaque(
            "Self::Output".to_string()
        )))),
        TrustVcType::Seq(Box::new(TrustVcType::MathInt))
    );
}

/// A3: the fully-qualified spelling `<Concrete as Trait>::X` resolves exactly
/// when it names THIS impl's own concrete type and trait (equivalent to
/// `Self::X`); a projection naming a DIFFERENT type or trait stays Opaque
/// (fail-closed), because the per-trait UF slot fixes its sort from the declared
/// type and a foreign resolution here could sort-diverge.
#[test]
fn test_resolve_assoc_projections_resolves_own_qualified_projection() {
    let decl = TraitImplDecl::new("T", TrustVcType::Opaque("S".to_string()), Vec::new())
        .with_assoc_type_bindings(vec![("X".to_string(), TrustVcType::Uint { width: 8 })]);
    // `<S as T>::X` names this impl (self type `S`, trait `T`) → resolves to u8.
    assert_eq!(
        decl.resolve_assoc_projections(&TrustVcType::Opaque("<S as T>::X".to_string())),
        TrustVcType::Uint { width: 8 }
    );
    // A different concrete type → left Opaque (fail-closed).
    assert_eq!(
        decl.resolve_assoc_projections(&TrustVcType::Opaque("<Other as T>::X".to_string())),
        TrustVcType::Opaque("<Other as T>::X".to_string())
    );
    // A different trait → left Opaque (fail-closed).
    assert_eq!(
        decl.resolve_assoc_projections(&TrustVcType::Opaque("<S as U>::X".to_string())),
        TrustVcType::Opaque("<S as U>::X".to_string())
    );
    // An unbound assoc on this impl → left Opaque (fail-closed).
    assert_eq!(
        decl.resolve_assoc_projections(&TrustVcType::Opaque("<S as T>::Y".to_string())),
        TrustVcType::Opaque("<S as T>::Y".to_string())
    );
}

/// When the concrete fn is already in helper_functions_typed, synthesize should skip it.
#[test]
fn test_synthesize_impl_method_contexts_skips_existing_helpers() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assert("check", "x > 0"));

    ctx.register_trait_decl(TraitDecl {
        name: "Valued".to_string(),
        methods: vec![TraitMethodDecl {
            name: "get_value".to_string(),
            params: vec![],
            return_type: TrustVcType::Int { width: 32 },
            requires: vec![],
            ensures: vec![],
            has_default: false,
            default_body: None,
            default_ensures: Vec::new(),
            generic_params: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    });

    // Pre-register the concrete fn in helper_functions_typed (mimics add_body_axiom path)
    ctx.declare_helper_function_typed(
        "IntImpl__get_value",
        TrustVcType::Int { width: 32 },
        vec![("self".to_string(), TrustVcType::Int { width: 32 })],
    );

    ctx.register_trait_impl(TraitImplDecl {
        inherent_shadowed_methods: Default::default(),
        impl_group: Default::default(),
        trait_name: "Valued".to_string(),
        concrete_type: TrustVcType::Int { width: 32 },
        method_bindings: vec![("get_value".to_string(), "IntImpl__get_value".to_string())],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    });

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");

    // Should appear exactly once (from helper_functions_typed, not duplicated by synthesize)
    let count = prepared
        .helper_function_contexts
        .iter()
        .filter(|fc| fc.name == "IntImpl__get_value")
        .count();
    assert_eq!(
        count, 1,
        "concrete fn already in helper_functions_typed must not be duplicated (#2425)"
    );
}

/// Multiple TraitImplDecls binding the same concrete fn must not produce duplicates.
#[test]
fn test_synthesize_deduplicates_across_multiple_trait_impls() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assert("check", "x > 0"));

    // Two different traits, both binding to the same concrete function name.
    ctx.register_trait_decl(TraitDecl {
        name: "TraitA".to_string(),
        methods: vec![TraitMethodDecl {
            name: "do_thing".to_string(),
            params: vec![],
            return_type: TrustVcType::Bool,
            requires: vec![],
            ensures: vec![],
            has_default: false,
            default_body: None,
            default_ensures: Vec::new(),
            generic_params: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    });
    ctx.register_trait_decl(TraitDecl {
        name: "TraitB".to_string(),
        methods: vec![TraitMethodDecl {
            name: "do_thing".to_string(),
            params: vec![],
            return_type: TrustVcType::Bool,
            requires: vec![],
            ensures: vec![],
            has_default: false,
            default_body: None,
            default_ensures: Vec::new(),
            generic_params: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    });

    ctx.register_trait_impl(TraitImplDecl {
        inherent_shadowed_methods: Default::default(),
        impl_group: Default::default(),
        trait_name: "TraitA".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![("do_thing".to_string(), "SharedImpl__do_thing".to_string())],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    });
    ctx.register_trait_impl(TraitImplDecl {
        inherent_shadowed_methods: Default::default(),
        impl_group: Default::default(),
        trait_name: "TraitB".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![("do_thing".to_string(), "SharedImpl__do_thing".to_string())],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    });

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");

    let count = prepared
        .helper_function_contexts
        .iter()
        .filter(|fc| fc.name == "SharedImpl__do_thing")
        .count();
    assert_eq!(
        count, 1,
        "same concrete fn from multiple trait impls must be deduplicated (#2425)"
    );
}

/// Trait impls with opaque concrete types must be skipped by synthesis — ay has
/// no sort for opaque types, so attempting to register a UF with opaque self
/// would crash at solver setup.
#[test]
fn test_synthesize_skips_opaque_concrete_type() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assert("check", "x > 0"));

    ctx.register_trait_decl(TraitDecl {
        name: "Valued".to_string(),
        methods: vec![TraitMethodDecl {
            name: "get_value".to_string(),
            params: vec![],
            return_type: TrustVcType::Int { width: 32 },
            requires: vec![],
            ensures: vec![],
            has_default: false,
            default_body: None,
            default_ensures: Vec::new(),
            generic_params: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    });

    // Opaque concrete type — no ay sort available.
    ctx.register_trait_impl(TraitImplDecl {
        inherent_shadowed_methods: Default::default(),
        impl_group: Default::default(),
        trait_name: "Valued".to_string(),
        concrete_type: TrustVcType::Opaque("Widget".to_string()),
        method_bindings: vec![("get_value".to_string(), "WidgetImpl__get_value".to_string())],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    });

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");

    let found = prepared
        .helper_function_contexts
        .iter()
        .any(|fc| fc.name == "WidgetImpl__get_value");
    assert!(
        !found,
        "synthesize must skip impls with opaque concrete types (#2425)"
    );
}

/// Trait method with additional params beyond self — synthesis must prepend self
/// and extend with the method's own params.
#[test]
fn test_synthesize_multi_param_method() {
    let mut ctx = VerificationContext::new();
    ctx.declare_var_typed("x", TrustVcType::Int { width: 32 });
    ctx.push_obligation(ProofObligation::assert("check", "x > 0"));

    ctx.register_trait_decl(TraitDecl {
        name: "Updater".to_string(),
        methods: vec![TraitMethodDecl {
            name: "update".to_string(),
            params: vec![
                ("key".to_string(), TrustVcType::Int { width: 32 }),
                ("val".to_string(), TrustVcType::Bool),
            ],
            return_type: TrustVcType::Bool,
            requires: vec![],
            ensures: vec![],
            has_default: false,
            default_body: None,
            default_ensures: Vec::new(),
            generic_params: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    });

    ctx.register_trait_impl(TraitImplDecl {
        inherent_shadowed_methods: Default::default(),
        impl_group: Default::default(),
        trait_name: "Updater".to_string(),
        concrete_type: TrustVcType::Int { width: 64 },
        method_bindings: vec![("update".to_string(), "I64Impl__update".to_string())],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    });

    let prepared = prepare_context(&ctx).expect("prepare_context should succeed");

    let fc = prepared
        .helper_function_contexts
        .iter()
        .find(|fc| fc.name == "I64Impl__update")
        .expect("synthesized FC must exist for multi-param method");

    assert_eq!(fc.params.len(), 3, "self + 2 method params");
    assert_eq!(fc.params[0].0, "self");
    assert_eq!(fc.params[0].1, TrustVcType::Int { width: 64 });
    assert_eq!(fc.params[1].0, "key");
    assert_eq!(fc.params[1].1, TrustVcType::Int { width: 32 });
    assert_eq!(fc.params[2].0, "val");
    assert_eq!(fc.params[2].1, TrustVcType::Bool);
    assert_eq!(fc.return_type, TrustVcType::Bool);
}
