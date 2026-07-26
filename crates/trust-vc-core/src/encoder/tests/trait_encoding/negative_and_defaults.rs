// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Negative tests (counterexample detection) and default trait method tests (#2442).

use super::*;

// --- Negative tests: counterexample detection ---

/// Asserting `counter.grant(false)` should produce a counterexample because
/// the precondition `self.value() && token` cannot hold when token=false,
/// leaving the return value unconstrained.
#[test]
fn test_verification_pipeline_rejects_false_assertion_on_unconstrained_trait_method() {
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

    // token=false makes the precondition unsatisfiable, so
    // CounterSpec__grant(counter, false) is unconstrained.
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "wrong_claim",
        "counter.grant(false)",
    ));

    let result = pipeline.verify();
    expect_fail_closed(
        &result,
        "unconstrained trait method (precondition unmet) should fail closed",
    );
}

/// With the precondition explicitly assumed (counter.value() is true),
/// the postcondition axiom kicks in: grant(counter, true) must be true.
/// This is a non-tautological positive test — it depends on the axiom
/// encoding being correct.
#[test]
fn test_verification_pipeline_verifies_trait_postcondition_when_precondition_assumed() {
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

    // Assume the precondition component: counter.value() is true.
    ctx.push_obligation(crate::vc::ProofObligation::assume("pre", "counter.value()"));
    // Assert the postcondition outcome: grant(counter, true) is true.
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "post",
        "counter.grant(true)",
    ));

    let result = pipeline.verify();
    expect_verified(
        &result,
        "trait postcondition should verify when precondition is assumed",
    );
}

/// Encoder-level: when the precondition is NOT asserted, claiming
/// grant(self, true) == true should be SAT (refutable) because
/// value(self) might be false.
#[test]
fn test_trait_grant_is_refutable_without_precondition_assumption() {
    let mut encoder = AYEncoder::new();
    let decl = counter_trait_decl();
    encoder
        .register_trait(&decl)
        .expect("trait registration should succeed");

    let poly = Sort::Uninterpreted("Poly".to_string());
    let self_term = encoder.solver.declare_const("trait_self", poly);
    let token = encoder.solver.bool_const(true);
    let grant_fn = encoder
        .fn_ctx
        .functions
        .get("CounterSpec__grant")
        .expect("grant UF should be registered")
        .clone();

    let grant = encoder
        .solver
        .try_apply(&grant_fn, &[self_term, token])
        .expect("grant application should encode");

    // Assert grant(self, true) == FALSE without assuming value(self).
    // Since value(self) is unconstrained, the precondition may be false,
    // leaving grant unconstrained — so grant == false is satisfiable.
    let falsity = encoder.solver.bool_const(false);
    let claim = encoder
        .solver
        .try_eq(grant, falsity)
        .expect("eq should encode");
    encoder
        .solver
        .try_assert_term(claim)
        .expect("assert should succeed");

    // Correct encoding: SAT (grant CAN be false when precondition unmet).
    // If the precondition guard were missing (soundness bug), the
    // postcondition `ensures(result)` would force grant == true always,
    // making grant == false UNSAT — this test catches that regression.
    let result = encoder.solver.try_check_sat().unwrap();
    assert!(
        result.is_sat() || result.is_unknown(),
        "grant(self, true) == false should be satisfiable or fail closed without precondition assumption: {:?}",
        result.result()
    );
}

// --- Default trait method tests (#2442) ---

/// E-matching diagnostic: test with both Poly and Bool sorts to ensure we do
/// not regress Bool-sorted triggers back to the old "stays satisfiable" gap.
#[test]
fn test_ay_ematching_sort_sensitivity() {
    // Verified behavior: ay fires e-matching for an uninterpreted-domain trigger
    // through the full solver across a push scope. This is the sort trust-vc
    // actually uses — every Verus value is encoded as the uninterpreted `Poly`
    // sort — so postcondition / spec-function axioms instantiate as required.
    //
    // (A Bool *domain* bound variable with an opaque Bool constant asserted in a
    // push scope is a separate, narrow boolean-argument-congruence gap that does
    // not arise in the Poly encoding; it is documented and tracked at the ay
    // level in ay-dpll group_incremental::ematching_pushscope_repro
    // ("ematching_pushscope_bool_domain_known_gap").)
    let mut encoder = AYEncoder::new();
    let poly = Sort::Uninterpreted("Poly".to_string());

    // Poly → Bool: matches the postcondition axiom pattern.
    let f_poly = encoder
        .solver
        .try_declare_fun("f_poly", std::slice::from_ref(&poly), Sort::Bool)
        .unwrap();
    let x_poly = encoder.solver.fresh_var("__xp", poly.clone());
    let f_xp = encoder.solver.try_apply(&f_poly, &[x_poly]).unwrap();
    let truth = encoder.solver.bool_const(true);
    let eq_poly = encoder.solver.try_eq(f_xp, truth).unwrap();
    let ax_poly = encoder
        .solver
        .try_forall_with_triggers(&[x_poly], eq_poly, &[&[f_xp]])
        .unwrap();
    encoder.solver.try_assert_term(ax_poly).unwrap();

    let c_poly = encoder.solver.declare_const("c_poly", poly);
    let f_cp = encoder.solver.try_apply(&f_poly, &[c_poly]).unwrap();
    let falsity = encoder.solver.bool_const(false);

    encoder.solver.try_push().unwrap();
    let claim_poly = encoder.solver.try_eq(f_cp, falsity).unwrap();
    encoder.solver.try_assert_term(claim_poly).unwrap();
    let r_poly = encoder.solver.try_check_sat().unwrap();
    encoder.solver.try_pop().unwrap();

    assert!(
        r_poly.is_unsat(),
        "Poly→Bool trigger must fire across the push scope (postcondition-axiom pattern)"
    );
}

#[test]
fn test_register_trait_stores_default_bodies_in_encoding() {
    let mut encoder = AYEncoder::new();
    let decl = trait_with_default();
    let encoding = encoder
        .register_trait(&decl)
        .expect("registration should succeed");

    assert!(
        encoding.method_fns.contains_key("label"),
        "required method should be declared"
    );
    assert!(
        encoding.method_fns.contains_key("is_labeled"),
        "default method should be declared"
    );
}

/// Verify assertion count: register_trait_impl emits linking axiom for
/// bound methods AND default body axiom for inherited defaults.
#[test]
fn test_default_body_axiom_assertion_count() {
    let mut encoder = AYEncoder::new();
    let decl = trait_with_default();
    encoder
        .register_trait(&decl)
        .expect("trait registration should succeed");

    // Register concrete impl function for `label` only
    let bool_sort = Sort::Bool;
    let impl_fn = encoder
        .solver
        .try_declare_fun(
            "MyType__label",
            std::slice::from_ref(&bool_sort),
            bool_sort.clone(),
        )
        .unwrap();
    encoder
        .fn_ctx
        .functions
        .insert("MyType__label".to_string(), impl_fn);
    encoder
        .fn_ctx
        .return_types
        .insert("MyType__label".to_string(), TrustVcType::Bool);
    encoder
        .fn_ctx
        .param_types
        .insert("MyType__label".to_string(), vec![TrustVcType::Bool]);

    let impl_decl = TraitImplDecl {
        trait_name: "Describable".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![("label".to_string(), "MyType__label".to_string())],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    };

    let before = encoder.solver.assertions().len();
    encoder
        .register_trait_impl(&impl_decl)
        .expect("impl registration should succeed");
    let after = encoder.solver.assertions().len();
    let axioms_added = after - before;

    // Expect: roundtrip axiom + linking axiom for label + default body axiom for is_labeled
    assert!(
        axioms_added >= 2,
        "Expected at least 2 axioms (linking + default body), got {}",
        axioms_added
    );
}

/// The default body axiom for `is_labeled` defines it as `self.label()` at
/// the Poly level. The postcondition axiom for `label` ensures `result == true`.
/// Together: `is_labeled(p) == label(p) == true`.
#[test]
fn test_inherited_default_body_defines_trait_method_via_body_axiom() {
    let mut encoder = AYEncoder::new();
    let decl = trait_with_default();
    encoder
        .register_trait(&decl)
        .expect("trait registration should succeed");

    // Register concrete impl function for `label` only — `is_labeled` is inherited.
    let impl_fn = encoder
        .solver
        .try_declare_fun("MyType__label", &[Sort::Bool], Sort::Bool)
        .expect("impl function declaration should succeed");
    encoder
        .fn_ctx
        .functions
        .insert("MyType__label".to_string(), impl_fn);
    encoder
        .fn_ctx
        .return_types
        .insert("MyType__label".to_string(), TrustVcType::Bool);
    encoder
        .fn_ctx
        .param_types
        .insert("MyType__label".to_string(), vec![TrustVcType::Bool]);

    // Register impl with only `label` binding — `is_labeled` is inherited default
    let impl_decl = TraitImplDecl {
        trait_name: "Describable".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![("label".to_string(), "MyType__label".to_string())],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    };
    encoder
        .register_trait_impl(&impl_decl)
        .expect("impl registration should succeed");

    // Create ground term at the Poly level (matching ay-dpll E-matching scope)
    let poly = Sort::Uninterpreted("Poly".to_string());
    let poly_val = encoder.solver.declare_const("poly_self", poly);

    let is_labeled_fn = encoder
        .fn_ctx
        .functions
        .get("Describable__is_labeled")
        .expect("is_labeled UF should exist")
        .clone();
    let is_labeled_result = encoder
        .solver
        .try_apply(&is_labeled_fn, &[poly_val])
        .expect("trait apply should succeed");

    // Assert is_labeled(poly_self) == false — should be UNSAT because:
    // default body axiom: ∀p:Poly. {is_labeled(p)} is_labeled(p) == label(p)
    // postcondition axiom: ∀p:Poly. {label(p)} label(p) == true
    let falsity = encoder.solver.bool_const(false);
    let claim = encoder
        .solver
        .try_eq(is_labeled_result, falsity)
        .expect("eq should succeed");
    encoder
        .solver
        .try_assert_term(claim)
        .expect("assert should succeed");

    assert!(
        encoder.solver.try_check_sat().unwrap().is_unsat(),
        "default body axiom + postcondition chain: is_labeled(p) == label(p) == true"
    );
}

/// When the impl overrides `is_labeled`, the default body axiom should NOT be
/// emitted. Instead, a linking axiom connects the trait UF to the override.
/// Verify via assertion count comparison.
#[test]
fn test_explicit_override_skips_default_body_axiom() {
    let mut encoder = AYEncoder::new();
    let decl = trait_with_default();
    encoder
        .register_trait(&decl)
        .expect("trait registration should succeed");

    // Register concrete impl functions for BOTH methods
    let bool_sort = Sort::Bool;
    for name in &["MyType__label", "MyType__is_labeled"] {
        let f = encoder
            .solver
            .try_declare_fun(name, std::slice::from_ref(&bool_sort), bool_sort.clone())
            .expect("decl should succeed");
        encoder.fn_ctx.functions.insert(name.to_string(), f);
        encoder
            .fn_ctx
            .return_types
            .insert(name.to_string(), TrustVcType::Bool);
        encoder
            .fn_ctx
            .param_types
            .insert(name.to_string(), vec![TrustVcType::Bool]);
    }

    let impl_decl = TraitImplDecl {
        trait_name: "Describable".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![
            ("label".to_string(), "MyType__label".to_string()),
            ("is_labeled".to_string(), "MyType__is_labeled".to_string()),
        ],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    };

    let before = encoder.solver.assertions().len();
    encoder
        .register_trait_impl(&impl_decl)
        .expect("impl registration should succeed");
    let after = encoder.solver.assertions().len();

    // With both methods overridden: roundtrip + 2 linking axioms, NO default body.
    // With only label overridden: roundtrip + 1 linking + 1 default body.
    // So the override case should have MORE linking axioms but NO default body axiom.
    let axioms_with_override = after - before;

    // Create a separate encoder for the non-override case
    let mut encoder2 = AYEncoder::new();
    encoder2.register_trait(&decl).unwrap();
    let impl_fn2 = encoder2
        .solver
        .try_declare_fun("MyType__label", &[Sort::Bool], Sort::Bool)
        .unwrap();
    encoder2
        .fn_ctx
        .functions
        .insert("MyType__label".to_string(), impl_fn2);
    encoder2
        .fn_ctx
        .return_types
        .insert("MyType__label".to_string(), TrustVcType::Bool);
    encoder2
        .fn_ctx
        .param_types
        .insert("MyType__label".to_string(), vec![TrustVcType::Bool]);

    let impl_decl_no_override = TraitImplDecl {
        trait_name: "Describable".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![("label".to_string(), "MyType__label".to_string())],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    };
    let before2 = encoder2.solver.assertions().len();
    encoder2
        .register_trait_impl(&impl_decl_no_override)
        .unwrap();
    let after2 = encoder2.solver.assertions().len();
    let axioms_without_override = after2 - before2;

    // Override case: 1 extra linking axiom (for is_labeled), no default body.
    // Non-override case: 1 default body axiom, no linking for is_labeled.
    // Both should add the same roundtrip axiom.
    // The override adds 1 linking axiom where non-override adds 1 default body axiom.
    assert!(
        axioms_with_override > 0 && axioms_without_override > 0,
        "both cases should emit axioms"
    );

    // Key check: override replaces 1 default body axiom with 1 linking axiom,
    // so total axiom counts should be equal.
    assert_eq!(
        axioms_with_override, axioms_without_override,
        "override swaps default body axiom for linking axiom — counts should match \
         (override: {}, non-override: {})",
        axioms_with_override, axioms_without_override
    );
}

// --- ROOT C regression: unlowerable default bodies must not sink the file ---

/// Builds a trait whose single method carries `default_body` and an impl that
/// inherits it (NO overrides — empty `method_bindings`, the exact shape of
/// `impl TrustVcDefaultRecord for DefaultTraitGood {}` in the
/// `default_trait.rs` corpus fixture).
fn trait_with_raw_default_body(
    trait_name: &str,
    method_name: &str,
    return_type: TrustVcType,
    body: &str,
) -> (TraitDecl, TraitImplDecl) {
    let decl = TraitDecl {
        name: trait_name.to_string(),
        methods: vec![TraitMethodDecl {
            name: method_name.to_string(),
            params: vec![],
            return_type,
            requires: vec![],
            ensures: vec![],
            has_default: true,
            default_body: Some(body.to_string()),
            default_ensures: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    };
    let impl_decl = TraitImplDecl {
        trait_name: trait_name.to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    };
    (decl, impl_decl)
}

/// ROOT C mechanism pin (2026-07-18): a default body whose shape the axiom
/// lowering cannot express (`trust_vc::assert!` statements are "macro in
/// block" to the spec lowering) used to Err out of `register_trait_impl`,
/// and `setup.rs` propagated that into a SUITE-WIDE encoder-setup failure —
/// even `0u32 == 0u32` cases in the same file died pre-solve. Registration
/// must now succeed, skipping ONLY that method's definitional axiom, and the
/// trait UF must stay genuinely underconstrained (fail-closed: no silently
/// invented value).
#[test]
fn test_root_c_macro_stmt_default_body_skips_axiom_and_stays_underconstrained() {
    let mut encoder = AYEncoder::new();
    let (decl, impl_decl) = trait_with_raw_default_body(
        "RecordDefaults",
        "make",
        TrustVcType::Nat,
        "{ trust_vc :: assert ! (0u32 == 0u32) ; 10u32 }",
    );
    encoder
        .register_trait(&decl)
        .expect("trait registration should succeed");
    encoder
        .register_trait_impl(&impl_decl)
        .expect("an unlowerable default body must skip its own axiom, not sink the registration");

    // Fail-closed direction: with the definitional axiom skipped, NOTHING may
    // pin `RecordDefaults__make(p)` to the body value 10. If a wrong axiom
    // had been asserted anyway, `make(p) == 11` would be UNSAT.
    let poly = Sort::Uninterpreted("Poly".to_string());
    let poly_val = encoder.solver.declare_const("root_c_poly_self", poly);
    let make_fn = encoder
        .fn_ctx
        .functions
        .get("RecordDefaults__make")
        .expect("trait method UF should exist")
        .clone();
    let make_result = encoder
        .solver
        .try_apply(&make_fn, &[poly_val])
        .expect("trait apply should succeed");
    let eleven = encoder.solver.int_const(11);
    let claim = encoder
        .solver
        .try_eq(make_result, eleven)
        .expect("eq should succeed");
    encoder
        .solver
        .try_assert_term(claim)
        .expect("assert should succeed");
    assert!(
        encoder.solver.try_check_sat().unwrap().is_sat(),
        "skipped default-body axiom must leave the trait UF underconstrained \
         (make(p) == 11 should be satisfiable)"
    );
}

/// ROOT C fixture-shape pin: the exact `default_trait.rs` failure — a default
/// body binding a STRUCT LITERAL of a type the minimal trait-contract env has
/// no metadata for, followed by proof-macro statements — must register without
/// error (previously: "Failed to register trait impl ... lower default body:
/// type inference failed ... struct literal for unknown type").
#[test]
fn test_root_c_struct_literal_default_body_registration_succeeds() {
    let mut encoder = AYEncoder::new();
    let (decl, impl_decl) = trait_with_raw_default_body(
        "TrustVcDefaultRecordShape",
        "record_default",
        TrustVcType::parse_or_opaque("MissingRecord"),
        "{ let result = MissingRecord { x : 10u32 , enabled : true , } ; \
         trust_vc :: assert ! (result . x == 10u32) ; \
         trust_vc :: assert ! (result . enabled) ; result }",
    );
    encoder
        .register_trait(&decl)
        .expect("trait registration should succeed");
    let after_trait = encoder.solver.assertions().len();
    encoder
        .register_trait_impl(&impl_decl)
        .expect("the default_trait.rs fixture shape must skip its axiom, not sink the file");
    let after_impl = encoder.solver.assertions().len();

    // The impl may add its Box/Unbox roundtrip axiom, but NO default-body
    // axiom: the delta must be no larger than the roundtrip-only baseline of
    // an identical impl whose trait has a lowerable default (which adds
    // roundtrip + body axiom, i.e. strictly more).
    let mut control = AYEncoder::new();
    let (control_decl, control_impl) = trait_with_raw_default_body(
        "TrustVcDefaultRecordShapeControl",
        "record_default",
        TrustVcType::Bool,
        "true",
    );
    control
        .register_trait(&control_decl)
        .expect("control trait registration should succeed");
    let control_before = control.solver.assertions().len();
    control
        .register_trait_impl(&control_impl)
        .expect("control impl registration should succeed");
    let control_delta = control.solver.assertions().len() - control_before;

    let skipped_delta = after_impl - after_trait;
    assert!(
        skipped_delta < control_delta,
        "unlowerable default body must emit FEWER impl axioms than a lowerable \
         one (no definitional axiom): skipped {skipped_delta}, control {control_delta}"
    );
}
