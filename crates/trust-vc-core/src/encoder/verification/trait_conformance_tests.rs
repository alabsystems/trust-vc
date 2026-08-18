//! Trait impl conformance regression tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::encoder::tests::{
    conformance_verdict, expect_counterexample, expect_encodes_without_error, expect_verified,
};
use crate::encoder::VerifyResult;
use crate::ir::{TraitDecl, TraitImplDecl, TraitMethodDecl, TrustVcType};
use crate::prepared_context::prepare_context;
use crate::vc::ProofObligation;

/// [`conformance_verdict`] for a pipeline-built context.
pub(super) fn pipeline_conformance_verdict(
    pipeline: &crate::verification_bridge::VerificationPipeline,
) -> VerifyResult {
    crate::encoder::tests::context_conformance_verdict(pipeline.context())
}

pub(super) fn valued_trait_decl() -> TraitDecl {
    TraitDecl {
        name: "Slice6Valued".to_string(),
        methods: vec![TraitMethodDecl {
            name: "get_value".to_string(),
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

pub(super) fn valued_impl_decl(concrete_fn_name: &str) -> TraitImplDecl {
    TraitImplDecl {
        trait_name: "Slice6Valued".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![("get_value".to_string(), concrete_fn_name.to_string())],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    }
}

fn gated_trait_decl() -> TraitDecl {
    TraitDecl {
        name: "Slice6Gate".to_string(),
        methods: vec![TraitMethodDecl {
            name: "grant".to_string(),
            params: vec![("token".to_string(), TrustVcType::Bool)],
            return_type: TrustVcType::Bool,
            requires: vec!["token".to_string()],
            ensures: vec!["result".to_string()],
            has_default: false,
            default_body: None,
            default_ensures: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    }
}

fn gated_impl_decl(concrete_fn_name: &str) -> TraitImplDecl {
    TraitImplDecl {
        trait_name: "Slice6Gate".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![("grant".to_string(), concrete_fn_name.to_string())],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    }
}

pub(super) fn add_body_axiom(
    ctx: &mut crate::vc::VerificationContext,
    function_name: &str,
    condition: &str,
    params: Vec<(&str, TrustVcType)>,
    bound_vars: Vec<&str>,
    trigger: &str,
    opaque: bool,
) {
    ctx.declare_helper_function_typed(
        function_name,
        TrustVcType::Bool,
        params
            .iter()
            .map(|(name, ty)| ((*name).to_string(), ty.clone()))
            .collect(),
    );
    ctx.push_obligation(
        ProofObligation::broadcast_assume(format!("__body_axiom_{function_name}"), condition)
            .with_bound_vars(bound_vars.into_iter().map(str::to_string).collect())
            .with_trigger_patterns(vec![vec![trigger.to_string()]])
            .with_opaque(opaque),
    );
}

#[test]
fn test_trait_conformance_verifies_good_opaque_impl_body() {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    ctx.declare_var_typed("self", TrustVcType::Bool);
    ctx.register_trait_decl(valued_trait_decl());
    ctx.register_trait_impl(valued_impl_decl("Slice6BoolImpl__good"));
    add_body_axiom(
        ctx,
        "Slice6BoolImpl__good",
        "Slice6BoolImpl__good(self) == true",
        vec![("self", TrustVcType::Bool)],
        vec!["self"],
        "Slice6BoolImpl__good(self)",
        true,
    );
    ctx.push_obligation(crate::vc::ProofObligation::assert("user_goal", "true"));

    let result = pipeline_conformance_verdict(&pipeline);
    expect_verified(
        &result,
        "trait conformance should verify a good opaque impl body",
    );
    expect_verified(
        &pipeline.verify(),
        "a conforming impl must not disturb an unrelated obligation",
    );
}

#[test]
fn test_trait_conformance_rejects_bad_impl_body() {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    ctx.declare_var_typed("self", TrustVcType::Bool);
    ctx.register_trait_decl(valued_trait_decl());
    ctx.register_trait_impl(valued_impl_decl("Slice6BoolImpl__bad"));
    add_body_axiom(
        ctx,
        "Slice6BoolImpl__bad",
        "Slice6BoolImpl__bad(self) == false",
        vec![("self", TrustVcType::Bool)],
        vec!["self"],
        "Slice6BoolImpl__bad(self)",
        true,
    );
    // Unrelated obligation: it is NO LONGER SUNK by the bad impl (attribution) —
    // the bad impl is refuted on its OWN conformance obligation below.
    ctx.push_obligation(crate::vc::ProofObligation::assert("user_goal", "true"));

    let result = pipeline_conformance_verdict(&pipeline);
    expect_counterexample(&result, "trait conformance should reject a bad impl body");
    if let VerifyResult::Counterexample {
        obligation_name, ..
    } = &result
    {
        assert_eq!(
            obligation_name,
            "trait impl conformance Slice6Valued::get_value for bool"
        );
    }
}

/// A CONFORMING impl whose body was CAPTURED from source (no body axiom in
/// scope, as when the verified function never references the impl method) must
/// verify: the conformance pass binds the result to the captured body's actual
/// value (`true`) and discharges the trait `ensures(result)`. This is the exact
/// generic/inherited-result over-rejection the fix closes — pre-fix the result
/// stayed an unconstrained `@Poly` and a conforming impl was rejected.
#[test]
fn test_trait_conformance_verifies_captured_body_without_body_axiom() {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    ctx.register_trait_decl(valued_trait_decl());
    ctx.register_trait_impl(valued_impl_decl("Slice6BoolImpl__cap_good"));
    // Declare the impl-method signature so `concrete_fn(..)` lowers, but do NOT
    // add its body axiom — exercising the captured-body binding path.
    ctx.declare_helper_function_typed(
        "Slice6BoolImpl__cap_good",
        TrustVcType::Bool,
        vec![("self".to_string(), TrustVcType::Bool)],
    );
    ctx.register_trait_impl_method_body(
        "Slice6BoolImpl__cap_good".to_string(),
        crate::ir::ConformanceMethodBody::new("true", 0),
    );
    ctx.push_obligation(crate::vc::ProofObligation::assert("user_goal", "true"));

    let result = pipeline_conformance_verdict(&pipeline);
    expect_verified(
        &result,
        "a conforming impl whose body was captured (no body axiom) must verify via the \
         captured-body binding",
    );
}

/// The captured-body binding must NOT let a NON-conforming impl pass: a captured
/// body of `false` against a trait `ensures(result)` must still Counterexample.
/// The captured text is the method's TRUE return value, so a violating body
/// contradicts the asserted postcondition — the decisive soundness direction.
#[test]
fn test_trait_conformance_rejects_captured_body_violating_contract() {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    ctx.register_trait_decl(valued_trait_decl());
    ctx.register_trait_impl(valued_impl_decl("Slice6BoolImpl__cap_bad"));
    ctx.declare_helper_function_typed(
        "Slice6BoolImpl__cap_bad",
        TrustVcType::Bool,
        vec![("self".to_string(), TrustVcType::Bool)],
    );
    ctx.register_trait_impl_method_body(
        "Slice6BoolImpl__cap_bad".to_string(),
        crate::ir::ConformanceMethodBody::new("false", 0),
    );
    // Unrelated obligation that would otherwise verify. It is NO LONGER SUNK by
    // the bad impl (attribution); the decisive soundness direction — the captured
    // violating body is REFUTED — is asserted on the impl's OWN obligation.
    ctx.push_obligation(crate::vc::ProofObligation::assert("user_goal", "true"));

    let result = pipeline_conformance_verdict(&pipeline);
    expect_counterexample(
        &result,
        "a captured body that violates the trait ensures must Counterexample, never verify",
    );
    if let VerifyResult::Counterexample {
        obligation_name, ..
    } = &result
    {
        assert_eq!(
            obligation_name,
            "trait impl conformance Slice6Valued::get_value for bool"
        );
    }
}

/// An impl method marked conformance-exempt (it is BLOCKED by a dedicated
/// ill-formedness error — own requires / returns-on-both conflict) must be
/// SKIPPED by the conformance pass: it neither over-rejects nor sinks unrelated
/// work. Without the exemption this impl (no body axiom, no captured body) would
/// over-reject against an unconstrained result. The blocked impl is still
/// rejected via its own error when verified directly (covered by the
/// `traits_rs` conflicting-returns fail-closed guard).
#[test]
fn test_trait_conformance_skips_exempt_method() {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    ctx.register_trait_decl(valued_trait_decl());
    ctx.register_trait_impl(valued_impl_decl("Slice6BoolImpl__exempt"));
    ctx.declare_helper_function_typed(
        "Slice6BoolImpl__exempt",
        TrustVcType::Bool,
        vec![("self".to_string(), TrustVcType::Bool)],
    );
    ctx.register_conformance_exempt_method("Slice6BoolImpl__exempt".to_string());
    ctx.push_obligation(crate::vc::ProofObligation::assert("user_goal", "true"));

    let result = pipeline_conformance_verdict(&pipeline);
    expect_verified(
        &result,
        "a conformance-exempt (blocked) impl method must be skipped, not over-reject \
         unrelated work",
    );
}

#[test]
fn test_trait_conformance_assumes_trait_preconditions() {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    ctx.declare_var_typed("self", TrustVcType::Bool);
    ctx.declare_var_typed("token", TrustVcType::Bool);
    ctx.register_trait_decl(gated_trait_decl());
    ctx.register_trait_impl(gated_impl_decl("Slice6BoolImpl__grant"));
    add_body_axiom(
        ctx,
        "Slice6BoolImpl__grant",
        "Slice6BoolImpl__grant(self, token) == token",
        vec![("self", TrustVcType::Bool), ("token", TrustVcType::Bool)],
        vec!["self", "token"],
        "Slice6BoolImpl__grant(self, token)",
        true,
    );
    ctx.push_obligation(crate::vc::ProofObligation::assert("user_goal", "true"));

    let result = pipeline_conformance_verdict(&pipeline);
    expect_verified(
        &result,
        "trait conformance should assume the trait precondition before checking ensures",
    );
}

#[test]
fn test_trait_conformance_skips_default_methods_without_binding() {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    ctx.register_trait_decl(TraitDecl {
        name: "Slice6DefaultOnly".to_string(),
        methods: vec![TraitMethodDecl {
            name: "default_ok".to_string(),
            params: vec![],
            return_type: TrustVcType::Bool,
            requires: vec![],
            ensures: vec!["result".to_string()],
            has_default: true,
            default_body: None,
            default_ensures: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    });
    ctx.register_trait_impl(TraitImplDecl {
        trait_name: "Slice6DefaultOnly".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    });
    ctx.push_obligation(crate::vc::ProofObligation::assert("user_goal", "true"));

    let result = pipeline_conformance_verdict(&pipeline);
    expect_verified(
        &result,
        "trait conformance should skip default methods until default-body verification lands",
    );
}

// =====================================================================
// Non-overridden default-method conformance (#2442 soundness follow-up).
//
// A non-overridden trait default method body must still establish the trait
// `ensures` (given the trait `requires`): `register_trait` asserts a GLOBAL
// trait-postcondition axiom over the trait method UF, so if the default body
// is never checked against that axiom it is a latent false-`Verified` the
// moment caller-side trait dispatch instantiates a ground `Trait::method(..)`
// term. These tests pin BOTH directions: a bad default fails closed, and a
// correct default passes without tainting unrelated work in the file.
// =====================================================================

/// Trait `TR3 { fn m() -> u8 ensures(result >= 10) { 5u8 } }` — the default
/// body returns 5 but promises `>= 10`.
fn bad_default_trait_decl() -> TraitDecl {
    TraitDecl {
        name: "TR3".to_string(),
        methods: vec![TraitMethodDecl {
            name: "m".to_string(),
            params: vec![],
            return_type: TrustVcType::Uint { width: 8 },
            requires: vec![],
            ensures: vec!["result >= 10".to_string()],
            has_default: true,
            default_body: Some("5u8".to_string()),
            default_ensures: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    }
}

/// (a)/(f) A non-overridden default whose body (5) violates its `ensures`
/// (`result >= 10`) must FAIL conformance with a `Counterexample` tagged to the
/// default's conformance obligation — never a false `Verified`.
#[test]
fn test_trait_conformance_rejects_bad_nonoverridden_default() {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    ctx.register_trait_decl(bad_default_trait_decl());
    ctx.register_trait_impl(TraitImplDecl {
        trait_name: "TR3".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    });
    // Unrelated obligation that would otherwise verify. ATTRIBUTION: it is no
    // longer SUNK by the bad default (the blast radius shrank) — but the bad
    // default is still REJECTED, on the IMPL'S OWN conformance obligation. That
    // rejection is the soundness content and it is unchanged: a default body
    // violating its `ensures` must never be false-`Verified`.
    ctx.push_obligation(crate::vc::ProofObligation::assert("user_goal", "true"));

    expect_verified(
        &pipeline.verify(),
        "attribution: an unrelated obligation is no longer sunk by a bad impl",
    );

    let result = pipeline_conformance_verdict(&pipeline);
    expect_counterexample(
        &result,
        "a non-overridden default body that violates its ensures must fail conformance",
    );
    if let VerifyResult::Counterexample {
        obligation_name, ..
    } = &result
    {
        assert_eq!(obligation_name, "trait impl conformance TR3::m for bool");
    }
}

/// Regression test (external_traits): an `#[trust_vc::external]` impl's
/// bodies are TRUSTED (Verus external_trait_specification), so the
/// body-conformance pass must SKIP it — a deliberately-divergent external
/// default/impl body must not Counterexample and sink unrelated functions.
/// Uses the same bad-default shape that the non-external test above proves
/// WOULD fail conformance, differing only in `is_external`.
#[test]
fn test_trait_conformance_skips_external_impl_bodies() {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    ctx.register_trait_decl(bad_default_trait_decl());
    ctx.register_trait_impl(
        TraitImplDecl::new("TR3", TrustVcType::Bool, vec![]).with_external(true),
    );
    ctx.push_obligation(crate::vc::ProofObligation::assert("user_goal", "true"));

    let result = pipeline_conformance_verdict(&pipeline);
    expect_verified(
        &result,
        "an external impl's trusted bodies must not be conformance-checked \
         (the non-external twin above Counterexamples)",
    );
}

/// (b) A CORRECT non-overridden default (body 15, `ensures(result >= 10)`) must
/// PASS conformance and leave unrelated functions in the file Verifying — no
/// over-rejection. A spurious conformance failure here would taint the genuine
/// `user_goal` obligation.
#[test]
fn test_trait_conformance_accepts_correct_nonoverridden_default_no_over_rejection() {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    ctx.declare_var_typed("n", TrustVcType::Uint { width: 32 });
    ctx.register_trait_decl(TraitDecl {
        name: "TR3Good".to_string(),
        methods: vec![TraitMethodDecl {
            name: "m".to_string(),
            params: vec![],
            return_type: TrustVcType::Uint { width: 8 },
            requires: vec![],
            ensures: vec!["result >= 10".to_string()],
            has_default: true,
            default_body: Some("15u8".to_string()),
            default_ensures: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    });
    ctx.register_trait_impl(TraitImplDecl {
        trait_name: "TR3Good".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    });
    // A genuine, unrelated obligation that exercises the solver.
    ctx.push_obligation(crate::vc::ProofObligation::assume("pre", "n == 3"));
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "user_goal",
        "n + 1 == 4",
    ));

    expect_verified(
        &pipeline_conformance_verdict(&pipeline),
        "a correct non-overridden default must PASS conformance (no over-rejection)",
    );
    expect_verified(
        &pipeline.verify(),
        "a correct non-overridden default must not taint unrelated work",
    );
}

/// (c) A default with a `requires` that the body relies on to establish its
/// `ensures` must PASS — conformance assumes the trait precondition.
/// `fn m(x: u8) -> u8 requires(x >= 5) ensures(result >= 5) { x }`.
#[test]
fn test_trait_conformance_accepts_default_using_requires_to_establish_ensures() {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    ctx.register_trait_decl(TraitDecl {
        name: "TR3Req".to_string(),
        methods: vec![TraitMethodDecl {
            name: "m".to_string(),
            params: vec![("x".to_string(), TrustVcType::Uint { width: 8 })],
            return_type: TrustVcType::Uint { width: 8 },
            requires: vec!["x >= 5".to_string()],
            ensures: vec!["result >= 5".to_string()],
            has_default: true,
            default_body: Some("x".to_string()),
            default_ensures: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    });
    ctx.register_trait_impl(TraitImplDecl {
        trait_name: "TR3Req".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    });
    ctx.push_obligation(crate::vc::ProofObligation::assert("user_goal", "true"));

    let result = pipeline_conformance_verdict(&pipeline);
    expect_verified(
        &result,
        "a default body that establishes its ensures under the trait requires must pass",
    );
}

/// (c, negative) The trait `requires` is genuinely load-bearing: drop it and the
/// SAME body no longer establishes the SAME ensures, so conformance must FAIL.
/// `fn m(x: u8) -> u8 ensures(result >= 5) { x }` (no requires) — `x` can be 0.
#[test]
fn test_trait_conformance_rejects_default_when_requires_dropped() {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    ctx.register_trait_decl(TraitDecl {
        name: "TR3NoReq".to_string(),
        methods: vec![TraitMethodDecl {
            name: "m".to_string(),
            params: vec![("x".to_string(), TrustVcType::Uint { width: 8 })],
            return_type: TrustVcType::Uint { width: 8 },
            requires: vec![],
            ensures: vec!["result >= 5".to_string()],
            has_default: true,
            default_body: Some("x".to_string()),
            default_ensures: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    });
    ctx.register_trait_impl(TraitImplDecl {
        trait_name: "TR3NoReq".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    });
    ctx.push_obligation(crate::vc::ProofObligation::assert("user_goal", "true"));

    expect_verified(
        &pipeline.verify(),
        "attribution: an unrelated obligation is no longer sunk by a bad impl",
    );

    let result = pipeline_conformance_verdict(&pipeline);
    expect_counterexample(
        &result,
        "without the trait requires the default body no longer establishes its ensures",
    );
    if let VerifyResult::Counterexample {
        obligation_name, ..
    } = &result
    {
        assert_eq!(
            obligation_name,
            "trait impl conformance TR3NoReq::m for bool"
        );
    }
}

/// Trait `TR3B { fn m() -> bool ensures(result) { false } }` — a Bool-returning
/// default whose body (`false`) violates its `ensures(result)`. Used by the
/// override tests (the `add_body_axiom` helper declares Bool-returning impls).
fn bad_default_bool_trait_decl() -> TraitDecl {
    TraitDecl {
        name: "TR3B".to_string(),
        methods: vec![TraitMethodDecl {
            name: "m".to_string(),
            params: vec![],
            return_type: TrustVcType::Bool,
            requires: vec![],
            ensures: vec!["result".to_string()],
            has_default: true,
            default_body: Some("false".to_string()),
            default_ensures: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    }
}

/// (d) An impl that DOES override a default method still routes through the
/// overridden-impl conformance path: a GOOD override (body `true`) verifies even
/// though the inherited default body (`false`) would have failed — overriding a
/// bad default with a correct body is allowed and unchanged by this fix.
#[test]
fn test_trait_conformance_good_override_of_default_still_verifies() {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    ctx.declare_var_typed("self", TrustVcType::Bool);
    ctx.register_trait_decl(bad_default_bool_trait_decl());
    ctx.register_trait_impl(TraitImplDecl {
        trait_name: "TR3B".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![("m".to_string(), "TR3BBoolImpl__m_good".to_string())],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    });
    add_body_axiom(
        ctx,
        "TR3BBoolImpl__m_good",
        "TR3BBoolImpl__m_good(self) == true",
        vec![("self", TrustVcType::Bool)],
        vec!["self"],
        "TR3BBoolImpl__m_good(self)",
        true,
    );
    ctx.push_obligation(crate::vc::ProofObligation::assert("user_goal", "true"));

    let result = pipeline_conformance_verdict(&pipeline);
    expect_verified(
        &result,
        "a good override of a default method must verify through the override path",
    );
}

/// (d) A BAD override (body `false`) of a default method still fails through the
/// override path — unchanged behavior.
#[test]
fn test_trait_conformance_bad_override_of_default_fails() {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    ctx.declare_var_typed("self", TrustVcType::Bool);
    ctx.register_trait_decl(bad_default_bool_trait_decl());
    ctx.register_trait_impl(TraitImplDecl {
        trait_name: "TR3B".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![("m".to_string(), "TR3BBoolImpl__m_bad".to_string())],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    });
    add_body_axiom(
        ctx,
        "TR3BBoolImpl__m_bad",
        "TR3BBoolImpl__m_bad(self) == false",
        vec![("self", TrustVcType::Bool)],
        vec!["self"],
        "TR3BBoolImpl__m_bad(self)",
        true,
    );
    ctx.push_obligation(crate::vc::ProofObligation::assert("user_goal", "true"));

    let result = pipeline_conformance_verdict(&pipeline);
    expect_counterexample(
        &result,
        "a bad override of a default method must fail through the override path",
    );
    if let VerifyResult::Counterexample {
        obligation_name, ..
    } = &result
    {
        assert_eq!(obligation_name, "trait impl conformance TR3B::m for bool");
    }
}

/// A declaration-only default (no body text) cannot be checked; conformance
/// preserves the prior skip rather than erroring (caller dispatch still fails
/// closed). Guards against a regression where missing body text taints the file.
#[test]
fn test_trait_conformance_skips_default_without_body_text() {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    ctx.register_trait_decl(TraitDecl {
        name: "TR3NoBody".to_string(),
        methods: vec![TraitMethodDecl {
            name: "m".to_string(),
            params: vec![],
            return_type: TrustVcType::Bool,
            requires: vec![],
            ensures: vec!["result".to_string()],
            has_default: true,
            default_body: None,
            default_ensures: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    });
    ctx.register_trait_impl(TraitImplDecl {
        trait_name: "TR3NoBody".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    });
    ctx.push_obligation(crate::vc::ProofObligation::assert("user_goal", "true"));

    let result = pipeline_conformance_verdict(&pipeline);
    expect_verified(
        &result,
        "a declaration-only default (no body text) is skipped, not over-rejected",
    );
}

// =====================================================================
// Round-3 trait surface: sibling-call default bodies (residual of #2442).
//
// An all-defaults `#[trait_impl]` whose default body calls an UNBOUND sibling
// trait DEFAULT method (`self.g()`) previously failed to lower (`g` unknown on
// the concrete type) and was SILENTLY SKIPPED, publishing the global trait
// postcondition axiom unjustified — a false `Verified` through generic dispatch.
// The fix inlines the non-overridden sibling's default body onto the concrete
// surface (its actual behavior in an all-defaults impl), so a non-conforming
// default Counterexamples and a conforming one still Verifies.
// =====================================================================

/// (cluster) `g` returns 5 (no ensures); `f` calls `self.g()` and promises
/// `>= 10`. The default `f` is non-conforming and must FAIL conformance — never
/// a false `Verified`. This is the headline round-3 hole.
#[test]
fn test_trait_conformance_rejects_bad_sibling_call_default() {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    ctx.register_trait_decl(TraitDecl {
        name: "TRSibBad".to_string(),
        methods: vec![
            TraitMethodDecl {
                name: "g".to_string(),
                params: vec![],
                return_type: TrustVcType::Uint { width: 8 },
                requires: vec![],
                ensures: vec![],
                has_default: true,
                default_body: Some("5u8".to_string()),
                default_ensures: Vec::new(),
            },
            TraitMethodDecl {
                name: "f".to_string(),
                params: vec![],
                return_type: TrustVcType::Uint { width: 8 },
                requires: vec![],
                ensures: vec!["result >= 10".to_string()],
                has_default: true,
                default_body: Some("self.g()".to_string()),
                default_ensures: Vec::new(),
            },
        ],
        supertraits: Vec::new(),
        generics: Vec::new(),
    });
    ctx.register_trait_impl(TraitImplDecl {
        trait_name: "TRSibBad".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    });
    // An unrelated obligation that would otherwise verify. ATTRIBUTION: it is no
    // longer sunk — the bad sibling-call default is REJECTED on the impl's own
    // conformance obligation, which is the soundness content.
    ctx.push_obligation(crate::vc::ProofObligation::assert("user_goal", "true"));

    expect_verified(
        &pipeline.verify(),
        "attribution: an unrelated obligation is no longer sunk by a bad impl",
    );

    let result = pipeline_conformance_verdict(&pipeline);
    expect_counterexample(
        &result,
        "a default body calling an unbound sibling that violates its ensures must fail conformance",
    );
    if let VerifyResult::Counterexample {
        obligation_name, ..
    } = &result
    {
        assert_eq!(
            obligation_name,
            "trait impl conformance TRSibBad::f for bool"
        );
    }
}

/// (no over-rejection) `g` returns 20; `f` calls `self.g()` and promises
/// `>= 10`. The default `f` is conforming and must still VERIFY, leaving the
/// unrelated `user_goal` intact — the inlined sibling body must not over-reject
/// a valid trait default.
#[test]
fn test_trait_conformance_accepts_good_sibling_call_default() {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    ctx.declare_var_typed("n", TrustVcType::Uint { width: 32 });
    ctx.register_trait_decl(TraitDecl {
        name: "TRSibGood".to_string(),
        methods: vec![
            TraitMethodDecl {
                name: "g".to_string(),
                params: vec![],
                return_type: TrustVcType::Uint { width: 8 },
                requires: vec![],
                ensures: vec![],
                has_default: true,
                default_body: Some("20u8".to_string()),
                default_ensures: Vec::new(),
            },
            TraitMethodDecl {
                name: "f".to_string(),
                params: vec![],
                return_type: TrustVcType::Uint { width: 8 },
                requires: vec![],
                ensures: vec!["result >= 10".to_string()],
                has_default: true,
                default_body: Some("self.g()".to_string()),
                default_ensures: Vec::new(),
            },
        ],
        supertraits: Vec::new(),
        generics: Vec::new(),
    });
    ctx.register_trait_impl(TraitImplDecl {
        trait_name: "TRSibGood".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    });
    ctx.push_obligation(crate::vc::ProofObligation::assume("pre", "n == 3"));
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "user_goal",
        "n + 1 == 4",
    ));

    expect_verified(
        &pipeline_conformance_verdict(&pipeline),
        "a conforming default that calls a sibling default must PASS conformance",
    );
    expect_verified(
        &pipeline.verify(),
        "a conforming sibling-call default must not taint unrelated work",
    );
}

/// (nested) `f` -> `self.g()` -> `self.h()` -> 20. Nested sibling-default calls
/// inline to a fixpoint; the conforming `f` (ensures `>= 10`) must VERIFY.
#[test]
fn test_trait_conformance_accepts_nested_sibling_call_default() {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    ctx.register_trait_decl(TraitDecl {
        name: "TRSibNest".to_string(),
        methods: vec![
            TraitMethodDecl {
                name: "h".to_string(),
                params: vec![],
                return_type: TrustVcType::Uint { width: 8 },
                requires: vec![],
                ensures: vec![],
                has_default: true,
                default_body: Some("20u8".to_string()),
                default_ensures: Vec::new(),
            },
            TraitMethodDecl {
                name: "g".to_string(),
                params: vec![],
                return_type: TrustVcType::Uint { width: 8 },
                requires: vec![],
                ensures: vec![],
                has_default: true,
                default_body: Some("self.h()".to_string()),
                default_ensures: Vec::new(),
            },
            TraitMethodDecl {
                name: "f".to_string(),
                params: vec![],
                return_type: TrustVcType::Uint { width: 8 },
                requires: vec![],
                ensures: vec!["result >= 10".to_string()],
                has_default: true,
                default_body: Some("self.g()".to_string()),
                default_ensures: Vec::new(),
            },
        ],
        supertraits: Vec::new(),
        generics: Vec::new(),
    });
    ctx.register_trait_impl(TraitImplDecl {
        trait_name: "TRSibNest".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    });
    ctx.push_obligation(crate::vc::ProofObligation::assert("user_goal", "true"));

    let result = pipeline_conformance_verdict(&pipeline);
    expect_verified(
        &result,
        "nested sibling-default calls inline to a fixpoint and a conforming default verifies",
    );
}

/// (nested, bad) Same chain but `h` returns 5, so `f` (ensures `>= 10`) is
/// non-conforming after inlining `self.g()` -> `self.h()` -> 5 — must FAIL.
#[test]
fn test_trait_conformance_rejects_nested_sibling_call_default() {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    ctx.register_trait_decl(TraitDecl {
        name: "TRSibNestBad".to_string(),
        methods: vec![
            TraitMethodDecl {
                name: "h".to_string(),
                params: vec![],
                return_type: TrustVcType::Uint { width: 8 },
                requires: vec![],
                ensures: vec![],
                has_default: true,
                default_body: Some("5u8".to_string()),
                default_ensures: Vec::new(),
            },
            TraitMethodDecl {
                name: "g".to_string(),
                params: vec![],
                return_type: TrustVcType::Uint { width: 8 },
                requires: vec![],
                ensures: vec![],
                has_default: true,
                default_body: Some("self.h()".to_string()),
                default_ensures: Vec::new(),
            },
            TraitMethodDecl {
                name: "f".to_string(),
                params: vec![],
                return_type: TrustVcType::Uint { width: 8 },
                requires: vec![],
                ensures: vec!["result >= 10".to_string()],
                has_default: true,
                default_body: Some("self.g()".to_string()),
                default_ensures: Vec::new(),
            },
        ],
        supertraits: Vec::new(),
        generics: Vec::new(),
    });
    ctx.register_trait_impl(TraitImplDecl {
        trait_name: "TRSibNestBad".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    });
    ctx.push_obligation(crate::vc::ProofObligation::assert("user_goal", "true"));

    expect_verified(
        &pipeline.verify(),
        "attribution: an unrelated obligation is no longer sunk by a bad impl",
    );

    let result = pipeline_conformance_verdict(&pipeline);
    expect_counterexample(
        &result,
        "a nested sibling-default chain that violates the ensures must fail conformance",
    );
}

/// (param substitution, good) `pick(&self, x)` returns its arg; `f(&self, y)`
/// requires `y >= 10` and returns `self.pick(y)`. Inlining substitutes the
/// sibling's `x` with the call arg `y`, so `result == y >= 10` VERIFIES — proves
/// positional param substitution is wired and not vacuous.
#[test]
fn test_trait_conformance_accepts_param_sibling_call_default() {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    ctx.register_trait_decl(TraitDecl {
        name: "TRSibParam".to_string(),
        methods: vec![
            TraitMethodDecl {
                name: "pick".to_string(),
                params: vec![("x".to_string(), TrustVcType::Uint { width: 8 })],
                return_type: TrustVcType::Uint { width: 8 },
                requires: vec![],
                ensures: vec![],
                has_default: true,
                default_body: Some("x".to_string()),
                default_ensures: Vec::new(),
            },
            TraitMethodDecl {
                name: "f".to_string(),
                params: vec![("y".to_string(), TrustVcType::Uint { width: 8 })],
                return_type: TrustVcType::Uint { width: 8 },
                requires: vec!["y >= 10".to_string()],
                ensures: vec!["result >= 10".to_string()],
                has_default: true,
                default_body: Some("self.pick(y)".to_string()),
                default_ensures: Vec::new(),
            },
        ],
        supertraits: Vec::new(),
        generics: Vec::new(),
    });
    ctx.register_trait_impl(TraitImplDecl {
        trait_name: "TRSibParam".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    });
    ctx.push_obligation(crate::vc::ProofObligation::assert("user_goal", "true"));

    let result = pipeline_conformance_verdict(&pipeline);
    expect_verified(
        &result,
        "a conforming default calling a param sibling default verifies (param substitution)",
    );
}

/// (param substitution, bad) Same as above but the `requires(y >= 10)` is
/// dropped: `result == y` with `y` unconstrained no longer establishes
/// `result >= 10`, so conformance must FAIL — proves the substitution carries
/// the real (unconstrained) argument rather than a vacuous truth.
#[test]
fn test_trait_conformance_rejects_param_sibling_call_default_without_requires() {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    ctx.register_trait_decl(TraitDecl {
        name: "TRSibParamBad".to_string(),
        methods: vec![
            TraitMethodDecl {
                name: "pick".to_string(),
                params: vec![("x".to_string(), TrustVcType::Uint { width: 8 })],
                return_type: TrustVcType::Uint { width: 8 },
                requires: vec![],
                ensures: vec![],
                has_default: true,
                default_body: Some("x".to_string()),
                default_ensures: Vec::new(),
            },
            TraitMethodDecl {
                name: "f".to_string(),
                params: vec![("y".to_string(), TrustVcType::Uint { width: 8 })],
                return_type: TrustVcType::Uint { width: 8 },
                requires: vec![],
                ensures: vec!["result >= 10".to_string()],
                has_default: true,
                default_body: Some("self.pick(y)".to_string()),
                default_ensures: Vec::new(),
            },
        ],
        supertraits: Vec::new(),
        generics: Vec::new(),
    });
    ctx.register_trait_impl(TraitImplDecl {
        trait_name: "TRSibParamBad".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    });
    ctx.push_obligation(crate::vc::ProofObligation::assert("user_goal", "true"));

    expect_verified(
        &pipeline.verify(),
        "attribution: an unrelated obligation is no longer sunk by a bad impl",
    );

    let result = pipeline_conformance_verdict(&pipeline);
    expect_counterexample(
        &result,
        "a param sibling-call default with an unconstrained arg must fail conformance",
    );
}

#[test]
fn test_trait_conformance_specializes_poly_params_and_return() {
    let mut ctx = crate::vc::VerificationContext::new();
    ctx.declare_var_typed("self", TrustVcType::Bool);
    ctx.declare_var_typed("other", TrustVcType::Bool);
    ctx.register_trait_decl(TraitDecl {
        name: "Slice6PolyMirror".to_string(),
        methods: vec![TraitMethodDecl {
            name: "mirror".to_string(),
            params: vec![("other".to_string(), TrustVcType::Poly)],
            return_type: TrustVcType::Poly,
            requires: vec![],
            ensures: vec!["result == other".to_string()],
            has_default: false,
            default_body: None,
            default_ensures: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    });
    ctx.register_trait_impl(TraitImplDecl {
        trait_name: "Slice6PolyMirror".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![("mirror".to_string(), "Slice6BoolImpl__mirror".to_string())],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    });
    add_body_axiom(
        &mut ctx,
        "Slice6BoolImpl__mirror",
        "Slice6BoolImpl__mirror(self, other) == other",
        vec![("self", TrustVcType::Bool), ("other", TrustVcType::Bool)],
        vec!["self", "other"],
        "Slice6BoolImpl__mirror(self, other)",
        true,
    );
    let prepared = prepare_context(&ctx).expect("poly mirror context should prepare");

    let result = conformance_verdict(&prepared);
    expect_verified(&result, "trait conformance should specialize Poly params and return types to the concrete impl type");
}

/// Regression test for #2425: when the concrete impl method is NOT registered
/// via declare_helper_function_typed (the integration pipeline path), the
/// synthesize_impl_method_contexts bridge in prepare_context must provide the
/// FunctionContext so setup_from_prepared can declare the UF before
/// register_trait_impl emits linking axioms.
#[test]
fn test_trait_conformance_pipeline_without_explicit_helper_registration() {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    ctx.declare_var_typed("self", TrustVcType::Bool);
    ctx.register_trait_decl(valued_trait_decl());

    // Register impl WITHOUT add_body_axiom / declare_helper_function_typed.
    // This is the real pipeline path through trait_registry — the concrete
    // function is NOT in helper_functions_typed, so synthesize_impl_method_contexts
    // must bridge the gap.
    ctx.register_trait_impl(valued_impl_decl("SynthBoolImpl__get_value"));

    // No body axiom — the concrete function will be a free UF.
    // The conformance check may fail (UF is unconstrained), but the pipeline
    // must not crash with "Concrete function not registered".
    ctx.push_obligation(crate::vc::ProofObligation::assert("user_goal", "true"));

    // Addressed through the CONFORMANCE path: that is where the #2425 crash lived,
    // and a function's verdict no longer routes through it, so asking
    // `pipeline.verify()` would leave this regression untested.
    let result = pipeline_conformance_verdict(&pipeline);
    expect_encodes_without_error(&result, "synthesized impl method (#2425)");
}

#[test]
fn test_trait_conformance_accepts_unit_receiver_and_return() {
    let mut ctx = crate::vc::VerificationContext::new();
    ctx.declare_var_typed("self", TrustVcType::Unit);
    ctx.register_trait_decl(TraitDecl {
        name: "Slice6UnitApply".to_string(),
        methods: vec![TraitMethodDecl {
            name: "apply".to_string(),
            params: vec![],
            return_type: TrustVcType::Unit,
            requires: vec![],
            ensures: vec!["result == ()".to_string()],
            has_default: false,
            default_body: None,
            default_ensures: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    });
    ctx.register_trait_impl(TraitImplDecl {
        trait_name: "Slice6UnitApply".to_string(),
        concrete_type: TrustVcType::Unit,
        method_bindings: vec![("apply".to_string(), "Slice6UnitImpl__apply".to_string())],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    });
    ctx.declare_helper_function_typed(
        "Slice6UnitImpl__apply",
        TrustVcType::Unit,
        vec![("self".to_string(), TrustVcType::Unit)],
    );
    ctx.push_obligation(
        ProofObligation::broadcast_assume(
            "__body_axiom_Slice6UnitImpl__apply",
            "Slice6UnitImpl__apply(self) == ()",
        )
        .with_bound_vars(vec!["self".to_string()])
        .with_trigger_patterns(vec![vec!["Slice6UnitImpl__apply(self)".to_string()]])
        .with_opaque(true),
    );
    let prepared = prepare_context(&ctx).expect("unit trait context should prepare");

    let result = conformance_verdict(&prepared);
    expect_verified(
        &result,
        "trait conformance should accept impls over the unit type",
    );
}

#[test]
fn test_trait_conformance_enforces_all_postconditions() {
    let mut ctx = crate::vc::VerificationContext::new();
    ctx.declare_var_typed("self", TrustVcType::Bool);
    ctx.declare_var_typed("token", TrustVcType::Bool);
    ctx.register_trait_decl(TraitDecl {
        name: "Slice6MultiEnsures".to_string(),
        methods: vec![TraitMethodDecl {
            name: "grant".to_string(),
            params: vec![("token".to_string(), TrustVcType::Bool)],
            return_type: TrustVcType::Bool,
            requires: vec![],
            ensures: vec!["result".to_string(), "token".to_string()],
            has_default: false,
            default_body: None,
            default_ensures: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    });
    ctx.register_trait_impl(TraitImplDecl {
        trait_name: "Slice6MultiEnsures".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![("grant".to_string(), "Slice6BoolImpl__grant_all".to_string())],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    });
    add_body_axiom(
        &mut ctx,
        "Slice6BoolImpl__grant_all",
        "Slice6BoolImpl__grant_all(self, token) == true",
        vec![("self", TrustVcType::Bool), ("token", TrustVcType::Bool)],
        vec!["self", "token"],
        "Slice6BoolImpl__grant_all(self, token)",
        true,
    );
    let prepared = prepare_context(&ctx).expect("multi-ensures context should prepare");

    let result = conformance_verdict(&prepared);
    expect_counterexample(
        &result,
        "trait conformance should fail when a later postcondition is violated",
    );
    if let VerifyResult::Counterexample {
        obligation_name, ..
    } = &result
    {
        assert_eq!(
            obligation_name,
            "trait impl conformance Slice6MultiEnsures::grant for bool"
        );
    }
}

// ============================================================
// Performance: obligation scan scaling in instantiate_referenced_body_axioms
// ============================================================

/// Build a conformance context with `n_noise` unrelated body axioms.
/// The concrete impl body references one helper function, so the worklist
/// has exactly 1 entry that must scan through all `n_noise + 1` body axioms.
///
/// The O(C×O) pattern in `instantiate_referenced_body_axioms` scans all
/// base.obligations per worklist call. This function exercises that path
/// at controllable obligation scale.
fn time_conformance_with_noise_obligations(n_noise: usize) -> u128 {
    let mut ctx = crate::vc::VerificationContext::new();
    ctx.declare_var_typed("self", TrustVcType::Bool);

    ctx.register_trait_decl(valued_trait_decl());
    ctx.register_trait_impl(valued_impl_decl("ScalingImpl__get_value"));

    // Concrete impl body axiom — references helper_fn(self) to create a worklist entry.
    add_body_axiom(
        &mut ctx,
        "ScalingImpl__get_value",
        "ScalingImpl__get_value(self) == helper_fn(self)",
        vec![("self", TrustVcType::Bool)],
        vec!["self"],
        "ScalingImpl__get_value(self)",
        true,
    );

    // Declare the helper function so the context prepares without error.
    ctx.declare_helper_function_typed(
        "helper_fn",
        TrustVcType::Bool,
        vec![("self".to_string(), TrustVcType::Bool)],
    );
    add_body_axiom(
        &mut ctx,
        "helper_fn",
        "helper_fn(self) == true",
        vec![("self", TrustVcType::Bool)],
        vec!["self"],
        "helper_fn(self)",
        true,
    );

    // Add n_noise unrelated body axioms (scanned but never matched).
    for i in 0..n_noise {
        let name = format!("noise_{i}");
        ctx.declare_helper_function_typed(
            &name,
            TrustVcType::Bool,
            vec![("self".to_string(), TrustVcType::Bool)],
        );
        add_body_axiom(
            &mut ctx,
            &name,
            &format!("{name}(self) == true"),
            vec![("self", TrustVcType::Bool)],
            vec!["self"],
            &format!("{name}(self)"),
            true,
        );
    }

    ctx.push_obligation(crate::vc::ProofObligation::assert("user_goal", "true"));

    let prepared = prepare_context(&ctx).expect("scaling context should prepare");

    let start = std::time::Instant::now();
    let _ = conformance_verdict(&prepared);
    start.elapsed().as_micros()
}

/// Verify that conformance verification scales at most linearly with the
/// number of base obligations. The inner loop in `instantiate_referenced_body_axioms`
/// scans all obligations per worklist call — a HashMap index would make this O(1)
/// per call, but today it is O(O). This test catches any regression to O(O²)
/// (e.g., from nested loops or repeated scanning).
///
/// Uses the same methodology as `performance_proof_audit` tests:
/// measure T(N) and T(4N), check ratio < quadratic threshold.
#[test]
fn test_conformance_obligation_scan_scales_at_most_linearly() {
    const SMALL_N: usize = 20;
    const LARGE_N: usize = 80;
    const QUADRATIC_THRESHOLD: f64 = 12.0;
    // Sub-5ms medians are dominated by scheduler noise on loaded CI/dev
    // machines, which makes a ratio assertion flaky even when absolute time is
    // harmless.
    const MIN_MEASURABLE_US: u128 = 5_000;

    let t_small = median_of(|| time_conformance_with_noise_obligations(SMALL_N), 3);
    let t_large = median_of(|| time_conformance_with_noise_obligations(LARGE_N), 3);

    if t_small < MIN_MEASURABLE_US {
        // Too fast to measure reliably — pass without assertion.
        return;
    }

    let ratio = t_large as f64 / t_small as f64;
    let scale = LARGE_N as f64 / SMALL_N as f64; // 4.0

    assert!(
        ratio < QUADRATIC_THRESHOLD,
        "Conformance obligation scan appears quadratic: \
         T(O={SMALL_N})={t_small}μs, T(O={LARGE_N})={t_large}μs, \
         ratio={ratio:.1}x (threshold {QUADRATIC_THRESHOLD}x for {scale}x scale). \
         instantiate_referenced_body_axioms may need a HashMap index by function name.",
    );
}

fn median_of<F: Fn() -> u128>(f: F, trials: usize) -> u128 {
    let mut timings: Vec<u128> = (0..trials).map(|_| f()).collect();
    timings.sort_unstable();
    timings[timings.len() / 2]
}

// ---------------------------------------------------------------------------
// Phase A3 — associated-type trait-ensures client seam, conformance-gated.
//
// Trait `AssocView { type V; fn produce(&self) -> Self::V ensures(result == 7) }`.
// The impl binds `type V = u64`, so the trait `ensures` is CONCRETELY sorted only
// after `Self::V` is resolved to `u64`. `assert_impl_trait_ensures_concrete_axioms`
// emits `∀self. Impl__produce(self) == 7` about the PER-IMPL concrete function, so
// a client relying on the trait spec can verify. That axiom is a FORGED FACT for a
// non-conforming impl; it is justified ONLY by the per-impl conformance pass. These
// tests pin (a) a conforming impl lets a client verify AND conforms, (b) a
// non-conforming impl is refuted on its own conformance obligation, and FALSIFY the
// gate by showing that the client verdict ALONE (conformance not consulted) FALSELY
// verifies for the bad impl.
// ---------------------------------------------------------------------------

fn assoc_view_trait_decl() -> TraitDecl {
    TraitDecl {
        name: "AssocView".to_string(),
        methods: vec![TraitMethodDecl {
            name: "produce".to_string(),
            params: vec![],
            // Declared as the associated-type projection `Self::V`.
            return_type: TrustVcType::Opaque("Self::V".to_string()),
            requires: vec![],
            ensures: vec!["result == 7".to_string()],
            has_default: false,
            default_body: None,
            default_ensures: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    }
}

fn assoc_view_impl(concrete_fn: &str) -> TraitImplDecl {
    TraitImplDecl::new(
        "AssocView",
        TrustVcType::Bool,
        vec![("produce".to_string(), concrete_fn.to_string())],
    )
    .with_assoc_type_bindings(vec![("V".to_string(), TrustVcType::Uint { width: 64 })])
}

/// Builds a pipeline whose client obligation `client_expr` relies on the trait
/// spec of the `produce` method, backed by an impl whose captured body is
/// `body_text`.
fn assoc_view_client(
    concrete_fn: &str,
    body_text: &str,
    client_expr: &str,
) -> crate::verification_bridge::VerificationPipeline {
    let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
    let ctx = pipeline.context_mut();
    ctx.declare_var_typed("self", TrustVcType::Bool);
    ctx.register_trait_decl(assoc_view_trait_decl());
    ctx.register_trait_impl(assoc_view_impl(concrete_fn));
    // Declare the per-impl concrete function so the client obligation naming it
    // lowers with its resolved concrete return sort (`Self::V` = u64). This is the
    // same surface `synthesize_impl_method_contexts` provides for real source; the
    // concrete-sorted trait-ensures axiom is emitted about exactly this function.
    ctx.declare_helper_function_typed(
        concrete_fn,
        TrustVcType::Uint { width: 64 },
        vec![("self".to_string(), TrustVcType::Bool)],
    );
    ctx.register_trait_impl_method_body(
        concrete_fn.to_string(),
        crate::ir::ConformanceMethodBody::new(body_text, 0),
    );
    ctx.push_obligation(crate::vc::ProofObligation::assert(
        "client_uses_trait_spec",
        client_expr,
    ));
    pipeline
}

/// (a) A CONFORMING impl (`produce` returns `7u64`) lets a client that relies on
/// the trait `ensures(result == 7)` verify — the associated-type projection
/// `Self::V` resolved to `u64` and the concrete-sorted postcondition axiom
/// carried the contract — AND the impl passes its own conformance obligation.
#[test]
fn assoc_conforming_client_verifies_via_trait_spec() {
    let pipeline = assoc_view_client(
        "AssocViewImpl__good",
        "7u64",
        "AssocViewImpl__good(self) == 7",
    );
    expect_verified(
        &pipeline.verify(),
        "a client relying on produce()'s ensures (result == 7) must verify against a conforming impl",
    );
    expect_verified(
        &pipeline_conformance_verdict(&pipeline),
        "the conforming assoc impl must pass its own conformance obligation",
    );
}

/// Soundness control: the emitted axiom carries the SPECIFIC contract value, not a
/// vacuous pass. A client asserting `produce() == 8` (the trait ensures says `== 7`)
/// must NOT verify — proving the axiom is `== 7`, so a wrong client claim is caught.
#[test]
fn assoc_client_wrong_value_does_not_verify() {
    let pipeline = assoc_view_client(
        "AssocViewImpl__ctl",
        "7u64",
        "AssocViewImpl__ctl(self) == 8",
    );
    let verdict = pipeline.verify();
    assert!(
        !verdict.is_verified(),
        "a client claiming produce() == 8 must NOT verify (trait ensures result == 7): {verdict:?}"
    );
}

/// (b) + FALSIFICATION. A NON-CONFORMING impl (`produce` returns `3u64`, violating
/// `ensures(result == 7)`).
///
/// FALSIFICATION (conformance gate removed): the client verdict ALONE — the entry
/// point that does NOT consult conformance — verifies `produce() == 7`, because the
/// concrete-sorted trait-ensures axiom is emitted for EVERY impl and justified only
/// by the (separate) conformance pass. With the gate not consulted, this Verified is
/// a FALSE VERIFY: the impl body returns `3u64`, not `7`.
///
/// THE GATE (restored): consulting the per-impl conformance obligation REFUTES the
/// impl (Counterexample on its own obligation), so the file cannot verify. This is
/// what withholds the forged axiom's effect — the cardinal trait soundness invariant.
#[test]
fn assoc_nonconforming_falsify_gate_then_gate_catches() {
    let pipeline = assoc_view_client(
        "AssocViewImpl__bad",
        "3u64",
        "AssocViewImpl__bad(self) == 7",
    );

    // Gate REMOVED (client obligation verdict only): FALSE VERIFY observed.
    let client_only = pipeline.verify();
    expect_verified(
        &client_only,
        "OBSERVED FALSE-VERIFY: with the conformance gate removed, a client relying on \
         produce() == 7 verifies even though the impl body returns 3u64",
    );

    // Gate RESTORED (per-impl conformance obligation): the impl is refuted.
    let gate = pipeline_conformance_verdict(&pipeline);
    expect_counterexample(
        &gate,
        "the conformance gate must refute the non-conforming impl on its own obligation",
    );
    if let VerifyResult::Counterexample {
        obligation_name, ..
    } = &gate
    {
        assert_eq!(
            obligation_name,
            "trait impl conformance AssocView::produce for bool"
        );
    }
}
