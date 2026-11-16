// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// End-to-end setup coverage for builtin datatype UF encoding (#1942).

use std::collections::{HashMap, HashSet};

use super::*;
use crate::encoder::datatype::ConstructorKind;
use crate::ir::{ArithOp, CompareOp, TrustVcType};
use crate::ir_expr::{MatchArm, MatchPattern, TrustVcExpr};
use crate::prepared_context::{PreparedObligation, PreparedVerificationContext};
use crate::vc::{ObligationKind, VariableDecl, VerificationMode};

fn option_u64_ty() -> TrustVcType {
    TrustVcType::from_str("Option<u64>").expect("Option<u64> should parse")
}

fn result_u64_bool_ty() -> TrustVcType {
    TrustVcType::from_str("Result<u64, bool>").expect("Result<u64, bool> should parse")
}

fn u64_ty() -> TrustVcType {
    TrustVcType::Uint { width: 64 }
}

fn trivial_context(variables: Vec<VariableDecl>) -> PreparedVerificationContext {
    PreparedVerificationContext {
        obligations: vec![PreparedObligation {
            name: "trivial".to_string(),
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
            condition: String::new(),
            expr: TrustVcExpr::BoolLit(true),
        }],
        variables,
        function_context: None,
        trait_decls: vec![],
        trait_impl_decls: vec![],
        verification_mode: VerificationMode::BodyLevel,
        overflow_behavior: crate::vc::OverflowBehavior::Allow,
        div0_behavior: crate::vc::Div0Behavior::default(),
        bitshift_behavior: crate::vc::BitshiftBehavior::default(),
        scalar_cast_capture: None,
        broadcast_use_groups: HashSet::new(),
        assert_by_scopes: HashMap::new(),
        forall_bound_vars: HashMap::new(),
        loop_guards: HashMap::new(),
        loop_modified_vars: HashMap::new(),
        has_collection_context: false,
        revealed_fns: HashSet::new(),
        helper_function_contexts: Vec::new(),
        struct_types: Vec::new(),
        type_invariants: HashMap::new(),
        invariant_mask: crate::vc::InvariantMask::default(),
        tracked_params: HashSet::new(),
        rlimit_ms: None,
        demand_inline: crate::vc::DemandInlineConfig::new(),
        counterexample_var_meta: HashMap::new(),
        ..Default::default()
    }
}

fn setup_from_context(ctx: &PreparedVerificationContext) -> AYEncoder {
    let slices =
        crate::encoder::verification::VerificationSlices::new(ctx, &[], &[], &[], &[], &[]);
    AYEncoder::setup_from_prepared(&slices, false, None)
        .expect("datatype setup_from_prepared should succeed")
}

#[test]
fn test_setup_e2e_result_match_ok_branch_verifies() {
    let result_ty = result_u64_bool_ty();
    let assertion_expr = TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(TrustVcExpr::Match {
            scrutinee: Box::new(TrustVcExpr::Var {
                name: "res".to_string(),
                ty: result_ty.clone(),
            }),
            arms: vec![
                MatchArm {
                    pattern: MatchPattern::Constructor {
                        variant_name: "Ok".to_string(),
                        bindings: vec!["value".to_string()],
                        has_rest: false,
                    },
                    body: TrustVcExpr::Arith {
                        op: ArithOp::Add,
                        left: Box::new(TrustVcExpr::Var {
                            name: "value".to_string(),
                            ty: u64_ty(),
                        }),
                        right: Box::new(TrustVcExpr::IntLit {
                            value: 1,
                            ty: u64_ty(),
                        }),
                        ty: u64_ty(),
                    },
                    guard: None,
                },
                MatchArm {
                    pattern: MatchPattern::Constructor {
                        variant_name: "Err".to_string(),
                        bindings: vec!["flag".to_string()],
                        has_rest: false,
                    },
                    body: TrustVcExpr::IntLit {
                        value: 0,
                        ty: u64_ty(),
                    },
                    guard: None,
                },
            ],
            ty: u64_ty(),
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 43,
            ty: u64_ty(),
        }),
    };

    let ctx = PreparedVerificationContext {
        obligations: vec![PreparedObligation {
            name: "result_match".to_string(),
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
            condition: String::new(),
            expr: assertion_expr,
        }],
        variables: vec![VariableDecl {
            bounded_len: false,
            name: "res".to_string(),
            ty: result_ty.clone(),
        }],
        function_context: None,
        trait_decls: vec![],
        trait_impl_decls: vec![],
        verification_mode: VerificationMode::BodyLevel,
        overflow_behavior: crate::vc::OverflowBehavior::Allow,
        div0_behavior: crate::vc::Div0Behavior::default(),
        bitshift_behavior: crate::vc::BitshiftBehavior::default(),
        scalar_cast_capture: None,
        broadcast_use_groups: HashSet::new(),
        assert_by_scopes: HashMap::new(),
        forall_bound_vars: HashMap::new(),
        loop_guards: HashMap::new(),
        loop_modified_vars: HashMap::new(),
        has_collection_context: false,
        revealed_fns: HashSet::new(),
        helper_function_contexts: Vec::new(),
        struct_types: Vec::new(),
        type_invariants: HashMap::new(),
        invariant_mask: crate::vc::InvariantMask::default(),
        tracked_params: HashSet::new(),
        rlimit_ms: None,
        demand_inline: crate::vc::DemandInlineConfig::new(),
        counterexample_var_meta: HashMap::new(),
        ..Default::default()
    };

    let mut encoder = setup_from_context(&ctx);
    assert!(
        encoder.datatype_encoding("Result<u64, bool>").is_some(),
        "setup should auto-register Result<u64, bool>"
    );

    let encoding = encoder
        .datatype_encoding("Result<u64, bool>")
        .expect("Result<u64, bool> datatype should be cached")
        .clone();
    let ok = encoding.variant("Ok").expect("Ok variant should exist");
    let ConstructorKind::Function(ok_ctor) = &ok.constructor else {
        panic!("Ok should be a function constructor");
    };
    let res_term = *encoder.variables.get("res").expect("res declared");
    let forty_two = encoder.solver.try_bv_const(42, 64).unwrap();
    let ok_42 = encoder.solver.try_apply(ok_ctor, &[forty_two]).unwrap();
    let res_is_ok_42 = encoder.solver.try_eq(res_term, ok_42).unwrap();
    encoder.solver.try_assert_term(res_is_ok_42).unwrap();

    let assertion_term = encoder
        .encode_condition_typed(&ctx.obligations[0].expr)
        .expect("Result match assertion should encode");
    let negated = encoder.solver.try_not(assertion_term).unwrap();
    encoder.solver.try_assert_term(negated).unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "res == Ok(42) should make the Result match evaluate to 43, got {:?}",
        result
    );
}

#[test]
fn test_setup_e2e_option_injectivity_axiom_holds() {
    let ctx = trivial_context(vec![
        VariableDecl {
            bounded_len: false,
            name: "opt".to_string(),
            ty: option_u64_ty(),
        },
        VariableDecl {
            bounded_len: false,
            name: "a".to_string(),
            ty: u64_ty(),
        },
        VariableDecl {
            bounded_len: false,
            name: "b".to_string(),
            ty: u64_ty(),
        },
    ]);
    let mut encoder = setup_from_context(&ctx);

    let encoding = encoder
        .datatype_encoding("Option<u64>")
        .expect("Option<u64> datatype should be cached")
        .clone();
    let some = encoding.variant("Some").expect("Some variant should exist");
    let ConstructorKind::Function(some_ctor) = &some.constructor else {
        panic!("Some should be a function constructor");
    };
    let a = *encoder.variables.get("a").expect("a declared");
    let b = *encoder.variables.get("b").expect("b declared");
    let some_a = encoder.solver.try_apply(some_ctor, &[a]).unwrap();
    let some_b = encoder.solver.try_apply(some_ctor, &[b]).unwrap();
    let same_ctor = encoder.solver.try_eq(some_a, some_b).unwrap();
    let same_payload = encoder.solver.try_eq(a, b).unwrap();
    let different_payload = encoder.solver.try_not(same_payload).unwrap();
    let contradiction = encoder
        .solver
        .try_and(same_ctor, different_payload)
        .unwrap();
    encoder.solver.try_assert_term(contradiction).unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "Option injectivity should reject Some(a) == Some(b) with a != b, got {:?}",
        result
    );
}

#[test]
fn test_setup_e2e_option_disjoint_axiom_holds() {
    let ctx = trivial_context(vec![VariableDecl {
        bounded_len: false,
        name: "opt".to_string(),
        ty: option_u64_ty(),
    }]);
    let mut encoder = setup_from_context(&ctx);

    let encoding = encoder
        .datatype_encoding("Option<u64>")
        .expect("Option<u64> datatype should be cached")
        .clone();
    let opt = *encoder.variables.get("opt").expect("opt declared");
    let is_none = encoder
        .solver
        .try_apply(&encoding.variant("None").unwrap().tester, &[opt])
        .unwrap();
    let is_some = encoder
        .solver
        .try_apply(&encoding.variant("Some").unwrap().tester, &[opt])
        .unwrap();
    let contradiction = encoder.solver.try_and(is_some, is_none).unwrap();
    encoder.solver.try_assert_term(contradiction).unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "Option disjointness should reject is_Some(opt) && is_None(opt), got {:?}",
        result
    );
}
