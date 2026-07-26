// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ========================================================================
// Slice 4: setup_from_prepared auto-registration + end-to-end proofs
// ========================================================================

/// `setup_from_prepared` auto-registers datatype UF symbols for variables with
/// `TrustVcType::Datatype`. After setup, the encoder's `datatypes` map should
/// contain the registered encoding without manual `register_datatype` calls.
#[test]
fn test_setup_auto_registers_option_u64_datatype() {
    use crate::prepared_context::PreparedVerificationContext;
    use crate::vc::{ObligationKind, VerificationMode};
    use std::collections::{HashMap, HashSet};

    let option_ty = option_u64_ty();
    let ctx = PreparedVerificationContext {
        obligations: vec![crate::prepared_context::PreparedObligation {
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
            condition: "true".to_string(),
            expr: crate::ir_expr::TrustVcExpr::BoolLit(true),
        }],
        variables: vec![VariableDecl {
            bounded_len: false,
            name: "opt".to_string(),
            ty: option_ty,
        }],
        function_context: None,
        trait_decls: vec![],
        trait_impl_decls: vec![],
        verification_mode: VerificationMode::BodyLevel,
        overflow_behavior: crate::vc::OverflowBehavior::Allow,
        div0_behavior: crate::vc::Div0Behavior::default(),
        bitshift_behavior: crate::vc::BitshiftBehavior::default(),
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

    let slices =
        crate::encoder::verification::VerificationSlices::new(&ctx, &[], &[], &[], &[], &[]);
    let encoder = AYEncoder::setup_from_prepared(&slices, false, None)
        .expect("setup_from_prepared should succeed with Option<u64> variable");

    assert!(
        encoder.datatype_encoding("Option<u64>").is_some(),
        "setup_from_prepared should auto-register Option<u64> datatype"
    );
    let encoding = encoder
        .datatype_encoding("Option<u64>")
        .expect("Option<u64> datatype should be cached");
    assert_eq!(encoding.variants.len(), 2, "Option should have 2 variants");
    assert_eq!(encoding.variants[0].name, "None");
    assert_eq!(encoding.variants[1].name, "Some");
}

/// End-to-end proof: declare `opt: Option<u64>`, assume `opt == Some(42)`,
/// match on opt, assert match result == 43 (Some branch: x + 1).
/// Exercises the full pipeline: auto-registration → match encoding → solver.
#[test]
fn test_setup_e2e_option_match_some_branch_verifies() {
    use crate::prepared_context::{PreparedObligation, PreparedVerificationContext};
    use crate::vc::{ObligationKind, VerificationMode};
    use std::collections::{HashMap, HashSet};

    let option_ty = option_u64_ty();

    let match_expr = TrustVcExpr::Match {
        scrutinee: Box::new(TrustVcExpr::Var {
            name: "opt".to_string(),
            ty: option_ty.clone(),
        }),
        arms: vec![
            MatchArm {
                pattern: MatchPattern::Constructor {
                    variant_name: "Some".to_string(),
                    bindings: vec!["x".to_string()],
                    has_rest: false,
                },
                body: TrustVcExpr::Arith {
                    op: ArithOp::Add,
                    left: Box::new(TrustVcExpr::Var {
                        name: "x".to_string(),
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
                    variant_name: "None".to_string(),
                    bindings: vec![],
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
    };

    let assertion_expr = TrustVcExpr::Compare {
        op: crate::ir::CompareOp::Eq,
        left: Box::new(match_expr),
        right: Box::new(TrustVcExpr::IntLit {
            value: 43,
            ty: u64_ty(),
        }),
    };

    let ctx = PreparedVerificationContext {
        obligations: vec![PreparedObligation {
            name: "match_result".to_string(),
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
            name: "opt".to_string(),
            ty: option_ty.clone(),
        }],
        function_context: None,
        trait_decls: vec![],
        trait_impl_decls: vec![],
        verification_mode: VerificationMode::BodyLevel,
        overflow_behavior: crate::vc::OverflowBehavior::Allow,
        div0_behavior: crate::vc::Div0Behavior::default(),
        bitshift_behavior: crate::vc::BitshiftBehavior::default(),
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

    let slices =
        crate::encoder::verification::VerificationSlices::new(&ctx, &[], &[], &[], &[], &[]);
    let mut encoder = AYEncoder::setup_from_prepared(&slices, false, None)
        .expect("setup should auto-register Option<u64>");

    let encoding = encoder
        .datatype_encoding("Option<u64>")
        .expect("Option<u64> datatype should be cached")
        .clone();
    let opt_term = *encoder.variables.get("opt").expect("opt declared");
    let some = encoding.variant("Some").expect("Some variant");
    let crate::encoder::datatype::ConstructorKind::Function(some_ctor) = &some.constructor else {
        panic!("Some should be a function constructor");
    };
    let forty_two = encoder.solver.try_bv_const(42, 64).unwrap();
    let some_42 = encoder.solver.try_apply(some_ctor, &[forty_two]).unwrap();
    let opt_is_some_42 = encoder.solver.try_eq(opt_term, some_42).unwrap();
    encoder.solver.try_assert_term(opt_is_some_42).unwrap();

    let assertion_term = encoder
        .encode_condition_typed(&ctx.obligations[0].expr)
        .expect("match assertion should encode");
    let negated = encoder.solver.try_not(assertion_term).unwrap();
    encoder.solver.try_assert_term(negated).unwrap();
    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "opt == Some(42) should make match result 43, got {:?}",
        result
    );
}

/// End-to-end proof: exhaustive axiom guarantees `is_None(opt) || is_Some(opt)`.
/// Uses only auto-registered datatypes (no manual registration).
#[test]
fn test_setup_e2e_option_exhaustive_axiom_holds() {
    use crate::prepared_context::{PreparedObligation, PreparedVerificationContext};
    use crate::vc::{ObligationKind, VerificationMode};
    use std::collections::{HashMap, HashSet};

    let option_ty = option_u64_ty();

    let ctx = PreparedVerificationContext {
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
        variables: vec![VariableDecl {
            bounded_len: false,
            name: "opt".to_string(),
            ty: option_ty,
        }],
        function_context: None,
        trait_decls: vec![],
        trait_impl_decls: vec![],
        verification_mode: VerificationMode::BodyLevel,
        overflow_behavior: crate::vc::OverflowBehavior::Allow,
        div0_behavior: crate::vc::Div0Behavior::default(),
        bitshift_behavior: crate::vc::BitshiftBehavior::default(),
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

    let slices =
        crate::encoder::verification::VerificationSlices::new(&ctx, &[], &[], &[], &[], &[]);
    let mut encoder =
        AYEncoder::setup_from_prepared(&slices, false, None).expect("setup should succeed");

    let encoding = encoder
        .datatype_encoding("Option<u64>")
        .expect("Option<u64> datatype should be cached")
        .clone();
    let opt_term = *encoder.variables.get("opt").unwrap();
    let none_tester = &encoding.variant("None").unwrap().tester;
    let some_tester = &encoding.variant("Some").unwrap().tester;

    let is_none = encoder.solver.try_apply(none_tester, &[opt_term]).unwrap();
    let is_some = encoder.solver.try_apply(some_tester, &[opt_term]).unwrap();
    let exhaustive = encoder.solver.try_or(is_none, is_some).unwrap();

    let neg = encoder.solver.try_not(exhaustive).unwrap();
    encoder.solver.try_assert_term(neg).unwrap();
    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "exhaustive axiom should make is_None || is_Some always true, got {:?}",
        result
    );
}
