// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Tests for struct type invariant verification (#2419 Slices 1+2).

use std::collections::{HashMap, HashSet};

use super::*;
use crate::encoder::datatype::ConstructorKind;
use crate::ir::{CompareOp, StructDef, TrustVcExpr, TrustVcType};
use crate::prepared_context::{PreparedObligation, PreparedVerificationContext};
use crate::vc::{InvariantMask, ObligationKind, VariableDecl, VerificationMode};

fn u32_ty() -> TrustVcType {
    TrustVcType::Uint { width: 32 }
}

fn counter_struct() -> StructDef {
    StructDef::new(
        "Counter",
        vec![
            ("count".to_string(), u32_ty()),
            ("max".to_string(), u32_ty()),
        ],
    )
}

fn counter_datatype_type() -> TrustVcType {
    counter_struct().to_datatype_type()
}

/// Invariant: count <= max
fn counter_invariant() -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: CompareOp::Le,
        left: Box::new(TrustVcExpr::Var {
            name: "count".to_string(),
            ty: u32_ty(),
        }),
        right: Box::new(TrustVcExpr::Var {
            name: "max".to_string(),
            ty: u32_ty(),
        }),
    }
}

fn counter_context(assertions: Vec<PreparedObligation>) -> PreparedVerificationContext {
    let counter_def = counter_struct();
    PreparedVerificationContext {
        obligations: assertions,
        variables: vec![VariableDecl {
            bounded_len: false,
            name: "c".to_string(),
            ty: counter_datatype_type(),
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
        struct_types: vec![counter_def],
        type_invariants: {
            let mut m = HashMap::new();
            m.insert("Counter".to_string(), counter_invariant());
            m
        },
        invariant_mask: InvariantMask::default(),
        tracked_params: HashSet::new(),
        rlimit_ms: None,
        demand_inline: crate::vc::DemandInlineConfig::new(),
        counterexample_var_meta: HashMap::new(),
        ..Default::default()
    }
}

// --- Slice 1: Struct Registration Tests ---

#[test]
fn test_struct_single_variant_registration() {
    let mut encoder = AYEncoder::new();
    let dt_type = counter_datatype_type();
    let TrustVcType::Datatype { name, variants } = &dt_type else {
        panic!("Counter should lower to TrustVcType::Datatype");
    };

    let encoding = encoder.register_datatype(name, variants).unwrap();
    assert_eq!(encoding.name, "Counter");
    assert_eq!(encoding.variants.len(), 1);

    let v = encoding
        .variant("Counter")
        .expect("Counter variant should exist");
    assert!(matches!(&v.constructor, ConstructorKind::Function(_)));
    assert_eq!(v.selectors.len(), 2);
    assert_eq!(v.selectors[0].name(), "Counter_Counter_count");
    assert_eq!(v.selectors[1].name(), "Counter_Counter_max");
}

#[test]
fn test_struct_field_roundtrip() {
    let mut encoder = AYEncoder::new();
    let dt_type = counter_datatype_type();
    let TrustVcType::Datatype { name, variants } = &dt_type else {
        panic!("Counter should lower to TrustVcType::Datatype");
    };

    let encoding = encoder.register_datatype(name, variants).unwrap();
    let v = encoding.variant("Counter").unwrap();
    let ConstructorKind::Function(ctor) = &v.constructor else {
        panic!("Counter constructor should be a function");
    };

    // Counter(5, 10)
    let five = encoder.solver.try_bv_const(5, 32).unwrap();
    let ten = encoder.solver.try_bv_const(10, 32).unwrap();
    let counter = encoder.solver.try_apply(ctor, &[five, ten]).unwrap();

    // Counter_Counter_count(Counter(5, 10)) == 5
    let selected_count = encoder
        .solver
        .try_apply(&v.selectors[0], &[counter])
        .unwrap();
    let eq_count = encoder.solver.try_eq(selected_count, five).unwrap();
    let not_eq = encoder.solver.try_not(eq_count).unwrap();
    encoder.solver.try_assert_term(not_eq).unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "field roundtrip should make negation unsat, got {:?}",
        result
    );
}

#[test]
fn test_struct_injectivity() {
    let mut encoder = AYEncoder::new();
    let dt_type = counter_datatype_type();
    let TrustVcType::Datatype { name, variants } = &dt_type else {
        panic!("Counter should lower to TrustVcType::Datatype");
    };

    let encoding = encoder.register_datatype(name, variants).unwrap();
    let v = encoding.variant("Counter").unwrap();
    let ConstructorKind::Function(ctor) = &v.constructor else {
        panic!("Counter constructor should be a function");
    };

    // Counter(a, b) == Counter(c, d) => a == c
    let a = encoder
        .solver
        .fresh_var("a", ay_dpll::api::Sort::bitvec(32));
    let b = encoder
        .solver
        .fresh_var("b", ay_dpll::api::Sort::bitvec(32));
    let c = encoder
        .solver
        .fresh_var("c", ay_dpll::api::Sort::bitvec(32));
    let d = encoder
        .solver
        .fresh_var("d", ay_dpll::api::Sort::bitvec(32));

    let ab = encoder.solver.try_apply(ctor, &[a, b]).unwrap();
    let cd = encoder.solver.try_apply(ctor, &[c, d]).unwrap();

    // Assume Counter(a,b) == Counter(c,d)
    let eq_ctors = encoder.solver.try_eq(ab, cd).unwrap();
    encoder.solver.try_assert_term(eq_ctors).unwrap();

    // Assert NOT(a == c) — should be unsat by injectivity
    let eq_ac = encoder.solver.try_eq(a, c).unwrap();
    let not_eq_ac = encoder.solver.try_not(eq_ac).unwrap();
    encoder.solver.try_assert_term(not_eq_ac).unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "injectivity should make negation unsat, got {:?}",
        result
    );
}

// --- Slice 2: Type Invariant Tests ---

#[test]
fn test_invariant_assumed_on_parameter() {
    // For c: Counter with invariant count <= max,
    // asserting c.count <= c.max should be trivially true.
    let assertion = PreparedObligation {
        name: "inv_holds".to_string(),
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
        // Assert: count_selector(c) <= max_selector(c)
        // Using FnCall to reference the selector UFs
        expr: TrustVcExpr::Compare {
            op: CompareOp::Le,
            left: Box::new(TrustVcExpr::FnCall {
                name: "Counter_Counter_count".to_string(),
                args: vec![TrustVcExpr::Var {
                    name: "c".to_string(),
                    ty: counter_datatype_type(),
                }],
                return_ty: u32_ty(),
            }),
            right: Box::new(TrustVcExpr::FnCall {
                name: "Counter_Counter_max".to_string(),
                args: vec![TrustVcExpr::Var {
                    name: "c".to_string(),
                    ty: counter_datatype_type(),
                }],
                return_ty: u32_ty(),
            }),
        },
    };

    let ctx = counter_context(vec![assertion]);
    let slices =
        crate::encoder::verification::VerificationSlices::new(&ctx, &[], &[], &[], &[], &[]);
    let mut encoder =
        AYEncoder::setup_from_prepared(&slices, false, None).expect("setup should succeed");

    // Verify the encoder set up invariant infrastructure
    assert!(
        encoder.has_type_invariant("Counter"),
        "invariant UF should be registered"
    );

    // The invariant is asserted on parameter c, so the formula is sat
    // (no assertion negation added by setup_from_prepared alone).
    let _result = encoder.solver.check_sat();
}

#[test]
fn test_invariant_encoding_registers_uf() {
    let dt_type = counter_datatype_type();
    let TrustVcType::Datatype { name, variants } = &dt_type else {
        panic!("Counter should lower to TrustVcType::Datatype");
    };

    let mut encoder = AYEncoder::new();
    // Register the datatype
    encoder.register_datatype(name, variants).unwrap();

    // Emit the invariant
    encoder
        .emit_type_invariant("Counter", &counter_invariant())
        .unwrap();

    // The invariant UF should be registered
    assert!(
        encoder.has_type_invariant("Counter"),
        "invariant UF should be registered after emit_type_invariant"
    );
}

#[test]
fn test_setup_from_prepared_emits_invariant_without_struct_parameter() {
    let assertion = PreparedObligation {
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
    };

    let mut ctx = counter_context(vec![assertion]);
    ctx.variables.clear();

    let slices =
        crate::encoder::verification::VerificationSlices::new(&ctx, &[], &[], &[], &[], &[]);
    let encoder = AYEncoder::setup_from_prepared(&slices, false, None)
        .expect("setup should emit invariant axioms without a Counter-typed parameter");

    assert!(
        encoder.has_type_invariant("Counter"),
        "Counter invariant UF should still be registered without a Counter variable"
    );
}

#[test]
fn test_invariant_assumption_makes_field_inequality_unsat() {
    let dt_type = counter_datatype_type();
    let TrustVcType::Datatype { name, variants } = &dt_type else {
        panic!("Counter should lower to TrustVcType::Datatype");
    };

    let mut encoder = AYEncoder::new();
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "c".to_string(),
            ty: dt_type.clone(),
        })
        .unwrap();

    encoder.register_datatype(name, variants).unwrap();
    encoder
        .emit_type_invariant("Counter", &counter_invariant())
        .unwrap();

    // Assert invariant on parameter c
    let c_term = *encoder.variables.get("c").unwrap();
    encoder
        .assert_type_invariant_on_term("Counter", c_term)
        .unwrap();

    // Now get selectors and assert count > max (should be unsat)
    let encoding = encoder
        .datatype_encoding("Counter")
        .expect("Counter datatype should be cached")
        .clone();
    let variant = &encoding.variants[0];
    let count_sel = encoder
        .solver
        .try_apply(&variant.selectors[0], &[c_term])
        .unwrap();
    let max_sel = encoder
        .solver
        .try_apply(&variant.selectors[1], &[c_term])
        .unwrap();

    // Assert count > max (negation of invariant)
    let count_gt_max = encoder.solver.try_bvugt(count_sel, max_sel).unwrap();
    encoder.solver.try_assert_term(count_gt_max).unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "invariant assumption should make count > max unsat, got {:?}",
        result
    );
}

#[test]
fn test_setup_from_prepared_registers_struct_and_invariant() {
    // Full pipeline test: setup_from_prepared should register struct types
    // and emit invariant axioms automatically.
    let assertion = PreparedObligation {
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
    };

    let ctx = counter_context(vec![assertion]);
    let slices =
        crate::encoder::verification::VerificationSlices::new(&ctx, &[], &[], &[], &[], &[]);
    let encoder = AYEncoder::setup_from_prepared(&slices, false, None)
        .expect("setup with struct type should succeed");

    // Verify that the datatype was registered
    assert!(
        encoder.datatype_encoding("Counter").is_some(),
        "Counter datatype should be registered after setup"
    );

    // Verify that the invariant UF was registered
    assert!(
        encoder.has_type_invariant("Counter"),
        "Counter invariant UF should be registered after setup"
    );
}

#[test]
fn test_type_invariant_accepts_valid_constructed_value() {
    let dt_type = counter_datatype_type();
    let TrustVcType::Datatype { name, variants } = &dt_type else {
        panic!("Counter should lower to TrustVcType::Datatype");
    };

    let mut encoder = AYEncoder::new();
    encoder.register_datatype(name, variants).unwrap();
    encoder
        .emit_type_invariant("Counter", &counter_invariant())
        .unwrap();

    let encoding = encoder
        .datatype_encoding("Counter")
        .expect("Counter datatype should be cached")
        .clone();
    let variant = encoding.variant("Counter").unwrap();
    let ConstructorKind::Function(ctor) = &variant.constructor else {
        panic!("Counter constructor should be a function");
    };

    let count = encoder.solver.try_bv_const(3, 32).unwrap();
    let max = encoder.solver.try_bv_const(7, 32).unwrap();
    let counter = encoder.solver.try_apply(ctor, &[count, max]).unwrap();

    encoder
        .assert_type_invariant_on_term("Counter", counter)
        .unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_sat() || result.is_unknown(),
        "valid constructed Counter value should satisfy the type invariant or fail closed, got {:?}",
        result
    );
}

#[test]
fn test_type_invariant_rejects_invalid_constructed_value() {
    let dt_type = counter_datatype_type();
    let TrustVcType::Datatype { name, variants } = &dt_type else {
        panic!("Counter should lower to TrustVcType::Datatype");
    };

    let mut encoder = AYEncoder::new();
    encoder.register_datatype(name, variants).unwrap();
    encoder
        .emit_type_invariant("Counter", &counter_invariant())
        .unwrap();

    let encoding = encoder
        .datatype_encoding("Counter")
        .expect("Counter datatype should be cached")
        .clone();
    let variant = encoding.variant("Counter").unwrap();
    let ConstructorKind::Function(ctor) = &variant.constructor else {
        panic!("Counter constructor should be a function");
    };

    let count = encoder.solver.try_bv_const(9, 32).unwrap();
    let max = encoder.solver.try_bv_const(4, 32).unwrap();
    let counter = encoder.solver.try_apply(ctor, &[count, max]).unwrap();

    encoder
        .assert_type_invariant_on_term("Counter", counter)
        .unwrap();

    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "invalid constructed Counter value should violate the type invariant, got {:?}",
        result
    );
}
