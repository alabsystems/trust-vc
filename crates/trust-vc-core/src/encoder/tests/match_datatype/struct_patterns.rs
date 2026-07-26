// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_named_struct_match_reordered_fields_bind_by_field_name() {
    let mut encoder = AYEncoder::new();
    let (encoding, counter_ty) = counter_encoding(&mut encoder);
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "counter".to_string(),
            ty: counter_ty.clone(),
        })
        .expect("datatype variable declaration should succeed");

    let counter_term = *encoder
        .variables
        .get("counter")
        .expect("declare_variable should register counter");
    let counter_variant = encoding
        .variant("Counter")
        .expect("Counter variant should exist");
    let crate::encoder::datatype::ConstructorKind::Function(counter_ctor) =
        &counter_variant.constructor
    else {
        panic!("Counter should be a function constructor");
    };
    let count_42 = encoder.solver.try_bv_const(42, 64).unwrap();
    let max_99 = encoder.solver.try_bv_const(99, 64).unwrap();
    let counter_value = encoder
        .solver
        .try_apply(counter_ctor, &[count_42, max_99])
        .unwrap();
    let counter_is_bound = encoder.solver.try_eq(counter_term, counter_value).unwrap();
    encoder.solver.try_assert_term(counter_is_bound).unwrap();

    let expr = TrustVcExpr::Compare {
        op: crate::ir::CompareOp::Eq,
        left: Box::new(TrustVcExpr::Match {
            scrutinee: Box::new(TrustVcExpr::Var {
                name: "counter".to_string(),
                ty: counter_ty.clone(),
            }),
            arms: vec![MatchArm {
                pattern: MatchPattern::Struct {
                    variant_name: "Counter".to_string(),
                    fields: vec![
                        StructPatternField {
                            field_name: "max".to_string(),
                            binding: None,
                        },
                        StructPatternField {
                            field_name: "count".to_string(),
                            binding: Some("count".to_string()),
                        },
                    ],
                    has_rest: false,
                },
                body: TrustVcExpr::Var {
                    name: "count".to_string(),
                    ty: u64_ty(),
                },
                guard: None,
            }],
            ty: u64_ty(),
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 42,
            ty: u64_ty(),
        }),
    };

    let encoded = encoder
        .encode_condition_typed(&expr)
        .expect("named-field struct pattern should encode");
    let negated = encoder.solver.try_not(encoded).unwrap();
    encoder.solver.try_assert_term(negated).unwrap();
    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "reordered named fields should still bind the 'count' selector, got {:?}",
        result
    );
}

#[test]
fn test_named_struct_match_alias_binding_uses_field_name_selector() {
    let mut encoder = AYEncoder::new();
    let (encoding, counter_ty) = counter_encoding(&mut encoder);
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "counter".to_string(),
            ty: counter_ty.clone(),
        })
        .expect("datatype variable declaration should succeed");

    let counter_term = *encoder
        .variables
        .get("counter")
        .expect("declare_variable should register counter");
    let counter_variant = encoding
        .variant("Counter")
        .expect("Counter variant should exist");
    let crate::encoder::datatype::ConstructorKind::Function(counter_ctor) =
        &counter_variant.constructor
    else {
        panic!("Counter should be a function constructor");
    };
    let count_42 = encoder.solver.try_bv_const(42, 64).unwrap();
    let max_99 = encoder.solver.try_bv_const(99, 64).unwrap();
    let counter_value = encoder
        .solver
        .try_apply(counter_ctor, &[count_42, max_99])
        .unwrap();
    let counter_is_bound = encoder.solver.try_eq(counter_term, counter_value).unwrap();
    encoder.solver.try_assert_term(counter_is_bound).unwrap();

    let expr = TrustVcExpr::Compare {
        op: crate::ir::CompareOp::Eq,
        left: Box::new(TrustVcExpr::Match {
            scrutinee: Box::new(TrustVcExpr::Var {
                name: "counter".to_string(),
                ty: counter_ty.clone(),
            }),
            arms: vec![MatchArm {
                pattern: MatchPattern::Struct {
                    variant_name: "Counter".to_string(),
                    fields: vec![
                        StructPatternField {
                            field_name: "count".to_string(),
                            binding: Some("current".to_string()),
                        },
                        StructPatternField {
                            field_name: "max".to_string(),
                            binding: None,
                        },
                    ],
                    has_rest: false,
                },
                body: TrustVcExpr::Var {
                    name: "current".to_string(),
                    ty: u64_ty(),
                },
                guard: None,
            }],
            ty: u64_ty(),
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 42,
            ty: u64_ty(),
        }),
    };

    let encoded = encoder
        .encode_condition_typed(&expr)
        .expect("aliased named-field struct pattern should encode");
    let negated = encoder.solver.try_not(encoded).unwrap();
    encoder.solver.try_assert_term(negated).unwrap();
    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "aliased named field should still bind the 'count' selector, got {:?}",
        result
    );
}

#[test]
fn test_named_struct_match_rest_allows_omitted_fields() {
    let mut encoder = AYEncoder::new();
    let (encoding, counter_ty) = counter_encoding(&mut encoder);
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "counter".to_string(),
            ty: counter_ty.clone(),
        })
        .expect("datatype variable declaration should succeed");

    let counter_term = *encoder
        .variables
        .get("counter")
        .expect("declare_variable should register counter");
    let counter_variant = encoding
        .variant("Counter")
        .expect("Counter variant should exist");
    let crate::encoder::datatype::ConstructorKind::Function(counter_ctor) =
        &counter_variant.constructor
    else {
        panic!("Counter should be a function constructor");
    };
    let count_42 = encoder.solver.try_bv_const(42, 64).unwrap();
    let max_99 = encoder.solver.try_bv_const(99, 64).unwrap();
    let counter_value = encoder
        .solver
        .try_apply(counter_ctor, &[count_42, max_99])
        .unwrap();
    let counter_is_bound = encoder.solver.try_eq(counter_term, counter_value).unwrap();
    encoder.solver.try_assert_term(counter_is_bound).unwrap();

    let expr = TrustVcExpr::Compare {
        op: crate::ir::CompareOp::Eq,
        left: Box::new(TrustVcExpr::Match {
            scrutinee: Box::new(TrustVcExpr::Var {
                name: "counter".to_string(),
                ty: counter_ty.clone(),
            }),
            arms: vec![MatchArm {
                pattern: MatchPattern::Struct {
                    variant_name: "Counter".to_string(),
                    fields: vec![StructPatternField {
                        field_name: "count".to_string(),
                        binding: Some("count".to_string()),
                    }],
                    has_rest: true,
                },
                body: TrustVcExpr::Arith {
                    op: ArithOp::Add,
                    left: Box::new(TrustVcExpr::Var {
                        name: "count".to_string(),
                        ty: u64_ty(),
                    }),
                    right: Box::new(TrustVcExpr::IntLit {
                        value: 1,
                        ty: u64_ty(),
                    }),
                    ty: u64_ty(),
                },
                guard: None,
            }],
            ty: u64_ty(),
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 43,
            ty: u64_ty(),
        }),
    };

    let encoded = encoder
        .encode_condition_typed(&expr)
        .expect("named-field struct pattern with rest should encode");
    let negated = encoder.solver.try_not(encoded).unwrap();
    encoder.solver.try_assert_term(negated).unwrap();
    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "rest pattern should allow omitted fields while still binding 'count', got {:?}",
        result
    );
}
