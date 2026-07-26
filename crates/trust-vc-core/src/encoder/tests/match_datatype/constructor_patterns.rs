// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_constructor_match_encodes_without_error() {
    let mut encoder = AYEncoder::new();
    let (_encoding, option_ty) = option_u64_encoding(&mut encoder);
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "opt".to_string(),
            ty: option_ty.clone(),
        })
        .expect("datatype variable declaration should succeed");

    let expr = TrustVcExpr::Match {
        scrutinee: Box::new(TrustVcExpr::Var {
            name: "opt".to_string(),
            ty: option_ty,
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

    let result = encoder.encode_condition_typed(&expr);
    assert!(
        result.is_ok(),
        "constructor-pattern match should encode, got {:?}",
        result.err()
    );
}

#[test]
fn test_constructor_match_requires_full_variant_coverage() {
    let mut encoder = AYEncoder::new();
    let (_encoding, option_ty) = option_u64_encoding(&mut encoder);
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "opt".to_string(),
            ty: option_ty.clone(),
        })
        .expect("datatype variable declaration should succeed");

    let expr = TrustVcExpr::Match {
        scrutinee: Box::new(TrustVcExpr::Var {
            name: "opt".to_string(),
            ty: option_ty,
        }),
        arms: vec![MatchArm {
            pattern: MatchPattern::Constructor {
                variant_name: "Some".to_string(),
                bindings: vec!["x".to_string()],
                has_rest: false,
            },
            body: TrustVcExpr::Var {
                name: "x".to_string(),
                ty: u64_ty(),
            },
            guard: None,
        }],
        ty: u64_ty(),
    };

    let err = encoder
        .encode_condition_typed(&expr)
        .expect_err("partial constructor match should remain non-exhaustive");
    assert!(
        err.to_string().contains("Non-exhaustive match"),
        "partial constructor match error should mention exhaustiveness, got {err}"
    );
}

#[test]
fn test_constructor_match_some_branch_uses_selector_binding() {
    let mut encoder = AYEncoder::new();
    let (encoding, option_ty) = option_u64_encoding(&mut encoder);
    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "opt".to_string(),
            ty: option_ty.clone(),
        })
        .expect("datatype variable declaration should succeed");

    let opt_term = *encoder
        .variables
        .get("opt")
        .expect("declare_variable should register opt");
    let some = encoding.variant("Some").expect("Some variant should exist");
    let crate::encoder::datatype::ConstructorKind::Function(some_ctor) = &some.constructor else {
        panic!("Some should be a function constructor");
    };
    let forty_two = encoder.solver.try_bv_const(42, 64).unwrap();
    let some_42 = encoder.solver.try_apply(some_ctor, &[forty_two]).unwrap();
    let opt_is_some_42 = encoder.solver.try_eq(opt_term, some_42).unwrap();
    encoder.solver.try_assert_term(opt_is_some_42).unwrap();

    let expr = TrustVcExpr::Compare {
        op: crate::ir::CompareOp::Eq,
        left: Box::new(TrustVcExpr::Match {
            scrutinee: Box::new(TrustVcExpr::Var {
                name: "opt".to_string(),
                ty: option_ty,
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
        }),
        right: Box::new(TrustVcExpr::IntLit {
            value: 43,
            ty: u64_ty(),
        }),
    };

    let encoded = encoder
        .encode_condition_typed(&expr)
        .expect("constructor-pattern match should encode");
    let negated = encoder.solver.try_not(encoded).unwrap();
    encoder.solver.try_assert_term(negated).unwrap();
    let result = encoder.solver.check_sat();
    assert!(
        result.is_unsat(),
        "selector-backed Some branch should force match result to 43, got {:?}",
        result
    );
}

#[test]
fn test_constructor_match_associated_trait_option_scrutinee_uses_actual_sort() {
    let mut encoder = AYEncoder::new();
    let option_ty = TrustVcType::from_str("Option<u8>").expect("Option<u8> should parse");
    let seq_ty = TrustVcType::from_str("Seq<u8>").expect("Seq<u8> should parse");
    let u8_ty = TrustVcType::Uint { width: 8 };

    encoder
        .declare_variable(&VariableDecl {
            bounded_len: false,
            name: "s".to_string(),
            ty: seq_ty.clone(),
        })
        .expect("Seq<u8> variable declaration should succeed");

    // Mirrors the associated-trait surface in
    // evals/verus/ported/recommends_trait_surface_blocker. The backend helper
    // must use the same native datatype carrier sort as its typed Option<u8>
    // return; final AY rejects the old forged tester/selector handles that
    // silently tolerated a mismatched helper result sort.
    let trait_fn_name =
        "__qualified_RecommendsImplementor_u8_as_RecommendsTr_u8_trait_fn_sha256_regression";
    let trait_fn = encoder
        .solver
        .try_declare_fun(
            trait_fn_name,
            &[crate::encoder::types::sort_for_type(&seq_ty)],
            crate::encoder::types::sort_for_type(&option_ty),
        )
        .expect("associated trait function declaration should succeed");
    encoder
        .fn_ctx
        .functions
        .insert(trait_fn_name.to_string(), trait_fn);
    encoder
        .fn_ctx
        .return_types
        .insert(trait_fn_name.to_string(), option_ty.clone());
    encoder
        .fn_ctx
        .param_types
        .insert(trait_fn_name.to_string(), vec![seq_ty.clone()]);

    let expr = TrustVcExpr::Match {
        scrutinee: Box::new(TrustVcExpr::FnCall {
            name: trait_fn_name.to_string(),
            args: vec![TrustVcExpr::Var {
                name: "s".to_string(),
                ty: seq_ty,
            }],
            return_ty: option_ty,
        }),
        arms: vec![
            MatchArm {
                pattern: MatchPattern::Constructor {
                    variant_name: "Some".to_string(),
                    bindings: vec!["x".to_string()],
                    has_rest: false,
                },
                body: TrustVcExpr::Compare {
                    op: crate::ir::CompareOp::Eq,
                    left: Box::new(TrustVcExpr::Var {
                        name: "x".to_string(),
                        ty: u8_ty.clone(),
                    }),
                    right: Box::new(TrustVcExpr::Var {
                        name: "x".to_string(),
                        ty: u8_ty,
                    }),
                },
                guard: None,
            },
            MatchArm {
                pattern: MatchPattern::Constructor {
                    variant_name: "None".to_string(),
                    bindings: vec![],
                    has_rest: false,
                },
                body: TrustVcExpr::BoolLit(false),
                guard: None,
            },
        ],
        ty: TrustVcType::Bool,
    };

    let result = encoder.encode_condition_typed(&expr);
    assert!(
        result.is_ok(),
        "Option match over associated trait call should preserve the native datatype carrier sort, got {:?}",
        result.err()
    );
}

#[test]
fn test_quantified_associated_trait_seq_arg_matches_helper_signature() {
    let mut encoder = AYEncoder::new();
    let option_ty = TrustVcType::from_str("Option<u8>").expect("Option<u8> should parse");
    let seq_ty = TrustVcType::from_str("Seq<u8>").expect("Seq<u8> should parse");

    // Mirrors evals/verus/ported/recommends_trait_surface_blocker: a quantified
    // Seq<u8> is passed as a whole value into the qualified associated trait
    // helper. The helper is declared over the normal Seq<u8> sort.
    let trait_fn_name =
        "__qualified_RecommendsImplementor_u8_as_RecommendsTr_u8_trait_fn_sha256_regression";
    let trait_fn = encoder
        .solver
        .try_declare_fun(
            trait_fn_name,
            &[crate::encoder::types::sort_for_type(&seq_ty)],
            crate::encoder::types::sort_for_type(&option_ty),
        )
        .expect("associated trait function declaration should succeed");
    encoder
        .fn_ctx
        .functions
        .insert(trait_fn_name.to_string(), trait_fn);
    encoder
        .fn_ctx
        .return_types
        .insert(trait_fn_name.to_string(), option_ty.clone());
    encoder
        .fn_ctx
        .param_types
        .insert(trait_fn_name.to_string(), vec![seq_ty.clone()]);

    let expr = TrustVcExpr::Quantifier {
        kind: crate::ir::QuantifierKind::Forall,
        bound_vars: vec![("s".to_string(), seq_ty.clone())],
        body: Box::new(TrustVcExpr::Match {
            scrutinee: Box::new(TrustVcExpr::FnCall {
                name: trait_fn_name.to_string(),
                args: vec![TrustVcExpr::Var {
                    name: "s".to_string(),
                    ty: seq_ty,
                }],
                return_ty: option_ty,
            }),
            arms: vec![
                MatchArm {
                    pattern: MatchPattern::Constructor {
                        variant_name: "Some".to_string(),
                        bindings: vec!["_x".to_string()],
                        has_rest: false,
                    },
                    body: TrustVcExpr::BoolLit(true),
                    guard: None,
                },
                MatchArm {
                    pattern: MatchPattern::Constructor {
                        variant_name: "None".to_string(),
                        bindings: vec![],
                        has_rest: false,
                    },
                    body: TrustVcExpr::BoolLit(false),
                    guard: None,
                },
            ],
            ty: TrustVcType::Bool,
        }),
        triggers: None,
        trigger_inference_mode: None,
    };

    let result = encoder.encode_condition_typed(&expr);
    assert!(
        result.is_ok(),
        "quantified associated trait helper call should not drift Seq<u8> from declared helper sort, got {:?}",
        result.err()
    );
}
