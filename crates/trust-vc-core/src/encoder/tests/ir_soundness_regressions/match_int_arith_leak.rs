//! #2511 regression: encode_match permanently mutates use_int_arithmetic.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `encode_match` set `use_int_arithmetic = false` for BV-typed match results
//! and constructor fields, but never restored it. This permanently flipped
//! all-Int contexts into BV mode for the remainder of the parser session.

use super::*;

use crate::ir::DatatypeVariant;
use crate::ir_expr::StructPatternField;

fn option_u64_ty() -> TrustVcType {
    TrustVcType::Datatype {
        name: "Option<u64>".to_string(),
        variants: vec![
            DatatypeVariant::new("Some", vec![("_0".to_string(), u64_ty())]),
            DatatypeVariant::new("None", vec![]),
        ],
    }
}

fn counter_ty() -> TrustVcType {
    TrustVcType::Datatype {
        name: "Counter".to_string(),
        variants: vec![DatatypeVariant::new(
            "Counter",
            vec![
                ("count".to_string(), u64_ty()),
                ("max".to_string(), u64_ty()),
            ],
        )],
    }
}

fn mathint_equality_expr() -> TrustVcExpr {
    TrustVcExpr::Compare {
        op: CompareOp::Eq,
        left: Box::new(TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(TrustVcExpr::Var {
                name: "n".into(),
                ty: TrustVcType::MathInt,
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 1,
                ty: TrustVcType::MathInt,
            }),
            ty: TrustVcType::MathInt,
        }),
        right: Box::new(TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(TrustVcExpr::Var {
                name: "n".into(),
                ty: TrustVcType::MathInt,
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 1,
                ty: TrustVcType::MathInt,
            }),
            ty: TrustVcType::MathInt,
        }),
    }
}

// ========================================================================
// #2511: encode_match must not leak use_int_arithmetic mutation
// ========================================================================

/// DISCRIMINATING: int_mode() must be true AFTER encoding a match with
/// BV result type in an all-Int (MathInt) context.
///
/// Pre-fix: encode_match sets use_int_arithmetic = false and never restores it.
/// Post-fix: saved and restored around the match encoding.
#[test]
fn test_2511_encode_match_preserves_int_mode_in_all_int_context() {
    let mut env = QuantifierTestEnv::new();

    // MathInt variable — no BV widths, so use_int_arithmetic starts true
    let n = env.solver.int_var("n");
    env.variables.insert("n".into(), n);
    env.var_types.insert("n".into(), TrustVcType::MathInt);

    let mut parser = env.parser();
    assert!(
        parser.int_mode(),
        "precondition: int_mode should be true in all-MathInt context"
    );

    // Encode a match with BV result type — this exercises the #2511
    // temporary BV-mode path inside encode_match.
    let match_expr = TrustVcExpr::Match {
        scrutinee: Box::new(TrustVcExpr::Var {
            name: "n".into(),
            ty: TrustVcType::MathInt,
        }),
        arms: vec![MatchArm {
            pattern: MatchPattern::Wildcard,
            body: TrustVcExpr::IntLit {
                value: 42,
                ty: TrustVcType::Int { width: 32 },
            },
            guard: None,
        }],
        ty: TrustVcType::Int { width: 32 },
    };

    let result = parser.encode_trust_vc_expr(&match_expr);
    assert!(
        result.is_ok(),
        "match encoding should succeed: {:?}",
        result.err()
    );

    // The critical assertion: int_mode() must still be true
    assert!(
        parser.int_mode(),
        "#2511 regression: encode_match permanently set use_int_arithmetic = false — \
         int_mode() must be restored after match in all-Int context"
    );
    assert!(
        parser.use_int_arithmetic,
        "#2511: use_int_arithmetic must be restored to true after match"
    );
}

/// DISCRIMINATING: Int arithmetic on MathInt variables must succeed AFTER
/// encoding a match with BV result type. Without the fix, the Int arithmetic
/// attempts BV operations on Sort::Int terms, causing sort mismatches.
#[test]
fn test_2511_int_arithmetic_works_after_bv_match() {
    let mut env = QuantifierTestEnv::new();

    let n = env.solver.int_var("n");
    env.variables.insert("n".into(), n);
    env.var_types.insert("n".into(), TrustVcType::MathInt);

    let mut parser = env.parser();

    // First: encode a match with BV result type (triggers the flag flip)
    let match_expr = TrustVcExpr::Match {
        scrutinee: Box::new(TrustVcExpr::Var {
            name: "n".into(),
            ty: TrustVcType::MathInt,
        }),
        arms: vec![MatchArm {
            pattern: MatchPattern::Wildcard,
            body: TrustVcExpr::IntLit {
                value: 10,
                ty: TrustVcType::Int { width: 32 },
            },
            guard: None,
        }],
        ty: TrustVcType::Int { width: 32 },
    };
    parser.encode_trust_vc_expr(&match_expr).unwrap();

    // Second: encode MathInt arithmetic that requires Int mode
    let result = parser.encode_trust_vc_expr(&mathint_equality_expr());
    assert!(
        result.is_ok(),
        "#2511: Int arithmetic after BV-typed match should succeed in all-Int context, \
         got error: {:?}",
        result.err()
    );
}

/// CONTROL: match with non-BV result type should NOT flip use_int_arithmetic.
/// This verifies the fix doesn't break the normal case.
#[test]
fn test_2511_control_bool_match_preserves_int_mode() {
    let mut env = QuantifierTestEnv::new();

    let n = env.solver.int_var("n");
    env.variables.insert("n".into(), n);
    env.var_types.insert("n".into(), TrustVcType::MathInt);

    let mut parser = env.parser();
    assert!(parser.int_mode(), "precondition");

    // Match with Bool result type — bit_width() returns None, so no flag flip
    let match_expr = TrustVcExpr::Match {
        scrutinee: Box::new(TrustVcExpr::Var {
            name: "n".into(),
            ty: TrustVcType::MathInt,
        }),
        arms: vec![MatchArm {
            pattern: MatchPattern::Wildcard,
            body: TrustVcExpr::BoolLit(true),
            guard: None,
        }],
        ty: TrustVcType::Bool,
    };

    parser.encode_trust_vc_expr(&match_expr).unwrap();
    assert!(
        parser.int_mode(),
        "Bool-typed match should not affect int_mode"
    );
}

#[test]
fn test_2643_outer_match_error_restores_int_mode() {
    let mut env = QuantifierTestEnv::new();

    let n = env.solver.int_var("n");
    env.variables.insert("n".into(), n);
    env.var_types.insert("n".into(), TrustVcType::MathInt);

    let mut parser = env.parser();
    assert!(
        parser.use_int_arithmetic,
        "precondition: all-MathInt context should start in int mode"
    );

    let match_expr = TrustVcExpr::Match {
        scrutinee: Box::new(TrustVcExpr::Var {
            name: "n".into(),
            ty: TrustVcType::MathInt,
        }),
        arms: vec![MatchArm {
            pattern: MatchPattern::Wildcard,
            body: TrustVcExpr::Var {
                name: "missing_match_body_bv".into(),
                ty: u64_ty(),
            },
            guard: None,
        }],
        ty: u64_ty(),
    };

    let result = parser.encode_trust_vc_expr(&match_expr);
    assert!(result.is_err(), "match arm body should fail to encode");
    assert!(
        parser.use_int_arithmetic,
        "outer match error path must restore use_int_arithmetic after a BV-typed arm body fails"
    );

    let follow_up = parser.encode_trust_vc_expr(&mathint_equality_expr());
    assert!(
        follow_up.is_ok(),
        "MathInt arithmetic should still encode after a failed BV-typed match body, got {:?}",
        follow_up.err()
    );
}

#[test]
fn test_2643_constructor_binding_success_restores_int_mode() {
    let mut env = QuantifierTestEnv::new();

    let n = env.solver.int_var("n");
    env.variables.insert("n".into(), n);
    env.var_types.insert("n".into(), TrustVcType::MathInt);

    let option_ty = option_u64_ty();
    let opt = env.solver.declare_const(
        "opt",
        crate::encoder::datatype::datatype_carrier_sort("Option<u64>"),
    );
    env.variables.insert("opt".into(), opt);
    env.var_types.insert("opt".into(), option_ty.clone());

    let mut parser = env.parser();
    assert!(
        parser.use_int_arithmetic,
        "precondition: all-MathInt context should start in int mode"
    );

    let match_expr = TrustVcExpr::Match {
        scrutinee: Box::new(TrustVcExpr::Var {
            name: "opt".into(),
            ty: option_ty,
        }),
        arms: vec![
            MatchArm {
                pattern: MatchPattern::Constructor {
                    variant_name: "Some".into(),
                    bindings: vec!["value".into()],
                    has_rest: false,
                },
                body: TrustVcExpr::Var {
                    name: "value".into(),
                    ty: u64_ty(),
                },
                guard: None,
            },
            MatchArm {
                pattern: MatchPattern::Constructor {
                    variant_name: "None".into(),
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

    let result = parser.encode_trust_vc_expr(&match_expr);
    assert!(
        result.is_ok(),
        "constructor-pattern match should encode successfully: {:?}",
        result.err()
    );
    assert!(
        parser.use_int_arithmetic,
        "constructor binding success path must restore use_int_arithmetic after BV selectors"
    );

    let follow_up = parser.encode_trust_vc_expr(&mathint_equality_expr());
    assert!(
        follow_up.is_ok(),
        "MathInt arithmetic should still encode after constructor binding success, got {:?}",
        follow_up.err()
    );
}

#[test]
fn test_2643_struct_binding_error_restores_int_mode() {
    let mut env = QuantifierTestEnv::new();

    let n = env.solver.int_var("n");
    env.variables.insert("n".into(), n);
    env.var_types.insert("n".into(), TrustVcType::MathInt);

    let counter_ty = counter_ty();
    let counter = env.solver.int_var("counter");
    env.variables.insert("counter".into(), counter);
    env.var_types.insert("counter".into(), counter_ty.clone());

    let mut parser = env.parser();
    assert!(
        parser.use_int_arithmetic,
        "precondition: all-MathInt context should start in int mode"
    );

    let match_expr = TrustVcExpr::Match {
        scrutinee: Box::new(TrustVcExpr::Var {
            name: "counter".into(),
            ty: counter_ty,
        }),
        arms: vec![MatchArm {
            pattern: MatchPattern::Struct {
                variant_name: "Counter".into(),
                fields: vec![
                    StructPatternField {
                        field_name: "count".into(),
                        binding: Some("count".into()),
                    },
                    StructPatternField {
                        field_name: "missing".into(),
                        binding: Some("missing".into()),
                    },
                ],
                has_rest: false,
            },
            body: TrustVcExpr::Var {
                name: "count".into(),
                ty: u64_ty(),
            },
            guard: None,
        }],
        ty: u64_ty(),
    };

    let result = parser.encode_trust_vc_expr(&match_expr);
    assert!(
        result.is_err(),
        "struct-pattern binding should fail on the invalid field lookup"
    );
    assert!(
        parser.use_int_arithmetic,
        "struct binding error path must restore use_int_arithmetic after a prior BV field"
    );

    let follow_up = parser.encode_trust_vc_expr(&mathint_equality_expr());
    assert!(
        follow_up.is_ok(),
        "MathInt arithmetic should still encode after struct binding failure, got {:?}",
        follow_up.err()
    );
}
