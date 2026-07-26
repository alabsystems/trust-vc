//! Tests for if/match/block, reference, return, paren, and unsupported variant lowering.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::ir::{DatatypeVariant, TrustVcType};
use crate::ir_expr::*;

use super::tests_support::env_with;

fn assert_unsupported_expr(expr_src: &str, vars: &[(&str, &str)], expected: &str) {
    let expr: syn::Expr = syn::parse_str(expr_src)
        .unwrap_or_else(|e| panic!("failed to parse unsupported expr '{expr_src}': {e}"));
    let env = env_with(vars);
    match lower_syn_expr(&expr, &env) {
        Err(LoweringError::UnsupportedExpr(msg)) => {
            assert!(
                msg.contains(expected),
                "expected UnsupportedExpr containing '{expected}', got '{msg}'"
            );
        }
        Err(other) => {
            panic!("expected UnsupportedExpr for '{expr_src}', got different error: {other:?}")
        }
        Ok(lowered) => panic!("expected error for unsupported expr '{expr_src}', got {lowered:?}"),
    }
}

// === If expression ===

#[test]
fn lower_if_else() {
    let expr: syn::Expr = syn::parse_str("if cond { x } else { y }").unwrap();
    let env = env_with(&[("cond", "bool"), ("x", "i32"), ("y", "i32")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert!(matches!(result, TrustVcExpr::Ite { .. }));
}

#[test]
fn lower_if_no_else_fails() {
    let expr: syn::Expr = syn::parse_str("if cond { x }").unwrap();
    let env = env_with(&[("cond", "bool"), ("x", "i32")]);
    let result = lower_syn_expr(&expr, &env);
    assert!(matches!(result, Err(LoweringError::MissingElseBranch)));
}

// === Match expression ===

#[test]
fn lower_empty_match_fails_closed() {
    let expr: syn::Expr = syn::parse_str("match x {}").unwrap();
    let env = env_with(&[("x", "i32")]);
    let err = lower_syn_expr(&expr, &env).expect_err("empty match must fail closed");
    assert!(
        matches!(err, LoweringError::TypeInference(_)),
        "expected TypeInference for empty match, got: {err:?}"
    );
    let msg = err.to_string();
    assert!(
        msg.contains("zero arms"),
        "error should mention empty/zero-arm match, got: {msg}",
    );
}

#[test]
fn lower_match_constructor_patterns_bind_datatype_fields() {
    let expr: syn::Expr = syn::parse_str("match opt { Some(x) => x, None => 0 }").unwrap();
    let env = env_with(&[("opt", "Option<u64>")]);
    let result = lower_syn_expr(&expr, &env).expect("constructor-pattern match should lower");

    let TrustVcExpr::Match { arms, .. } = result else {
        panic!("expected lowered match expression");
    };
    assert_eq!(arms.len(), 2);
    assert_eq!(
        arms[0].pattern,
        MatchPattern::Constructor {
            variant_name: "Some".to_string(),
            bindings: vec!["x".to_string()],
            has_rest: false,
        }
    );
    assert_eq!(
        arms[1].pattern,
        MatchPattern::Constructor {
            variant_name: "None".to_string(),
            bindings: vec![],
            has_rest: false,
        }
    );
    assert_eq!(
        arms[0].body,
        TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::Uint { width: 64 },
        }
    );
}

#[test]
fn lower_match_bare_identifier_still_binds_when_not_a_variant() {
    let expr: syn::Expr = syn::parse_str("match opt { whole => whole }").unwrap();
    let env = env_with(&[("opt", "Option<u64>")]);
    let result = lower_syn_expr(&expr, &env).expect("identifier pattern should lower");

    let TrustVcExpr::Match { arms, .. } = result else {
        panic!("expected lowered match expression");
    };
    assert_eq!(arms.len(), 1);
    assert_eq!(arms[0].pattern, MatchPattern::Ident("whole".to_string()));
    assert_eq!(
        arms[0].body,
        TrustVcExpr::Var {
            name: "whole".to_string(),
            ty: TrustVcType::from_str("Option<u64>").unwrap(),
        }
    );
}

#[test]
fn lower_match_named_struct_pattern_preserves_field_names() {
    let expr: syn::Expr =
        syn::parse_str("match counter { Counter { max: _, count } => count }").unwrap();
    let mut env = TypeEnv::new();
    env.insert(
        "counter".to_string(),
        TrustVcType::Datatype {
            name: "Counter".to_string(),
            variants: vec![DatatypeVariant::new(
                "Counter",
                vec![
                    ("count".to_string(), TrustVcType::Uint { width: 32 }),
                    ("max".to_string(), TrustVcType::Uint { width: 32 }),
                ],
            )],
        },
    );

    let result = lower_syn_expr(&expr, &env).expect("named-field struct pattern should lower");
    let TrustVcExpr::Match { arms, .. } = result else {
        panic!("expected lowered match expression");
    };
    assert_eq!(arms.len(), 1);
    assert_eq!(
        arms[0].pattern,
        MatchPattern::Struct {
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
        }
    );
    assert_eq!(
        arms[0].body,
        TrustVcExpr::Var {
            name: "count".to_string(),
            ty: TrustVcType::Uint { width: 32 },
        }
    );
}

#[test]
fn lower_match_named_struct_pattern_supports_field_aliases() {
    let expr: syn::Expr =
        syn::parse_str("match counter { Counter { count: current, max: _ } => current }").unwrap();
    let mut env = TypeEnv::new();
    env.insert(
        "counter".to_string(),
        TrustVcType::Datatype {
            name: "Counter".to_string(),
            variants: vec![DatatypeVariant::new(
                "Counter",
                vec![
                    ("count".to_string(), TrustVcType::Uint { width: 32 }),
                    ("max".to_string(), TrustVcType::Uint { width: 32 }),
                ],
            )],
        },
    );

    let result = lower_syn_expr(&expr, &env).expect("aliased struct field pattern should lower");
    let TrustVcExpr::Match { arms, .. } = result else {
        panic!("expected lowered match expression");
    };
    assert_eq!(arms.len(), 1);
    assert_eq!(
        arms[0].pattern,
        MatchPattern::Struct {
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
        }
    );
    assert_eq!(
        arms[0].body,
        TrustVcExpr::Var {
            name: "current".to_string(),
            ty: TrustVcType::Uint { width: 32 },
        }
    );
}

#[test]
fn lower_match_named_struct_pattern_supports_rest() {
    let expr: syn::Expr =
        syn::parse_str("match counter { Counter { count, .. } => count }").unwrap();
    let mut env = TypeEnv::new();
    env.insert(
        "counter".to_string(),
        TrustVcType::Datatype {
            name: "Counter".to_string(),
            variants: vec![DatatypeVariant::new(
                "Counter",
                vec![
                    ("count".to_string(), TrustVcType::Uint { width: 32 }),
                    ("max".to_string(), TrustVcType::Uint { width: 32 }),
                ],
            )],
        },
    );

    let result =
        lower_syn_expr(&expr, &env).expect("named-field struct pattern with rest should lower");
    let TrustVcExpr::Match { arms, .. } = result else {
        panic!("expected lowered match expression");
    };
    assert_eq!(
        arms[0].pattern,
        MatchPattern::Struct {
            variant_name: "Counter".to_string(),
            fields: vec![StructPatternField {
                field_name: "count".to_string(),
                binding: Some("count".to_string()),
            }],
            has_rest: true,
        }
    );
}

#[test]
fn lower_match_guard_lowers_to_guard_field() {
    let unguarded_expr: syn::Expr = syn::parse_str("match x { 0 => 1, _ => 2 }").unwrap();
    let guarded_expr: syn::Expr = syn::parse_str("match x { 0 if x > 5 => 1, _ => 2 }").unwrap();
    let env = env_with(&[("x", "i32")]);

    let unguarded =
        lower_syn_expr(&unguarded_expr, &env).expect("unguarded match should lower successfully");
    let TrustVcExpr::Match { arms, .. } = &unguarded else {
        panic!("unguarded counterpart should lower to Match IR, got: {unguarded:?}");
    };
    assert!(
        arms.iter().all(|arm| arm.guard.is_none()),
        "unguarded arms must carry no guard"
    );

    // A guard now lowers into the arm's `guard` field (no longer dropped or rejected).
    let guarded = lower_syn_expr(&guarded_expr, &env).expect("guarded match should now lower");
    let TrustVcExpr::Match { arms, .. } = &guarded else {
        panic!("guarded match should lower to Match IR, got: {guarded:?}");
    };
    assert!(
        arms[0].guard.is_some(),
        "the first arm's `if x > 5` guard must be captured in the guard field"
    );
    assert!(
        arms[1].guard.is_none(),
        "the trailing wildcard arm has no guard"
    );
}

#[test]
fn lower_non_bool_match_guard_fails_closed() {
    // A non-boolean guard is rejected fail-closed (cannot be encoded as a condition).
    let expr: syn::Expr = syn::parse_str("match x { 0 if x => 1, _ => 2 }").unwrap();
    let env = env_with(&[("x", "i32")]);
    let err = lower_syn_expr(&expr, &env).expect_err("non-bool guard must fail closed");
    assert!(
        matches!(err, LoweringError::UnsupportedPattern(_)) && err.to_string().contains("boolean"),
        "non-bool guard should be rejected as non-boolean, got: {err:?}"
    );
}

// === Paren / Group ===

#[test]
fn lower_paren_passthrough() {
    let expr: syn::Expr = syn::parse_str("(x)").unwrap();
    let env = env_with(&[("x", "i32")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert_eq!(
        result,
        TrustVcExpr::Var {
            name: "x".into(),
            ty: TrustVcType::Int { width: 32 }
        }
    );
}

// === Unsupported variants return errors ===

#[test]
fn lower_assign_fails() {
    let expr: syn::Expr = syn::parse_str("x = 5").unwrap();
    let env = env_with(&[("x", "i32")]);
    let result = lower_syn_expr(&expr, &env);
    assert!(matches!(result, Err(LoweringError::UnsupportedExpr(_))));
}

#[test]
fn lower_field_access_fails() {
    let expr: syn::Expr = syn::parse_str("s.field").unwrap();
    let env = env_with(&[("s", "i32")]);
    let err = lower_syn_expr(&expr, &env).expect_err("non-datatype field access must fail");
    assert!(matches!(err, LoweringError::UnsupportedExpr(_)));
    assert!(
        err.to_string().contains("field 'field' on type 'i32'"),
        "error should describe the missing field receiver, got: {err}",
    );
}

#[test]
#[allow(clippy::type_complexity)]
fn lower_multiple_unsupported_variants_fail_closed() {
    let cases: [(&str, &[(&str, &str)], &str); 20] = [
        (
            "s.missing",
            &[("s", "i32")],
            "field 'missing' on type 'i32'",
        ),
        ("0..10", &[], "range"),
        ("x = 5", &[("x", "i32")], "assignment"),
        ("async { 1 }", &[], "async block"),
        ("foo.await", &[("foo", "i32")], "await"),
        ("break", &[], "break"),
        ("continue", &[], "continue"),
        (
            "Missing { x: 1 }",
            &[],
            "struct literal for unknown type 'Missing'",
        ),
        ("foo?", &[("foo", "i32")], "try (?)"),
        ("const { 1 }", &[], "const block"),
        ("_", &[], "infer (_)"),
        ("|x: i32| x + 1", &[], "standalone closure"),
        (
            // A DIRECT `if let` now desugars to a sound match (see
            // `lower_if`/`desugar_if_let`); a let-CHAIN (`&& b`) still fails
            // closed because the desugar fires ONLY on a direct `Expr::Let`
            // condition, so the let wrapped in the `&&` reaches the backstop.
            "if let Some(x) = y && b { x } else { 0 }",
            &[("y", "i32"), ("b", "bool")],
            "if-let pattern",
        ),
        ("while x > 0 { break; }", &[("x", "i32")], "while loop"),
        ("loop { break; }", &[], "loop"),
        ("for x in y { break; }", &[("y", "Seq<i32>")], "for loop"),
        ("unsafe { 1 }", &[], "unsafe block"),
        ("foo!()", &[], "macro"),
        ("&raw const x", &[("x", "i32")], "raw address"),
        ("return", &[], "return without value"),
    ];

    for (expr_src, vars, expected) in cases {
        assert_unsupported_expr(expr_src, vars, expected);
    }
}

// === Reference expression ===

#[test]
fn lower_immutable_ref_is_identity() {
    let expr: syn::Expr = syn::parse_str("&x").unwrap();
    let env = env_with(&[("x", "i32")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert_eq!(
        result,
        TrustVcExpr::Var {
            name: "x".into(),
            ty: TrustVcType::Int { width: 32 }
        }
    );
}

#[test]
fn lower_mutable_ref_fails() {
    let expr: syn::Expr = syn::parse_str("&mut x").unwrap();
    let env = env_with(&[("x", "i32")]);
    let result = lower_syn_expr(&expr, &env);
    assert!(matches!(result, Err(LoweringError::UnsupportedExpr(_))));
}

// === Return expression ===

#[test]
fn lower_return_with_value() {
    let expr: syn::Expr = syn::parse_str("return x").unwrap();
    let env = env_with(&[("x", "i32")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert_eq!(
        result,
        TrustVcExpr::Var {
            name: "x".into(),
            ty: TrustVcType::Int { width: 32 }
        }
    );
}

// === Block expression ===

#[test]
fn lower_empty_block_as_unit() {
    let expr: syn::Expr = syn::parse_str("{}").unwrap();
    let result = lower_syn_expr(&expr, &TypeEnv::new()).unwrap();
    assert_eq!(result, TrustVcExpr::UnitLit);
}

#[test]
fn lower_block_with_trailing_semicolon_as_unit() {
    let expr: syn::Expr = syn::parse_str("{ x; }").unwrap();
    let env = env_with(&[("x", "i32")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    assert_eq!(result, TrustVcExpr::UnitLit);
}

#[test]
fn lower_typed_std_collection_default_locals_to_empty_constructors() {
    for (src, expected_ty) in [
        (
            "{ let v: Vec<u32> = Vec::default(); v }",
            TrustVcType::from_str("Vec<u32>").unwrap(),
        ),
        (
            "{ let m: HashMap<u32, bool> = HashMap::default(); m }",
            TrustVcType::from_str("HashMap<u32, bool>").unwrap(),
        ),
        (
            "{ let s: HashSet<u32> = HashSet::default(); s }",
            TrustVcType::from_str("HashSet<u32>").unwrap(),
        ),
    ] {
        let expr: syn::Expr = syn::parse_str(src).unwrap();
        let result = lower_syn_expr(&expr, &TypeEnv::new())
            .unwrap_or_else(|err| panic!("{src} should lower: {err}"));
        let TrustVcExpr::Let {
            value, ty, body, ..
        } = result
        else {
            panic!("expected typed default local to lower as Let");
        };
        assert_eq!(ty, expected_ty);
        match *value {
            TrustVcExpr::FnCall {
                name,
                args,
                return_ty,
            } => {
                assert!(name.starts_with(COLLECTION_CONSTRUCTOR_PREFIX));
                assert!(name.ends_with("_new"));
                assert!(args.is_empty());
                assert_eq!(return_ty, expected_ty);
            }
            other => panic!("expected empty collection constructor, got {other:?}"),
        }
        assert_eq!(infer_expr_type(&body), expected_ty);
    }
}

#[test]
fn test_block_trailing_let_statement_rejected() {
    let expr: syn::Expr = syn::parse_str("{ let y = 1; }").unwrap();
    let env = env_with(&[]);
    match lower_syn_expr(&expr, &env) {
        Err(LoweringError::UnsupportedExpr(msg)) => {
            assert!(
                msg.contains("unit-valued block"),
                "expected unit-valued block error, got: {msg}"
            );
        }
        Err(other) => panic!("expected UnsupportedExpr, got: {other:?}"),
        Ok(result) => panic!("expected error for trailing let statement, got: {result:?}"),
    }
}

#[test]
fn test_block_trailing_let_statement_in_nested_lower_stmts_rejected() {
    let expr: syn::Expr = syn::parse_str("{ let a = 1; let b = a + 1; }").unwrap();
    let env = env_with(&[]);
    match lower_syn_expr(&expr, &env) {
        Err(LoweringError::UnsupportedExpr(msg)) => {
            assert!(
                msg.contains("unit-valued block"),
                "expected unit-valued block error, got: {msg}"
            );
        }
        Err(other) => panic!("expected UnsupportedExpr, got: {other:?}"),
        Ok(result) => panic!("expected error for nested trailing let statement, got: {result:?}"),
    }
}

#[test]
fn lower_block_assignment_statement_as_scoped_let() {
    let expr: syn::Expr = syn::parse_str("{ a = a + 1u64; a }").unwrap();
    let env = env_with(&[("a", "u64")]);
    let result = lower_syn_expr(&expr, &env).expect("assignment block should lower");

    let TrustVcExpr::Let {
        name,
        ty,
        value,
        body,
    } = result
    else {
        panic!("expected assignment block to lower to a scoped Let");
    };
    assert_eq!(name, "a");
    assert_eq!(ty, TrustVcType::Uint { width: 64 });
    assert!(matches!(
        value.as_ref(),
        TrustVcExpr::Arith {
            op: ArithOp::Add,
            ty: TrustVcType::Uint { width: 64 },
            ..
        }
    ));
    assert_eq!(
        body.as_ref(),
        &TrustVcExpr::Var {
            name: "a".to_string(),
            ty: TrustVcType::Uint { width: 64 },
        }
    );
}

#[test]
fn lower_block_indexed_assignment_as_update_let() {
    let expr: syn::Expr = syn::parse_str("{ a[1] = 9; a[1] }").unwrap();
    let env = env_with(&[("a", "Seq<i32>")]);
    let result = lower_syn_expr(&expr, &env).expect("indexed assignment block should lower");

    let TrustVcExpr::Let {
        name,
        ty,
        value,
        body,
    } = result
    else {
        panic!("expected indexed assignment block to lower to a scoped Let");
    };
    assert_eq!(name, "a");
    assert_eq!(
        ty,
        TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }))
    );
    assert!(matches!(
        value.as_ref(),
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Update,
            receiver_name: Some(receiver_name),
            args,
            ty: TrustVcType::Seq(_),
            ..
        } if receiver_name == "a" && args.len() == 2
    ));
    assert!(matches!(
        body.as_ref(),
        TrustVcExpr::Index {
            receiver,
            elem_ty: TrustVcType::Int { width: 32 },
            ..
        } if matches!(
            receiver.as_ref(),
            TrustVcExpr::Var {
                name,
                ty: TrustVcType::Seq(_)
            } if name == "a"
        )
    ));
}

#[test]
fn lower_block_indexed_compound_assignment_as_update_let() {
    let expr: syn::Expr = syn::parse_str("{ a[1] += 8; a[1] }").unwrap();
    let env = env_with(&[("a", "Seq<i32>")]);
    let result =
        lower_syn_expr(&expr, &env).expect("indexed compound assignment block should lower");

    let TrustVcExpr::Let {
        name,
        ty,
        value,
        body,
    } = result
    else {
        panic!("expected indexed compound assignment block to lower to a scoped Let");
    };
    assert_eq!(name, "a");
    assert_eq!(
        ty,
        TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 }))
    );
    assert!(matches!(
        value.as_ref(),
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Update,
            receiver_name: Some(receiver_name),
            args,
            ty: TrustVcType::Seq(_),
            ..
        } if receiver_name == "a"
            && args.len() == 2
            && matches!(
                &args[1],
                TrustVcExpr::Arith {
                    op: ArithOp::Add,
                    left,
                    right,
                    ty: TrustVcType::Int { width: 32 },
                } if matches!(
                    left.as_ref(),
                    TrustVcExpr::Index {
                        elem_ty: TrustVcType::Int { width: 32 },
                        ..
                    }
                ) && matches!(
                    right.as_ref(),
                    TrustVcExpr::IntLit {
                        value: 8,
                        ty: TrustVcType::Int { width: 32 },
                    }
                )
            )
    ));
    assert!(matches!(
        body.as_ref(),
        TrustVcExpr::Index {
            receiver,
            elem_ty: TrustVcType::Int { width: 32 },
            ..
        } if matches!(
            receiver.as_ref(),
            TrustVcExpr::Var {
                name,
                ty: TrustVcType::Seq(_)
            } if name == "a"
        )
    ));
}

#[test]
fn lower_block_nested_indexed_assignment_as_nested_update_let() {
    let expr: syn::Expr = syn::parse_str("{ x[0][1] = 9; x[0][1] }").unwrap();
    let env = env_with(&[("x", "[[u64; 2]; 2]")]);
    let result = lower_syn_expr(&expr, &env).expect("nested indexed assignment block should lower");

    let TrustVcExpr::Let {
        name, value, body, ..
    } = result
    else {
        panic!("expected nested indexed assignment block to lower to a scoped Let");
    };
    assert_eq!(name, "x");
    assert!(matches!(
        value.as_ref(),
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Update,
            receiver_name: Some(receiver_name),
            args,
            ty: TrustVcType::Array(_, 2),
            ..
        } if receiver_name == "x"
            && args.len() == 2
            && matches!(
                &args[1],
                TrustVcExpr::CollectionOp {
                    op: CollectionOp::Update,
                    receiver_name: None,
                    args: inner_args,
                    ty: TrustVcType::Array(_, 2),
                    ..
                } if inner_args.len() == 2
            )
    ));
    assert!(matches!(
        body.as_ref(),
        TrustVcExpr::Index {
            receiver,
            elem_ty: TrustVcType::Uint { width: 64 },
            ..
        } if matches!(receiver.as_ref(), TrustVcExpr::Index { .. })
    ));
}

#[test]
fn lower_block_nested_indexed_compound_assignment_as_nested_update_let() {
    let expr: syn::Expr = syn::parse_str("{ x[0][0] += 5; x[0][0] }").unwrap();
    let env = env_with(&[("x", "[[u64; 2]; 2]")]);
    let result =
        lower_syn_expr(&expr, &env).expect("nested indexed compound assignment block should lower");

    let TrustVcExpr::Let { name, value, .. } = result else {
        panic!("expected nested indexed compound assignment block to lower to a scoped Let");
    };
    assert_eq!(name, "x");
    assert!(matches!(
        value.as_ref(),
        TrustVcExpr::CollectionOp {
            op: CollectionOp::Update,
            receiver_name: Some(receiver_name),
            args,
            ..
        } if receiver_name == "x"
            && args.len() == 2
            && matches!(
                &args[1],
                TrustVcExpr::CollectionOp {
                    op: CollectionOp::Update,
                    receiver_name: None,
                    args: inner_args,
                    ..
                } if inner_args.len() == 2
                    && matches!(
                        &inner_args[1],
                        TrustVcExpr::Arith {
                            op: ArithOp::Add,
                            left,
                            right,
                            ty: TrustVcType::Uint { width: 64 },
                        } if matches!(
                            left.as_ref(),
                            TrustVcExpr::Index {
                                receiver,
                                elem_ty: TrustVcType::Uint { width: 64 },
                                ..
                            } if matches!(receiver.as_ref(), TrustVcExpr::Index { .. })
                        ) && matches!(
                            right.as_ref(),
                            TrustVcExpr::IntLit {
                                value: 5,
                                ty: TrustVcType::Uint { width: 64 },
                            }
                        )
                    )
            )
    ));
}

#[test]
fn lower_block_parenthesized_indexed_compound_assignment_as_update_let() {
    let expr: syn::Expr = syn::parse_str("{ (a[1]) += 8; a[1] }").unwrap();
    let env = env_with(&[("a", "Seq<i32>")]);
    let result = lower_syn_expr(&expr, &env)
        .expect("parenthesized indexed compound assignment block should lower");

    assert!(matches!(
        result,
        TrustVcExpr::Let {
            name,
            value,
            ..
        } if name == "a"
            && matches!(
                value.as_ref(),
                TrustVcExpr::CollectionOp {
                    op: CollectionOp::Update,
                    receiver_name: Some(receiver_name),
                    ..
                } if receiver_name == "a"
            )
    ));
}

#[test]
fn lower_helper_call_preserves_statement_expression_argument_shape() {
    let expr: syn::Expr = syn::parse_str("id({ a = a + 1u64; a })").unwrap();
    let mut env = env_with(&[("a", "u64")]);
    env.insert_fn("id".to_string(), TrustVcType::Uint { width: 64 });
    env.insert_fn_params("id".to_string(), vec![TrustVcType::Uint { width: 64 }]);

    let result =
        lower_syn_expr(&expr, &env).expect("helper call with assignment block should lower");
    let TrustVcExpr::FnCall { name, args, .. } = result else {
        panic!("expected helper call to stay a FnCall");
    };
    assert_eq!(name, "id");
    assert_eq!(args.len(), 1);
    assert!(
        matches!(args.first(), Some(TrustVcExpr::Let { name, .. }) if name == "a"),
        "statement-expression argument should lower inside the call, got: {args:?}"
    );
}

// === ITE branch literal coercion (#1560) ===

#[test]
fn lower_if_coerces_then_literal_to_else_type() {
    // `if cond { 0 } else { x }` where x: u8 → then literal coerced to Uint{8}
    let expr: syn::Expr = syn::parse_str("if cond { 0 } else { x }").unwrap();
    let env = env_with(&[("cond", "bool"), ("x", "u8")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::Ite {
            then_branch,
            else_branch,
            ty,
            ..
        } => {
            assert_eq!(
                *then_branch,
                TrustVcExpr::IntLit {
                    value: 0,
                    ty: TrustVcType::Uint { width: 8 }
                },
                "unsuffixed literal in then branch should be coerced to u8"
            );
            assert_eq!(
                *else_branch,
                TrustVcExpr::Var {
                    name: "x".into(),
                    ty: TrustVcType::Uint { width: 8 }
                },
            );
            assert_eq!(ty, TrustVcType::Uint { width: 8 });
        }
        other => panic!("expected Ite, got: {other:?}"),
    }
}

#[test]
fn lower_if_coerces_else_literal_to_then_type() {
    // `if cond { y } else { 1 }` where y: i64 → else literal coerced to Int{64}
    let expr: syn::Expr = syn::parse_str("if cond { y } else { 1 }").unwrap();
    let env = env_with(&[("cond", "bool"), ("y", "i64")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::Ite {
            then_branch,
            else_branch,
            ty,
            ..
        } => {
            assert_eq!(
                *else_branch,
                TrustVcExpr::IntLit {
                    value: 1,
                    ty: TrustVcType::Int { width: 64 }
                },
                "unsuffixed literal in else branch should be coerced to i64"
            );
            assert_eq!(ty, TrustVcType::Int { width: 64 });
            assert_eq!(
                *then_branch,
                TrustVcExpr::Var {
                    name: "y".into(),
                    ty: TrustVcType::Int { width: 64 }
                },
            );
        }
        other => panic!("expected Ite, got: {other:?}"),
    }
}

#[test]
fn lower_if_no_coercion_when_both_branches_typed() {
    // Both branches are variables with explicit types — no coercion needed
    let expr: syn::Expr = syn::parse_str("if cond { x } else { y }").unwrap();
    let env = env_with(&[("cond", "bool"), ("x", "i32"), ("y", "i32")]);
    let result = lower_syn_expr(&expr, &env).unwrap();
    match result {
        TrustVcExpr::Ite {
            then_branch,
            else_branch,
            ..
        } => {
            assert_eq!(
                *then_branch,
                TrustVcExpr::Var {
                    name: "x".into(),
                    ty: TrustVcType::Int { width: 32 }
                },
            );
            assert_eq!(
                *else_branch,
                TrustVcExpr::Var {
                    name: "y".into(),
                    ty: TrustVcType::Int { width: 32 }
                },
            );
        }
        other => panic!("expected Ite, got: {other:?}"),
    }
}
