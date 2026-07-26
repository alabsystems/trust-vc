// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// -- Parser: basic expressions --

#[test]
fn test_parse_expr_variable() {
    let expr = SpecParser::parse_expr("x").unwrap();
    assert_eq!(expr, SpecExpr::Variable("x".to_string()));
}

#[test]
fn test_parse_expr_int_literal() {
    let expr = SpecParser::parse_expr("42").unwrap();
    assert_eq!(expr, SpecExpr::IntLit(42));
}

#[test]
fn test_parse_expr_negative_int() {
    let expr = SpecParser::parse_expr("-7").unwrap();
    assert_eq!(expr, SpecExpr::IntLit(-7));
}

#[test]
fn test_parse_expr_bool_true() {
    let expr = SpecParser::parse_expr("true").unwrap();
    assert_eq!(expr, SpecExpr::BoolLit(true));
}

#[test]
fn test_parse_expr_bool_false() {
    let expr = SpecParser::parse_expr("false").unwrap();
    assert_eq!(expr, SpecExpr::BoolLit(false));
}

// -- Parser: binary operators --

#[test]
fn test_parse_expr_addition() {
    let expr = SpecParser::parse_expr("x + 1").unwrap();
    assert_eq!(
        expr,
        SpecExpr::BinOp(
            Box::new(SpecExpr::Variable("x".to_string())),
            BinOpKind::Add,
            Box::new(SpecExpr::IntLit(1)),
        )
    );
}

#[test]
fn test_parse_expr_precedence_mul_over_add() {
    // x + y * z => x + (y * z)
    let expr = SpecParser::parse_expr("x + y * z").unwrap();
    assert_eq!(
        expr,
        SpecExpr::BinOp(
            Box::new(SpecExpr::Variable("x".to_string())),
            BinOpKind::Add,
            Box::new(SpecExpr::BinOp(
                Box::new(SpecExpr::Variable("y".to_string())),
                BinOpKind::Mul,
                Box::new(SpecExpr::Variable("z".to_string())),
            )),
        )
    );
}

#[test]
fn test_parse_expr_comparison_eq() {
    let expr = SpecParser::parse_expr("x == 0").unwrap();
    assert_eq!(
        expr,
        SpecExpr::BinOp(
            Box::new(SpecExpr::Variable("x".to_string())),
            BinOpKind::Eq,
            Box::new(SpecExpr::IntLit(0)),
        )
    );
}

#[test]
fn test_parse_expr_implies() {
    let expr = SpecParser::parse_expr("a ==> b").unwrap();
    assert_eq!(
        expr,
        SpecExpr::BinOp(
            Box::new(SpecExpr::Variable("a".to_string())),
            BinOpKind::Implies,
            Box::new(SpecExpr::Variable("b".to_string())),
        )
    );
}

#[test]
fn test_parse_expr_and_or_precedence() {
    // a || b && c => a || (b && c)
    let expr = SpecParser::parse_expr("a || b && c").unwrap();
    assert_eq!(
        expr,
        SpecExpr::BinOp(
            Box::new(SpecExpr::Variable("a".to_string())),
            BinOpKind::Or,
            Box::new(SpecExpr::BinOp(
                Box::new(SpecExpr::Variable("b".to_string())),
                BinOpKind::And,
                Box::new(SpecExpr::Variable("c".to_string())),
            )),
        )
    );
}

// -- Parser: unary operators --

#[test]
fn test_parse_expr_not() {
    let expr = SpecParser::parse_expr("!x").unwrap();
    assert_eq!(
        expr,
        SpecExpr::UnaryOp(
            UnaryOpKind::Not,
            Box::new(SpecExpr::Variable("x".to_string()))
        )
    );
}

// -- Parser: function calls --

#[test]
fn test_parse_expr_fn_call_no_args() {
    let expr = SpecParser::parse_expr("foo()").unwrap();
    assert_eq!(expr, SpecExpr::FnCall("foo".to_string(), vec![]));
}

#[test]
fn test_parse_expr_fn_call_two_args() {
    let expr = SpecParser::parse_expr("max(x, y)").unwrap();
    assert_eq!(
        expr,
        SpecExpr::FnCall(
            "max".to_string(),
            vec![
                SpecExpr::Variable("x".to_string()),
                SpecExpr::Variable("y".to_string()),
            ],
        )
    );
}

// -- Parser: old, field access, index access, if-then-else --

#[test]
fn test_parse_expr_old() {
    let expr = SpecParser::parse_expr("old(x)").unwrap();
    assert_eq!(
        expr,
        SpecExpr::Old(Box::new(SpecExpr::Variable("x".to_string())))
    );
}

#[test]
fn test_parse_expr_field_access() {
    let expr = SpecParser::parse_expr("s.len").unwrap();
    assert_eq!(
        expr,
        SpecExpr::FieldAccess(
            Box::new(SpecExpr::Variable("s".to_string())),
            "len".to_string(),
        )
    );
}

#[test]
fn test_parse_expr_index_access() {
    let expr = SpecParser::parse_expr("a[i]").unwrap();
    assert_eq!(
        expr,
        SpecExpr::IndexAccess(
            Box::new(SpecExpr::Variable("a".to_string())),
            Box::new(SpecExpr::Variable("i".to_string())),
        )
    );
}

#[test]
fn test_parse_expr_if_then_else() {
    let expr = SpecParser::parse_expr("if x then 1 else 0").unwrap();
    assert_eq!(
        expr,
        SpecExpr::IfThenElse(
            Box::new(SpecExpr::Variable("x".to_string())),
            Box::new(SpecExpr::IntLit(1)),
            Box::new(SpecExpr::IntLit(0)),
        )
    );
}

// -- Parser: quantifiers --

#[test]
fn test_parse_expr_forall() {
    let expr = SpecParser::parse_expr("forall i: int :: a[i] >= 0").unwrap();
    assert_eq!(
        expr,
        SpecExpr::Quantifier(
            QuantKind::Forall,
            vec![("i".to_string(), "int".to_string())],
            Box::new(SpecExpr::BinOp(
                Box::new(SpecExpr::IndexAccess(
                    Box::new(SpecExpr::Variable("a".to_string())),
                    Box::new(SpecExpr::Variable("i".to_string())),
                )),
                BinOpKind::Ge,
                Box::new(SpecExpr::IntLit(0)),
            )),
        )
    );
}

#[test]
fn test_parse_expr_exists_multi_binding() {
    let expr = SpecParser::parse_expr("exists i: int, j: int :: i + j == n").unwrap();
    match &expr {
        SpecExpr::Quantifier(QuantKind::Exists, bindings, _) => {
            assert_eq!(bindings.len(), 2);
            assert_eq!(bindings[0], ("i".to_string(), "int".to_string()));
            assert_eq!(bindings[1], ("j".to_string(), "int".to_string()));
        }
        other => panic!("expected Quantifier, got {other:?}"),
    }
}

// -- Parser: parentheses --

#[test]
fn test_parse_expr_parenthesized() {
    let expr = SpecParser::parse_expr("(x + y) * z").unwrap();
    assert_eq!(
        expr,
        SpecExpr::BinOp(
            Box::new(SpecExpr::BinOp(
                Box::new(SpecExpr::Variable("x".to_string())),
                BinOpKind::Add,
                Box::new(SpecExpr::Variable("y".to_string())),
            )),
            BinOpKind::Mul,
            Box::new(SpecExpr::Variable("z".to_string())),
        )
    );
}

// -- Parser: error cases --

#[test]
fn test_parse_expr_empty_input_error() {
    let err = SpecParser::parse_expr("").unwrap_err();
    assert!(
        err.message.contains("unexpected end"),
        "got: {}",
        err.message
    );
}

#[test]
fn test_parse_expr_trailing_content_error() {
    let err = SpecParser::parse_expr("x y").unwrap_err();
    assert!(err.message.contains("trailing"), "got: {}", err.message);
}

// -- Parser: clauses --

#[test]
fn test_parse_clause_requires() {
    let clause = SpecParser::parse_clause("requires x > 0").unwrap();
    assert_eq!(
        clause,
        SpecClause::Requires(SpecExpr::BinOp(
            Box::new(SpecExpr::Variable("x".to_string())),
            BinOpKind::Gt,
            Box::new(SpecExpr::IntLit(0)),
        ))
    );
}

#[test]
fn test_parse_clause_ensures() {
    let clause = SpecParser::parse_clause("ensures result >= 0").unwrap();
    assert_eq!(
        clause,
        SpecClause::Ensures(SpecExpr::BinOp(
            Box::new(SpecExpr::Variable("result".to_string())),
            BinOpKind::Ge,
            Box::new(SpecExpr::IntLit(0)),
        ))
    );
}

#[test]
fn test_parse_clause_invariant() {
    let clause = SpecParser::parse_clause("invariant i < n").unwrap();
    assert_eq!(
        clause,
        SpecClause::Invariant(SpecExpr::BinOp(
            Box::new(SpecExpr::Variable("i".to_string())),
            BinOpKind::Lt,
            Box::new(SpecExpr::Variable("n".to_string())),
        ))
    );
}

#[test]
fn test_parse_clause_decreases() {
    let clause = SpecParser::parse_clause("decreases n").unwrap();
    assert_eq!(
        clause,
        SpecClause::Decreases(SpecExpr::Variable("n".to_string()))
    );
}

#[test]
fn test_parse_clause_bad_keyword_error() {
    let err = SpecParser::parse_clause("foobar x").unwrap_err();
    assert!(err.message.contains("expected"), "got: {}", err.message);
}

// -- Parser: function specs --

#[test]
fn test_parse_function_spec_basic() {
    let spec =
        SpecParser::parse_function_spec("fn abs(x: i32) -> i32 requires true ensures result >= 0")
            .unwrap();
    assert_eq!(spec.name, "abs");
    assert_eq!(spec.params, vec![("x".to_string(), "i32".to_string())]);
    assert_eq!(spec.return_type.as_deref(), Some("i32"));
    assert_eq!(spec.clauses.len(), 2);
}

#[test]
fn test_parse_function_spec_no_return() {
    let spec =
        SpecParser::parse_function_spec("fn push(v: Vec<i32>, x: i32) requires x > 0").unwrap();
    assert_eq!(spec.name, "push");
    assert_eq!(spec.params.len(), 2);
    assert!(spec.return_type.is_none());
    assert_eq!(spec.clauses.len(), 1);
}

#[test]
fn test_parse_function_spec_no_params() {
    let spec = SpecParser::parse_function_spec("fn init() -> bool ensures result == true").unwrap();
    assert_eq!(spec.name, "init");
    assert!(spec.params.is_empty());
    assert_eq!(spec.return_type.as_deref(), Some("bool"));
}

// -- Printer: roundtrip --

#[test]
fn test_printer_roundtrip_variable() {
    let expr = SpecExpr::Variable("x".to_string());
    assert_eq!(SpecPrinter::to_string(&expr), "x");
}

#[test]
fn test_printer_roundtrip_binop() {
    let input = "x + y * z";
    let expr = SpecParser::parse_expr(input).unwrap();
    let printed = SpecPrinter::to_string(&expr);
    assert_eq!(printed, "x + y * z");
}

#[test]
fn test_printer_roundtrip_implies() {
    let input = "a ==> b || c";
    let expr = SpecParser::parse_expr(input).unwrap();
    let printed = SpecPrinter::to_string(&expr);
    // Re-parse to confirm structural equivalence.
    let reparsed = SpecParser::parse_expr(&printed).unwrap();
    assert_eq!(expr, reparsed);
}

#[test]
fn test_printer_parenthesizes_nested_or_in_and() {
    // (a || b) && c
    let expr = SpecExpr::BinOp(
        Box::new(SpecExpr::BinOp(
            Box::new(SpecExpr::Variable("a".to_string())),
            BinOpKind::Or,
            Box::new(SpecExpr::Variable("b".to_string())),
        )),
        BinOpKind::And,
        Box::new(SpecExpr::Variable("c".to_string())),
    );
    let printed = SpecPrinter::to_string(&expr);
    assert!(printed.contains('('), "should parenthesize: {printed}");
    // Re-parse must give back the same tree.
    let reparsed = SpecParser::parse_expr(&printed).unwrap();
    assert_eq!(expr, reparsed);
}

#[test]
fn test_printer_old_expression() {
    let expr = SpecExpr::Old(Box::new(SpecExpr::Variable("v".to_string())));
    assert_eq!(SpecPrinter::to_string(&expr), "old(v)");
}

#[test]
fn test_printer_quantifier() {
    let expr = SpecExpr::Quantifier(
        QuantKind::Forall,
        vec![("i".to_string(), "int".to_string())],
        Box::new(SpecExpr::BinOp(
            Box::new(SpecExpr::Variable("i".to_string())),
            BinOpKind::Ge,
            Box::new(SpecExpr::IntLit(0)),
        )),
    );
    let printed = SpecPrinter::to_string(&expr);
    assert_eq!(printed, "forall i: int :: i >= 0");
}

#[test]
fn test_printer_function_spec() {
    let spec = FunctionSpec {
        name: "inc".to_string(),
        params: vec![("x".to_string(), "i32".to_string())],
        return_type: Some("i32".to_string()),
        clauses: vec![SpecClause::Ensures(SpecExpr::BinOp(
            Box::new(SpecExpr::Variable("result".to_string())),
            BinOpKind::Eq,
            Box::new(SpecExpr::BinOp(
                Box::new(SpecExpr::Variable("x".to_string())),
                BinOpKind::Add,
                Box::new(SpecExpr::IntLit(1)),
            )),
        ))],
    };
    let printed = SpecPrinter::function_spec_to_string(&spec);
    assert!(printed.starts_with("fn inc(x: i32) -> i32"));
    assert!(printed.contains("ensures"));
}

// -- SpecExpr methods --

#[test]
fn test_free_variables_simple() {
    let expr = SpecParser::parse_expr("x + y").unwrap();
    let fv = expr.free_variables();
    assert!(fv.contains("x"));
    assert!(fv.contains("y"));
    assert_eq!(fv.len(), 2);
}

#[test]
fn test_free_variables_quantifier_binds() {
    let expr = SpecParser::parse_expr("forall i: int :: i + x").unwrap();
    let fv = expr.free_variables();
    // `i` is bound, `x` is free.
    assert!(!fv.contains("i"));
    assert!(fv.contains("x"));
    assert_eq!(fv.len(), 1);
}

#[test]
fn test_depth_leaf() {
    assert_eq!(SpecExpr::IntLit(0).depth(), 1);
}

#[test]
fn test_depth_nested() {
    let expr = SpecParser::parse_expr("(x + y) * z").unwrap();
    // tree:  * (depth 1)
    //        +  (depth 2)   z (depth 1)
    //       x y (depth 1 each)
    assert_eq!(expr.depth(), 3);
}

#[test]
fn test_complexity_leaf() {
    assert_eq!(SpecExpr::Variable("x".to_string()).complexity(), 1);
}

#[test]
fn test_complexity_binop() {
    let expr = SpecParser::parse_expr("x + y").unwrap();
    // 3 nodes: BinOp, Variable("x"), Variable("y")
    assert_eq!(expr.complexity(), 3);
}

// -- Transformer: substitute --

#[test]
fn test_substitute_simple() {
    let expr = SpecParser::parse_expr("x + 1").unwrap();
    let result = SpecTransformer::substitute(&expr, "x", &SpecExpr::Variable("y".to_string()));
    assert_eq!(result, SpecParser::parse_expr("y + 1").unwrap());
}

#[test]
fn test_substitute_respects_binding() {
    // In `forall x: int :: x + y`, substituting x should NOT replace the bound x.
    let expr = SpecParser::parse_expr("forall x: int :: x + y").unwrap();
    let result = SpecTransformer::substitute(&expr, "x", &SpecExpr::IntLit(99));
    // The bound x stays; only free x would be replaced (there is none).
    assert_eq!(result, expr);
}

#[test]
fn test_substitute_free_under_quantifier() {
    // forall i: int :: x + i, substitute x -> 5
    let expr = SpecParser::parse_expr("forall i: int :: x + i").unwrap();
    let result = SpecTransformer::substitute(&expr, "x", &SpecExpr::IntLit(5));
    let expected = SpecParser::parse_expr("forall i: int :: 5 + i").unwrap();
    assert_eq!(result, expected);
}

// -- Transformer: weaken --

#[test]
fn test_weaken_conjunction_drops_rhs() {
    let expr = SpecParser::parse_expr("x > 0 && y > 0").unwrap();
    let weakened = SpecTransformer::weaken(&expr);
    // Should become just `x > 0`.
    let expected = SpecParser::parse_expr("x > 0").unwrap();
    assert_eq!(weakened, expected);
}

#[test]
fn test_weaken_non_conjunction_disjoins_true() {
    let expr = SpecParser::parse_expr("x > 0").unwrap();
    let weakened = SpecTransformer::weaken(&expr);
    match &weakened {
        SpecExpr::BinOp(_, BinOpKind::Or, rhs) => {
            assert_eq!(**rhs, SpecExpr::BoolLit(true));
        }
        other => panic!("expected Or with true, got {other:?}"),
    }
}

// -- Transformer: strengthen --

#[test]
fn test_strengthen_adds_conjunction() {
    let expr = SpecParser::parse_expr("result == x + 1").unwrap();
    let strengthened = SpecTransformer::strengthen(&expr);
    match &strengthened {
        SpecExpr::BinOp(lhs, BinOpKind::And, rhs) => {
            assert_eq!(**lhs, expr);
            // rhs should be `result >= 0`
            match rhs.as_ref() {
                SpecExpr::BinOp(rl, BinOpKind::Ge, rr) => {
                    assert_eq!(**rl, SpecExpr::Variable("result".to_string()));
                    assert_eq!(**rr, SpecExpr::IntLit(0));
                }
                other => panic!("expected Ge, got {other:?}"),
            }
        }
        other => panic!("expected And, got {other:?}"),
    }
}

// -- FunctionSpec: merge --

#[test]
fn test_function_spec_merge_combines_clauses() {
    let s1 = FunctionSpec {
        name: "f".to_string(),
        params: vec![("x".to_string(), "i32".to_string())],
        return_type: Some("i32".to_string()),
        clauses: vec![SpecClause::Requires(SpecExpr::BinOp(
            Box::new(SpecExpr::Variable("x".to_string())),
            BinOpKind::Gt,
            Box::new(SpecExpr::IntLit(0)),
        ))],
    };
    let s2 = FunctionSpec {
        name: "f".to_string(),
        params: vec![],
        return_type: None,
        clauses: vec![SpecClause::Ensures(SpecExpr::BinOp(
            Box::new(SpecExpr::Variable("result".to_string())),
            BinOpKind::Ge,
            Box::new(SpecExpr::IntLit(0)),
        ))],
    };
    let merged = s1.merge(&s2);
    assert_eq!(merged.clauses.len(), 2);
    assert_eq!(merged.params.len(), 1); // kept from s1
    assert_eq!(merged.return_type.as_deref(), Some("i32"));
}

// -- FunctionSpec: validate --

#[test]
fn test_function_spec_validate_no_clauses() {
    let spec = FunctionSpec {
        name: "f".to_string(),
        params: vec![],
        return_type: None,
        clauses: vec![],
    };
    let warnings = spec.validate();
    assert!(warnings.iter().any(|w| w.contains("no specification")));
}

#[test]
fn test_function_spec_validate_unknown_variable() {
    let spec = FunctionSpec {
        name: "f".to_string(),
        params: vec![("x".to_string(), "i32".to_string())],
        return_type: None,
        clauses: vec![SpecClause::Requires(SpecExpr::Variable("z".to_string()))],
    };
    let warnings = spec.validate();
    assert!(warnings.iter().any(|w| w.contains("`z`")));
}

#[test]
fn test_function_spec_validate_result_is_ok() {
    let spec = FunctionSpec {
        name: "f".to_string(),
        params: vec![("x".to_string(), "i32".to_string())],
        return_type: Some("i32".to_string()),
        clauses: vec![SpecClause::Ensures(SpecExpr::Variable(
            "result".to_string(),
        ))],
    };
    let warnings = spec.validate();
    // `result` is allowed — no warnings about unknown variables.
    assert!(
        !warnings.iter().any(|w| w.contains("`result`")),
        "unexpected warning about result: {warnings:?}"
    );
}

#[test]
fn test_function_spec_validate_multiple_decreases() {
    let spec = FunctionSpec {
        name: "f".to_string(),
        params: vec![("n".to_string(), "u64".to_string())],
        return_type: None,
        clauses: vec![
            SpecClause::Decreases(SpecExpr::Variable("n".to_string())),
            SpecClause::Decreases(SpecExpr::Variable("n".to_string())),
        ],
    };
    let warnings = spec.validate();
    assert!(warnings.iter().any(|w| w.contains("multiple decreases")));
}

// -- Roundtrip: parse -> print -> reparse --

#[test]
fn test_roundtrip_complex_expression() {
    let input = "forall i: int :: 0 <= i && i < n ==> a[i] >= 0";
    let parsed = SpecParser::parse_expr(input).unwrap();
    let printed = SpecPrinter::to_string(&parsed);
    let reparsed = SpecParser::parse_expr(&printed).unwrap();
    assert_eq!(parsed, reparsed, "roundtrip failed: {input} -> {printed}");
}

#[test]
fn test_roundtrip_if_then_else() {
    let input = "if x > 0 then x else 0";
    let parsed = SpecParser::parse_expr(input).unwrap();
    let printed = SpecPrinter::to_string(&parsed);
    let reparsed = SpecParser::parse_expr(&printed).unwrap();
    assert_eq!(parsed, reparsed);
}

#[test]
fn test_roundtrip_fn_call_nested() {
    let input = "max(f(x), g(y, z))";
    let parsed = SpecParser::parse_expr(input).unwrap();
    let printed = SpecPrinter::to_string(&parsed);
    let reparsed = SpecParser::parse_expr(&printed).unwrap();
    assert_eq!(parsed, reparsed);
}

// -- Additional edge cases --

#[test]
fn test_parse_expr_chained_field_index() {
    let expr = SpecParser::parse_expr("a.b[i].c").unwrap();
    // Structure: FieldAccess(IndexAccess(FieldAccess(a, b), i), c)
    match &expr {
        SpecExpr::FieldAccess(base, field) => {
            assert_eq!(field, "c");
            match base.as_ref() {
                SpecExpr::IndexAccess(inner_base, _) => match inner_base.as_ref() {
                    SpecExpr::FieldAccess(root, f) => {
                        assert_eq!(f, "b");
                        assert_eq!(**root, SpecExpr::Variable("a".to_string()));
                    }
                    other => panic!("expected FieldAccess, got {other:?}"),
                },
                other => panic!("expected IndexAccess, got {other:?}"),
            }
        }
        other => panic!("expected FieldAccess, got {other:?}"),
    }
}

#[test]
fn test_parse_expr_le_ne_ge() {
    for (input, expected_op) in [
        ("x <= y", BinOpKind::Le),
        ("x != y", BinOpKind::Ne),
        ("x >= y", BinOpKind::Ge),
    ] {
        let expr = SpecParser::parse_expr(input).unwrap();
        match &expr {
            SpecExpr::BinOp(_, op, _) => assert_eq!(*op, expected_op, "for input: {input}"),
            other => panic!("expected BinOp for {input}, got {other:?}"),
        }
    }
}

#[test]
fn test_parse_expr_mod_operator() {
    let expr = SpecParser::parse_expr("x % 2 == 0").unwrap();
    match &expr {
        SpecExpr::BinOp(lhs, BinOpKind::Eq, _) => match lhs.as_ref() {
            SpecExpr::BinOp(_, BinOpKind::Mod, _) => {}
            other => panic!("expected Mod, got {other:?}"),
        },
        other => panic!("expected Eq, got {other:?}"),
    }
}

#[test]
fn test_parse_expr_div_operator() {
    let expr = SpecParser::parse_expr("x / y").unwrap();
    match &expr {
        SpecExpr::BinOp(_, BinOpKind::Div, _) => {}
        other => panic!("expected Div, got {other:?}"),
    }
}

#[test]
fn test_complexity_of_if_then_else() {
    let expr = SpecParser::parse_expr("if a then b else c").unwrap();
    // 4 nodes: IfThenElse + 3 variables
    assert_eq!(expr.complexity(), 4);
}

#[test]
fn test_depth_of_old() {
    let expr = SpecParser::parse_expr("old(x)").unwrap();
    assert_eq!(expr.depth(), 2);
}

#[test]
fn test_free_variables_in_old() {
    let expr = SpecParser::parse_expr("old(x) + y").unwrap();
    let fv = expr.free_variables();
    assert!(fv.contains("x"));
    assert!(fv.contains("y"));
    assert_eq!(fv.len(), 2);
}

#[test]
fn test_substitute_in_if_then_else() {
    let expr = SpecParser::parse_expr("if x then x else 0").unwrap();
    let result = SpecTransformer::substitute(&expr, "x", &SpecExpr::Variable("y".to_string()));
    let expected = SpecParser::parse_expr("if y then y else 0").unwrap();
    assert_eq!(result, expected);
}

#[test]
fn test_substitute_in_old() {
    let expr = SpecParser::parse_expr("old(x)").unwrap();
    let result = SpecTransformer::substitute(&expr, "x", &SpecExpr::IntLit(5));
    assert_eq!(result, SpecExpr::Old(Box::new(SpecExpr::IntLit(5))));
}
