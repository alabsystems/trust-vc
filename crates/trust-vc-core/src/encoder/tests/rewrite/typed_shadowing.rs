// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_typed_rename_respects_let_shadowing() {
    let expr = TrustVcExpr::Let {
        name: "x".to_string(),
        ty: i32_ty(),
        value: Box::new(int_lit(1)),
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(var("x")),
            right: Box::new(int_lit(0)),
        }),
    };
    let vars = make_vars(&["x"]);
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::Let { body, .. } = &result {
        if let TrustVcExpr::Compare { left, .. } = body.as_ref() {
            assert_eq!(**left, var("x"), "let-bound x should not be renamed");
        } else {
            panic!("expected Compare in let body");
        }
    } else {
        panic!("expected Let");
    }
}

#[test]
fn test_typed_rename_respects_quantifier_shadowing() {
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".to_string(), i32_ty())],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(var("x")),
            right: Box::new(int_lit(0)),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };
    let vars = make_vars(&["x"]);
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::Quantifier { body, .. } = &result {
        if let TrustVcExpr::Compare { left, .. } = body.as_ref() {
            assert_eq!(**left, var("x"), "quantifier-bound x should not be renamed");
        } else {
            panic!("expected Compare in quantifier body");
        }
    } else {
        panic!("expected Quantifier");
    }
}

// ---- Typed rewrite: deep nesting correctness ----

#[test]
fn test_typed_rename_deeply_nested_let_shadowing() {
    let vars = make_vars(&["x", "y", "z"]);
    let body = TrustVcExpr::Compare {
        op: CompareOp::Gt,
        left: Box::new(TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(var("x")),
            right: Box::new(TrustVcExpr::Arith {
                op: ArithOp::Add,
                left: Box::new(var("y")),
                right: Box::new(var("z")),
                ty: i32_ty(),
            }),
            ty: i32_ty(),
        }),
        right: Box::new(int_lit(0)),
    };

    let expr = TrustVcExpr::Let {
        name: "z".to_string(),
        ty: i32_ty(),
        value: Box::new(int_lit(3)),
        body: Box::new(TrustVcExpr::Let {
            name: "y".to_string(),
            ty: i32_ty(),
            value: Box::new(int_lit(2)),
            body: Box::new(TrustVcExpr::Let {
                name: "x".to_string(),
                ty: i32_ty(),
                value: Box::new(int_lit(1)),
                body: Box::new(body),
            }),
        }),
    };

    let result = replace_vars_with_pre_typed(&expr, &vars);

    fn assert_body_vars_not_renamed(expr: &TrustVcExpr, depth: usize) {
        match expr {
            TrustVcExpr::Let { body, .. } => {
                assert_body_vars_not_renamed(body, depth + 1);
            }
            TrustVcExpr::Compare { left, .. } => {
                fn collect_var_names(expr: &TrustVcExpr, names: &mut Vec<String>) {
                    match expr {
                        TrustVcExpr::Var { name, .. } => names.push(name.clone()),
                        TrustVcExpr::Arith { left, right, .. } => {
                            collect_var_names(left, names);
                            collect_var_names(right, names);
                        }
                        _ => {}
                    }
                }
                let mut names = Vec::new();
                collect_var_names(left, &mut names);
                for name in &names {
                    assert!(
                        !name.contains("__trust_vc_pre"),
                        "Variable '{}' in innermost body should NOT be renamed \
                         (shadowed by let at depth {})",
                        name,
                        depth
                    );
                }
            }
            _ => panic!("unexpected structure at depth {}", depth),
        }
    }

    assert_body_vars_not_renamed(&result, 0);
}

#[test]
fn test_typed_rename_quantifier_inside_let_partial_shadow() {
    let vars = make_vars(&["x", "y"]);
    let expr = TrustVcExpr::Let {
        name: "x".to_string(),
        ty: i32_ty(),
        value: Box::new(int_lit(1)),
        body: Box::new(TrustVcExpr::Quantifier {
            kind: QuantifierKind::Forall,
            bound_vars: vec![("y".to_string(), i32_ty())],
            body: Box::new(TrustVcExpr::Compare {
                op: CompareOp::Gt,
                left: Box::new(TrustVcExpr::Arith {
                    op: ArithOp::Add,
                    left: Box::new(var("x")),
                    right: Box::new(var("y")),
                    ty: i32_ty(),
                }),
                right: Box::new(int_lit(0)),
            }),
            triggers: None,
            trigger_inference_mode: None,
        }),
    };

    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::Let { body, .. } = &result {
        if let TrustVcExpr::Quantifier { body: qbody, .. } = body.as_ref() {
            if let TrustVcExpr::Compare { left, .. } = qbody.as_ref() {
                if let TrustVcExpr::Arith {
                    left: l, right: r, ..
                } = left.as_ref()
                {
                    assert_eq!(**l, var("x"), "x should NOT be renamed (shadowed by let)");
                    assert_eq!(
                        **r,
                        var("y"),
                        "y should NOT be renamed (shadowed by forall)"
                    );
                } else {
                    panic!("expected Arith");
                }
            } else {
                panic!("expected Compare");
            }
        } else {
            panic!("expected Quantifier");
        }
    } else {
        panic!("expected Let");
    }
}
