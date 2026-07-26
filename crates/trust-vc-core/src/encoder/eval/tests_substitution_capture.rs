// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::super::substitution::substitute_vars_in_expr;
use super::support::{i32_lit, i32_var};
use crate::ir::{TrustVcExpr, TrustVcType};

#[test]
fn test_substitute_vars_let_capture_avoidance() {
    use crate::ir::ArithOp;

    let expr = TrustVcExpr::Let {
        name: "x".to_string(),
        ty: TrustVcType::Int { width: 32 },
        value: Box::new(TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(i32_var("x")),
            right: Box::new(i32_lit(1)),
            ty: TrustVcType::Int { width: 32 },
        }),
        body: Box::new(TrustVcExpr::Arith {
            op: ArithOp::Mul,
            left: Box::new(i32_var("x")),
            right: Box::new(i32_lit(2)),
            ty: TrustVcType::Int { width: 32 },
        }),
    };

    let mut subst = std::collections::HashMap::new();
    let five = i32_lit(5);
    subst.insert("x", &five);

    let result = substitute_vars_in_expr(&expr, &subst);

    match &result {
        TrustVcExpr::Let { value, body, .. } => {
            match value.as_ref() {
                TrustVcExpr::Arith { left, .. } => match left.as_ref() {
                    TrustVcExpr::IntLit { value: 5, .. } => {}
                    other => panic!("value.left should be IntLit(5), got {:?}", other),
                },
                other => panic!("value should be Arith, got {:?}", other),
            }
            match body.as_ref() {
                TrustVcExpr::Arith { left, .. } => match left.as_ref() {
                    TrustVcExpr::Var { name, .. } => {
                        assert_eq!(name, "x", "body.left should be Var(x), not substituted");
                    }
                    TrustVcExpr::IntLit { .. } => {
                        panic!("BUG: body.left was substituted through Let shadow");
                    }
                    other => panic!("body.left unexpected: {:?}", other),
                },
                other => panic!("body should be Arith, got {:?}", other),
            }
        }
        other => panic!("result should be Let, got {:?}", other),
    }
}

#[test]
fn test_substitute_vars_quantifier_capture_avoidance() {
    use crate::ir::CompareOp;
    use crate::ir_expr::QuantifierKind;

    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".to_string(), TrustVcType::Int { width: 32 })],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(i32_var("x")),
            right: Box::new(i32_lit(0)),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };

    let mut subst = std::collections::HashMap::new();
    let five = i32_lit(5);
    subst.insert("x", &five);

    let result = substitute_vars_in_expr(&expr, &subst);

    match &result {
        TrustVcExpr::Quantifier { body, .. } => match body.as_ref() {
            TrustVcExpr::Compare { left, .. } => match left.as_ref() {
                TrustVcExpr::Var { name, .. } => {
                    assert_eq!(name, "x", "quantifier body.left should stay Var(x)");
                }
                TrustVcExpr::IntLit { .. } => {
                    panic!("BUG: quantifier body.left was substituted through bound var");
                }
                other => panic!("unexpected: {:?}", other),
            },
            other => panic!("body should be Compare, got {:?}", other),
        },
        other => panic!("result should be Quantifier, got {:?}", other),
    }
}

#[test]
fn test_substitute_vars_choose_capture_avoidance() {
    use crate::ir::CompareOp;

    let expr = TrustVcExpr::Choose {
        var_name: "x".to_string(),
        var_ty: TrustVcType::Int { width: 32 },
        condition: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(i32_var("x")),
            right: Box::new(i32_lit(0)),
        }),
        key: "choose_x".to_string(),
        also_assert: None,
    };

    let mut subst = std::collections::HashMap::new();
    let five = i32_lit(5);
    subst.insert("x", &five);

    let result = substitute_vars_in_expr(&expr, &subst);

    match &result {
        TrustVcExpr::Choose { condition, .. } => match condition.as_ref() {
            TrustVcExpr::Compare { left, .. } => match left.as_ref() {
                TrustVcExpr::Var { name, .. } => {
                    assert_eq!(name, "x", "choose condition.left should stay Var(x)");
                }
                TrustVcExpr::IntLit { .. } => {
                    panic!("BUG: choose condition.left was substituted through bound var");
                }
                other => panic!("unexpected: {:?}", other),
            },
            other => panic!("condition should be Compare, got {:?}", other),
        },
        other => panic!("result should be Choose, got {:?}", other),
    }
}

#[test]
fn test_substitute_vars_let_non_shadow_still_substituted() {
    use crate::ir::ArithOp;

    let expr = TrustVcExpr::Let {
        name: "y".to_string(),
        ty: TrustVcType::Int { width: 32 },
        value: Box::new(i32_var("x")),
        body: Box::new(TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(i32_var("y")),
            right: Box::new(i32_var("x")),
            ty: TrustVcType::Int { width: 32 },
        }),
    };

    let mut subst = std::collections::HashMap::new();
    let five = i32_lit(5);
    subst.insert("x", &five);

    let result = substitute_vars_in_expr(&expr, &subst);

    match &result {
        TrustVcExpr::Let { value, body, .. } => {
            match value.as_ref() {
                TrustVcExpr::IntLit { value: 5, .. } => {}
                other => panic!("value should be IntLit(5), got {:?}", other),
            }
            match body.as_ref() {
                TrustVcExpr::Arith { left, right, .. } => {
                    match left.as_ref() {
                        TrustVcExpr::Var { name, .. } => assert_eq!(name, "y"),
                        other => panic!("body.left should be Var(y), got {:?}", other),
                    }
                    match right.as_ref() {
                        TrustVcExpr::IntLit { value: 5, .. } => {}
                        other => panic!("body.right should be IntLit(5), got {:?}", other),
                    }
                }
                other => panic!("body should be Arith, got {:?}", other),
            }
        }
        other => panic!("result should be Let, got {:?}", other),
    }
}

#[test]
fn test_substitute_vars_match_pattern_capture_avoidance() {
    use crate::ir::ArithOp;
    use crate::ir_expr::MatchPattern;

    let expr = TrustVcExpr::Match {
        scrutinee: Box::new(i32_var("s")),
        arms: vec![crate::ir::MatchArm {
            pattern: MatchPattern::Constructor {
                variant_name: "Some".to_string(),
                bindings: vec!["x".to_string()],
                has_rest: false,
            },
            body: TrustVcExpr::Arith {
                op: ArithOp::Add,
                left: Box::new(i32_var("x")),
                right: Box::new(i32_var("y")),
                ty: TrustVcType::Int { width: 32 },
            },
            guard: None,
        }],
        ty: TrustVcType::Int { width: 32 },
    };

    let mut subst = std::collections::HashMap::new();
    let five = i32_lit(5);
    let ten = i32_lit(10);
    subst.insert("x", &five);
    subst.insert("y", &ten);

    let result = substitute_vars_in_expr(&expr, &subst);

    match &result {
        TrustVcExpr::Match { arms, .. } => {
            let body = &arms[0].body;
            match body {
                TrustVcExpr::Arith { left, right, .. } => {
                    match left.as_ref() {
                        TrustVcExpr::Var { name, .. } => {
                            assert_eq!(name, "x", "match arm x should stay Var(x)");
                        }
                        TrustVcExpr::IntLit { .. } => {
                            panic!("BUG: match pattern-bound x was substituted");
                        }
                        other => panic!("unexpected left: {:?}", other),
                    }
                    match right.as_ref() {
                        TrustVcExpr::IntLit { value: 10, .. } => {}
                        other => panic!("y should be substituted to 10, got {:?}", other),
                    }
                }
                other => panic!("arm body should be Arith, got {:?}", other),
            }
        }
        other => panic!("result should be Match, got {:?}", other),
    }
}

#[test]
fn test_substitute_vars_in_expr_recurses_into_spec_closure_body() {
    let closure = TrustVcExpr::SpecClosure {
        params: vec![("item".to_string(), TrustVcType::Int { width: 32 })],
        body: Box::new(TrustVcExpr::Compare {
            op: crate::ir::CompareOp::Gt,
            left: Box::new(TrustVcExpr::Var {
                name: "item".to_string(),
                ty: TrustVcType::Int { width: 32 },
            }),
            right: Box::new(TrustVcExpr::Var {
                name: "x".to_string(),
                ty: TrustVcType::Int { width: 32 },
            }),
        }),
        ty: TrustVcType::Bool,
    };

    let replacement = TrustVcExpr::IntLit {
        value: 5,
        ty: TrustVcType::Int { width: 32 },
    };
    let subst = std::collections::HashMap::from([("x", &replacement)]);

    let result = substitute_vars_in_expr(&closure, &subst);

    match &result {
        TrustVcExpr::SpecClosure { params, body, .. } => {
            assert_eq!(params.len(), 1);
            assert_eq!(params[0].0, "item");

            match body.as_ref() {
                TrustVcExpr::Compare { left, right, .. } => {
                    match left.as_ref() {
                        TrustVcExpr::Var { name, .. } => assert_eq!(name, "item"),
                        other => {
                            panic!("closure param 'item' should remain as Var, got {:?}", other)
                        }
                    }
                    match right.as_ref() {
                        TrustVcExpr::IntLit { value: 5, .. } => {}
                        other => panic!("captured 'x' should be substituted to 5, got {:?}", other),
                    }
                }
                other => panic!("closure body should be Compare, got {:?}", other),
            }
        }
        other => panic!("result should be SpecClosure, got {:?}", other),
    }
}

#[test]
fn test_substitute_vars_closure_param_shadows_outer_substitution() {
    let closure = TrustVcExpr::SpecClosure {
        params: vec![("x".to_string(), TrustVcType::Int { width: 32 })],
        body: Box::new(TrustVcExpr::Compare {
            op: crate::ir::CompareOp::Gt,
            left: Box::new(TrustVcExpr::Var {
                name: "x".to_string(),
                ty: TrustVcType::Int { width: 32 },
            }),
            right: Box::new(TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::Int { width: 32 },
            }),
        }),
        ty: TrustVcType::Bool,
    };

    let replacement = TrustVcExpr::IntLit {
        value: 99,
        ty: TrustVcType::Int { width: 32 },
    };
    let subst = std::collections::HashMap::from([("x", &replacement)]);

    let result = substitute_vars_in_expr(&closure, &subst);

    match &result {
        TrustVcExpr::SpecClosure { body, .. } => match body.as_ref() {
            TrustVcExpr::Compare { left, .. } => match left.as_ref() {
                TrustVcExpr::Var { name, .. } => assert_eq!(name, "x"),
                other => panic!(
                    "closure param 'x' should shadow outer subst, got {:?}",
                    other
                ),
            },
            other => panic!("body should be Compare, got {:?}", other),
        },
        other => panic!("result should be SpecClosure, got {:?}", other),
    }
}
