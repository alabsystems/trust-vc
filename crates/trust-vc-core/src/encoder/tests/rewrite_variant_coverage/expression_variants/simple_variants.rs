// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Neg: rename_vars recurses into negation operand.
#[test]
fn test_typed_rename_neg() {
    let expr = TrustVcExpr::Neg(Box::new(var("x")));
    let vars = make_vars(&["x"]);
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::Neg(inner) = &result {
        assert_eq!(
            **inner,
            TrustVcExpr::Var {
                name: "x__trust_vc_pre".to_string(),
                ty: i32_ty(),
            }
        );
    } else {
        panic!("expected Neg");
    }
}

/// Implies: rename_vars recurses into both premise and conclusion.
#[test]
fn test_typed_rename_implies() {
    let expr = TrustVcExpr::Implies {
        premise: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(var("x")),
            right: Box::new(int_lit(0)),
        }),
        conclusion: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(var("y")),
            right: Box::new(int_lit(0)),
        }),
    };
    let vars = make_vars(&["x", "y"]);
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::Implies {
        premise,
        conclusion,
    } = &result
    {
        if let TrustVcExpr::Compare { left, .. } = premise.as_ref() {
            assert_eq!(
                **left,
                TrustVcExpr::Var {
                    name: "x__trust_vc_pre".to_string(),
                    ty: i32_ty(),
                }
            );
        } else {
            panic!("expected Compare in premise");
        }
        if let TrustVcExpr::Compare { left, .. } = conclusion.as_ref() {
            assert_eq!(
                **left,
                TrustVcExpr::Var {
                    name: "y__trust_vc_pre".to_string(),
                    ty: i32_ty(),
                }
            );
        } else {
            panic!("expected Compare in conclusion");
        }
    } else {
        panic!("expected Implies");
    }
}

/// Ite: rename_vars recurses into condition, then-branch, and else-branch.
#[test]
fn test_typed_rename_ite() {
    let expr = TrustVcExpr::Ite {
        cond: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(var("x")),
            right: Box::new(int_lit(0)),
        }),
        then_branch: Box::new(var("y")),
        else_branch: Box::new(var("z")),
        ty: i32_ty(),
    };
    let vars = make_vars(&["x", "y", "z"]);
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::Ite {
        cond,
        then_branch,
        else_branch,
        ..
    } = &result
    {
        if let TrustVcExpr::Compare { left, .. } = cond.as_ref() {
            assert_eq!(
                **left,
                TrustVcExpr::Var {
                    name: "x__trust_vc_pre".to_string(),
                    ty: i32_ty(),
                }
            );
        } else {
            panic!("expected Compare in cond");
        }
        assert_eq!(
            **then_branch,
            TrustVcExpr::Var {
                name: "y__trust_vc_pre".to_string(),
                ty: i32_ty(),
            }
        );
        assert_eq!(
            **else_branch,
            TrustVcExpr::Var {
                name: "z__trust_vc_pre".to_string(),
                ty: i32_ty(),
            }
        );
    } else {
        panic!("expected Ite");
    }
}

/// Cast: rename_vars recurses into the inner expression.
#[test]
fn test_typed_rename_cast() {
    let expr = TrustVcExpr::Cast {
        expr: Box::new(var("x")),
        from_ty: i32_ty(),
        to_ty: TrustVcType::Uint { width: 64 },
    };
    let vars = make_vars(&["x"]);
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::Cast { expr: inner, .. } = &result {
        assert_eq!(
            **inner,
            TrustVcExpr::Var {
                name: "x__trust_vc_pre".to_string(),
                ty: i32_ty(),
            }
        );
    } else {
        panic!("expected Cast");
    }
}

/// FnCall: rename_vars recurses into arguments but NOT the function name.
#[test]
fn test_typed_rename_fn_call() {
    let expr = TrustVcExpr::FnCall {
        name: "f".to_string(),
        args: vec![var("x"), var("y")],
        return_ty: i32_ty(),
    };
    let vars = make_vars(&["x", "y", "f"]);
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::FnCall { name, args, .. } = &result {
        assert_eq!(name, "f", "function name must NOT be renamed");
        assert_eq!(
            args[0],
            TrustVcExpr::Var {
                name: "x__trust_vc_pre".to_string(),
                ty: i32_ty(),
            }
        );
        assert_eq!(
            args[1],
            TrustVcExpr::Var {
                name: "y__trust_vc_pre".to_string(),
                ty: i32_ty(),
            }
        );
    } else {
        panic!("expected FnCall");
    }
}

/// SpecialArith: rename_vars recurses into operands.
#[test]
fn test_typed_rename_special_arith() {
    let expr = TrustVcExpr::SpecialArith {
        op: SpecialArithOp::BitAnd,
        left: Box::new(var("x")),
        right: Box::new(var("y")),
        ty: i32_ty(),
    };
    let vars = make_vars(&["x", "y"]);
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::SpecialArith { left, right, .. } = &result {
        assert_eq!(
            **left,
            TrustVcExpr::Var {
                name: "x__trust_vc_pre".to_string(),
                ty: i32_ty(),
            }
        );
        assert_eq!(
            **right,
            TrustVcExpr::Var {
                name: "y__trust_vc_pre".to_string(),
                ty: i32_ty(),
            }
        );
    } else {
        panic!("expected SpecialArith");
    }
}

/// WrappingArith: rename_vars recurses into operands.
#[test]
fn test_typed_rename_wrapping_arith() {
    let expr = TrustVcExpr::WrappingArith {
        mode: WrappingMode::Wrapping,
        op: ArithOp::Add,
        left: Box::new(var("x")),
        right: Box::new(var("y")),
        ty: i32_ty(),
    };
    let vars = make_vars(&["x", "y"]);
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::WrappingArith { left, right, .. } = &result {
        assert_eq!(
            **left,
            TrustVcExpr::Var {
                name: "x__trust_vc_pre".to_string(),
                ty: i32_ty(),
            }
        );
        assert_eq!(
            **right,
            TrustVcExpr::Var {
                name: "y__trust_vc_pre".to_string(),
                ty: i32_ty(),
            }
        );
    } else {
        panic!("expected WrappingArith");
    }
}
