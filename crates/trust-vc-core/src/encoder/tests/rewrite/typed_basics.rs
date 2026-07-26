// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_typed_rename_var() {
    let expr = var("x");
    let vars = make_vars(&["x", "y"]);
    let result = replace_vars_with_pre_typed(&expr, &vars);
    assert_eq!(
        result,
        TrustVcExpr::Var {
            name: "x__trust_vc_pre".to_string(),
            ty: i32_ty(),
        }
    );
}

#[test]
fn test_typed_rename_leaves_literals() {
    let expr = int_lit(42);
    let vars = make_vars(&["x"]);
    let result = replace_vars_with_pre_typed(&expr, &vars);
    assert_eq!(result, int_lit(42));
}

#[test]
fn test_typed_rename_in_compare() {
    let expr = TrustVcExpr::Compare {
        op: CompareOp::Gt,
        left: Box::new(var("x")),
        right: Box::new(int_lit(0)),
    };
    let vars = make_vars(&["x"]);
    let result = replace_vars_with_pre_typed(&expr, &vars);
    let expected = TrustVcExpr::Compare {
        op: CompareOp::Gt,
        left: Box::new(TrustVcExpr::Var {
            name: "x__trust_vc_pre".to_string(),
            ty: i32_ty(),
        }),
        right: Box::new(int_lit(0)),
    };
    assert_eq!(result, expected);
}

#[test]
fn test_typed_rename_in_logic() {
    let expr = TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(var("x")),
            right: Box::new(int_lit(0)),
        }),
        right: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(var("y")),
            right: Box::new(int_lit(0)),
        }),
    };
    let vars = make_vars(&["x", "y"]);
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::Logic { left, right, .. } = &result {
        if let TrustVcExpr::Compare { left: l, .. } = left.as_ref() {
            assert_eq!(
                **l,
                TrustVcExpr::Var {
                    name: "x__trust_vc_pre".to_string(),
                    ty: i32_ty(),
                }
            );
        } else {
            panic!("expected Compare");
        }
        if let TrustVcExpr::Compare { left: l, .. } = right.as_ref() {
            assert_eq!(
                **l,
                TrustVcExpr::Var {
                    name: "y__trust_vc_pre".to_string(),
                    ty: i32_ty(),
                }
            );
        } else {
            panic!("expected Compare");
        }
    } else {
        panic!("expected Logic");
    }
}

#[test]
fn test_typed_rename_with_precomputed_targets_matches_wrapper() {
    let expr = TrustVcExpr::Logic {
        op: LogicOp::And,
        left: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(var("x")),
            right: Box::new(int_lit(0)),
        }),
        right: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(var("y")),
            right: Box::new(var("x")),
        }),
    };
    let vars = make_vars(&["x", "y"]);
    let targets = collect_pre_state_target_names(&vars);

    let via_wrapper = replace_vars_with_pre_typed(&expr, &vars);
    let via_precomputed = replace_vars_with_pre_typed_with_targets(&expr, &targets);

    assert_eq!(via_precomputed, via_wrapper);
}

#[test]
fn test_typed_rename_skips_non_target_vars() {
    let expr = var("z");
    let vars = make_vars(&["x", "y"]);
    let result = replace_vars_with_pre_typed(&expr, &vars);
    assert_eq!(result, var("z"));
}

#[test]
fn test_typed_rename_parity_with_string_version() {
    let vars = make_vars(&["x", "y"]);
    let string_result = replace_vars_with_pre("x + y > 0", &vars);
    assert_eq!(string_result, "x__trust_vc_pre + y__trust_vc_pre > 0");

    let expr = TrustVcExpr::Compare {
        op: CompareOp::Gt,
        left: Box::new(TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(var("x")),
            right: Box::new(var("y")),
            ty: i32_ty(),
        }),
        right: Box::new(int_lit(0)),
    };
    let typed_result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::Compare { left, .. } = &typed_result {
        if let TrustVcExpr::Arith {
            left: l, right: r, ..
        } = left.as_ref()
        {
            assert_eq!(
                **l,
                TrustVcExpr::Var {
                    name: "x__trust_vc_pre".to_string(),
                    ty: i32_ty(),
                }
            );
            assert_eq!(
                **r,
                TrustVcExpr::Var {
                    name: "y__trust_vc_pre".to_string(),
                    ty: i32_ty(),
                }
            );
        } else {
            panic!("expected Arith");
        }
    } else {
        panic!("expected Compare");
    }
}
