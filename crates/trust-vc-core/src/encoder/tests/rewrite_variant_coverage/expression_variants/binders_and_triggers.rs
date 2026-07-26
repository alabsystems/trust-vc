// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Match: rename_vars renames in scrutinee and arm bodies, and respects
/// pattern-introduced bindings as shadowing.
#[test]
fn test_typed_rename_match_with_pattern_shadowing() {
    let expr = TrustVcExpr::Match {
        scrutinee: Box::new(var("x")),
        arms: vec![MatchArm {
            pattern: MatchPattern::Ident("y".to_string()),
            body: TrustVcExpr::Arith {
                op: ArithOp::Add,
                left: Box::new(var("x")),
                right: Box::new(var("y")),
                ty: i32_ty(),
            },
            guard: None,
        }],
        ty: i32_ty(),
    };
    let vars = make_vars(&["x", "y"]);
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::Match {
        scrutinee, arms, ..
    } = &result
    {
        assert_eq!(
            **scrutinee,
            TrustVcExpr::Var {
                name: "x__trust_vc_pre".to_string(),
                ty: i32_ty(),
            },
            "match scrutinee must be renamed"
        );
        if let TrustVcExpr::Arith { left, right, .. } = &arms[0].body {
            assert_eq!(
                **left,
                TrustVcExpr::Var {
                    name: "x__trust_vc_pre".to_string(),
                    ty: i32_ty(),
                },
                "x in match arm body should be renamed (not shadowed)"
            );
            assert_eq!(
                **right,
                var("y"),
                "y in match arm body should NOT be renamed (shadowed by Ident pattern)"
            );
        } else {
            panic!("expected Arith in match arm body");
        }
    } else {
        panic!("expected Match");
    }
}

/// Choose: var_name shadows the outer variable inside the condition.
///
/// `choose!(|x: i32| x > y)` with targets {x, y}:
/// - `x` inside the condition is shadowed by var_name and must NOT be renamed
/// - `y` inside the condition is NOT shadowed and must be renamed
///
/// DISCRIMINATING: if Choose didn't shadow, x would be incorrectly renamed.
#[test]
fn test_typed_rename_choose_shadows_var_name() {
    let expr = TrustVcExpr::Choose {
        var_name: "x".to_string(),
        var_ty: i32_ty(),
        condition: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(var("x")),
            right: Box::new(var("y")),
        }),
        key: "sk_x_0".to_string(),
        also_assert: None,
    };
    let vars = make_vars(&["x", "y"]);
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::Choose {
        var_name,
        condition,
        key,
        ..
    } = &result
    {
        assert_eq!(var_name, "x", "Choose var_name must NOT be renamed");
        assert_eq!(key, "sk_x_0", "Choose key must NOT be renamed");
        if let TrustVcExpr::Compare { left, right, .. } = condition.as_ref() {
            assert_eq!(
                **left,
                var("x"),
                "x inside Choose condition must NOT be renamed (shadowed by var_name)"
            );
            assert_eq!(
                **right,
                TrustVcExpr::Var {
                    name: "y__trust_vc_pre".to_string(),
                    ty: i32_ty(),
                },
                "y inside Choose condition must be renamed (not shadowed)"
            );
        } else {
            panic!("expected Compare in Choose condition");
        }
    } else {
        panic!("expected Choose");
    }
}

/// Choose: when var_name is NOT a target, only the free variables in
/// the condition that are targets get renamed.
#[test]
fn test_typed_rename_choose_non_target_var_name() {
    let expr = TrustVcExpr::Choose {
        var_name: "w".to_string(),
        var_ty: i32_ty(),
        condition: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(var("w")),
            right: Box::new(var("x")),
        }),
        key: "sk_w_0".to_string(),
        also_assert: None,
    };
    let vars = make_vars(&["x"]);
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::Choose { condition, .. } = &result {
        if let TrustVcExpr::Compare { left, right, .. } = condition.as_ref() {
            assert_eq!(**left, var("w"), "w is shadowed by var_name, unchanged");
            assert_eq!(
                **right,
                TrustVcExpr::Var {
                    name: "x__trust_vc_pre".to_string(),
                    ty: i32_ty(),
                },
                "x is a target and not shadowed, must be renamed"
            );
        } else {
            panic!("expected Compare in Choose condition");
        }
    } else {
        panic!("expected Choose");
    }
}

/// Quantifier with triggers: rename_vars recurses into trigger expressions
/// and respects quantifier-bound variable shadowing inside triggers.
///
/// `forall |x: i32| { triggers: [[f(x, y)]] } body(x, y)` with targets {x, y}:
/// - `x` in both body and triggers is shadowed by bound_vars
/// - `y` in both body and triggers must be renamed
///
/// DISCRIMINATING: if triggers weren't processed, y inside triggers would
/// remain unrenamed, breaking pre-state substitution correctness.
#[test]
fn test_typed_rename_quantifier_with_triggers() {
    let trigger_expr = TrustVcExpr::FnCall {
        name: "f".to_string(),
        args: vec![var("x"), var("y")],
        return_ty: i32_ty(),
    };
    let expr = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Forall,
        bound_vars: vec![("x".to_string(), i32_ty())],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(var("x")),
            right: Box::new(var("y")),
        }),
        triggers: Some(vec![vec![trigger_expr]]),
        trigger_inference_mode: None,
    };
    let vars = make_vars(&["x", "y"]);
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::Quantifier {
        triggers: Some(trigger_groups),
        trigger_inference_mode: None,
        body,
        ..
    } = &result
    {
        if let TrustVcExpr::Compare { left, right, .. } = body.as_ref() {
            assert_eq!(
                **left,
                var("x"),
                "x in quantifier body must NOT be renamed (bound variable)"
            );
            assert_eq!(
                **right,
                TrustVcExpr::Var {
                    name: "y__trust_vc_pre".to_string(),
                    ty: i32_ty(),
                },
                "y in quantifier body must be renamed"
            );
        } else {
            panic!("expected Compare in body");
        }
        assert_eq!(trigger_groups.len(), 1);
        assert_eq!(trigger_groups[0].len(), 1);
        if let TrustVcExpr::FnCall { args, .. } = &trigger_groups[0][0] {
            assert_eq!(
                args[0],
                var("x"),
                "x in trigger must NOT be renamed (bound)"
            );
            assert_eq!(
                args[1],
                TrustVcExpr::Var {
                    name: "y__trust_vc_pre".to_string(),
                    ty: i32_ty(),
                },
                "y in trigger must be renamed"
            );
        } else {
            panic!("expected FnCall in trigger");
        }
    } else {
        panic!("expected Quantifier with triggers");
    }
}
