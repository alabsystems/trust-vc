// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Match with Constructor pattern: bindings introduced by the Constructor
/// pattern shadow outer variables in the arm body.
///
/// `match scrutinee { Some(x) => x + y }` with targets {x, y}:
/// - scrutinee references x — must be renamed
/// - arm body x is shadowed by Constructor binding — must NOT be renamed
/// - arm body y is not shadowed — must be renamed
///
/// DISCRIMINATING: if collect_pattern_bindings didn't extract Constructor
/// bindings, x in the arm body would be incorrectly renamed.
#[test]
fn test_typed_rename_match_constructor_pattern_shadows_bindings() {
    let expr = TrustVcExpr::Match {
        scrutinee: Box::new(var("x")),
        arms: vec![MatchArm {
            pattern: MatchPattern::Constructor {
                variant_name: "Some".to_string(),
                bindings: vec!["x".to_string()],
                has_rest: false,
            },
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
            "scrutinee x must be renamed"
        );
        if let TrustVcExpr::Arith { left, right, .. } = &arms[0].body {
            assert_eq!(
                **left,
                var("x"),
                "x in arm body must NOT be renamed (shadowed by Constructor binding)"
            );
            assert_eq!(
                **right,
                TrustVcExpr::Var {
                    name: "y__trust_vc_pre".to_string(),
                    ty: i32_ty(),
                },
                "y in arm body must be renamed (not shadowed)"
            );
        } else {
            panic!("expected Arith in arm body");
        }
    } else {
        panic!("expected Match");
    }
}

/// Match with Or pattern containing Ident sub-patterns: all bindings
/// from all Or alternatives shadow in the arm body.
///
/// `match s { A | B(x) => x + y }` with targets {x, y}:
/// - x is bound by `B(x)` inside the Or — shadowed in arm body
/// - y is free — renamed in arm body
///
/// DISCRIMINATING: if collect_pattern_bindings didn't recurse into Or
/// sub-patterns, x from B(x) would not shadow and would be incorrectly renamed.
#[test]
fn test_typed_rename_match_or_pattern_collects_all_bindings() {
    let expr = TrustVcExpr::Match {
        scrutinee: Box::new(var("s")),
        arms: vec![MatchArm {
            pattern: MatchPattern::Or(vec![
                MatchPattern::Ident("a".to_string()),
                MatchPattern::Constructor {
                    variant_name: "B".to_string(),
                    bindings: vec!["x".to_string()],
                    has_rest: false,
                },
            ]),
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
    let vars = make_vars(&["x", "y", "a", "s"]);
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::Match {
        scrutinee, arms, ..
    } = &result
    {
        assert_eq!(
            **scrutinee,
            TrustVcExpr::Var {
                name: "s__trust_vc_pre".to_string(),
                ty: i32_ty(),
            },
            "scrutinee s must be renamed"
        );
        if let TrustVcExpr::Arith { left, right, .. } = &arms[0].body {
            assert_eq!(
                **left,
                var("x"),
                "x must NOT be renamed (shadowed by B(x) inside Or pattern)"
            );
            assert_eq!(
                **right,
                TrustVcExpr::Var {
                    name: "y__trust_vc_pre".to_string(),
                    ty: i32_ty(),
                },
                "y must be renamed (not shadowed)"
            );
        } else {
            panic!("expected Arith in arm body");
        }
    } else {
        panic!("expected Match");
    }
}

/// Match with literal pattern: variable references in the pattern's
/// literal expression are renamed (evaluated in outer scope).
#[test]
fn test_typed_rename_match_literal_pattern() {
    let expr = TrustVcExpr::Match {
        scrutinee: Box::new(var("x")),
        arms: vec![MatchArm {
            pattern: MatchPattern::Lit(var("y")),
            body: var("z"),
            guard: None,
        }],
        ty: i32_ty(),
    };
    let vars = make_vars(&["x", "y", "z"]);
    let result = replace_vars_with_pre_typed(&expr, &vars);
    if let TrustVcExpr::Match { arms, .. } = &result {
        if let MatchPattern::Lit(lit_expr) = &arms[0].pattern {
            assert_eq!(
                *lit_expr,
                TrustVcExpr::Var {
                    name: "y__trust_vc_pre".to_string(),
                    ty: i32_ty(),
                },
                "variable in Lit pattern should be renamed (outer scope)"
            );
        } else {
            panic!("expected Lit pattern");
        }
        assert_eq!(
            arms[0].body,
            TrustVcExpr::Var {
                name: "z__trust_vc_pre".to_string(),
                ty: i32_ty(),
            }
        );
    } else {
        panic!("expected Match");
    }
}
