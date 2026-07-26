//! Free-variable collection for TrustVcExpr trees.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Extracts free variable names from a `TrustVcExpr`, properly tracking
//! all binding constructs (Let, Quantifier, Match patterns, nested Choose).
//! Used by the choose (Skolem) encoder to determine capture variables.
//!
//! Extracted from advanced.rs as part of #2433.
//! Migrated to scope-aware visitor as part of #2641.

use crate::ir::TrustVcExpr;
use crate::ir_expr_traversal::free_root_names_with_initial_bound;

/// Collect free variable names in a TrustVcExpr, excluding `bound_name`.
///
/// Properly tracks all binding constructs (Let, Quantifier, Match patterns,
/// nested Choose) so that inner-bound variables are not reported as free.
/// The previous post-hoc removal approach (`names.retain(); seen.remove()`)
/// was unsound: if a let/quantifier/match-bound name shadowed a free
/// variable used in a sibling expression, the removal deleted the legitimate
/// free reference. This scope-tracking approach extends the bound set BEFORE
/// recursing into the body, which is the standard correct algorithm.
pub(super) fn collect_free_vars(expr: &TrustVcExpr, bound_name: &str) -> Vec<String> {
    let initial_bound = [bound_name].into_iter().collect();
    free_root_names_with_initial_bound(expr, &initial_bound)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::TrustVcType;
    use crate::ir_expr::{ArithOp, CompareOp, LogicOp, MatchArm, MatchPattern, QuantifierKind};

    fn var(name: &str) -> TrustVcExpr {
        TrustVcExpr::Var {
            name: name.to_string(),
            ty: TrustVcType::Int { width: 32 },
        }
    }

    fn int_lit(v: i128) -> TrustVcExpr {
        TrustVcExpr::IntLit {
            value: v,
            ty: TrustVcType::Int { width: 32 },
        }
    }

    fn gt(l: TrustVcExpr, r: TrustVcExpr) -> TrustVcExpr {
        TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(l),
            right: Box::new(r),
        }
    }

    fn add(l: TrustVcExpr, r: TrustVcExpr) -> TrustVcExpr {
        TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(l),
            right: Box::new(r),
            ty: TrustVcType::Int { width: 32 },
        }
    }

    /// Basic: free vars from a simple comparison.
    #[test]
    fn test_collect_free_vars_basic() {
        // choose(|x| x > y) -> free = [y]
        let expr = gt(var("x"), var("y"));
        let free = collect_free_vars(&expr, "x");
        assert_eq!(free, vec!["y".to_string()]);
    }

    /// Let-expression: value references outer scope correctly.
    #[test]
    fn test_collect_free_vars_let_value_is_outer_scope() {
        // choose(|x| let z = y + 1 in z > x)
        // free = [y] (z is bound by let, y is free in value)
        let expr = TrustVcExpr::Let {
            name: "z".to_string(),
            ty: TrustVcType::Int { width: 32 },
            value: Box::new(add(var("y"), int_lit(1))),
            body: Box::new(gt(var("z"), var("x"))),
        };
        let free = collect_free_vars(&expr, "x");
        assert_eq!(free, vec!["y".to_string()], "z is let-bound, y is free");
    }

    /// REGRESSION: Let shadowing must not remove free var from value.
    ///
    /// choose(|x| let y = f(y) in g(y))
    /// The `y` in `f(y)` is the OUTER y (free), the `y` in `g(y)` is let-bound.
    /// The old post-hoc removal approach deleted "y" from the free set entirely,
    /// losing the legitimate free reference from the value expression.
    #[test]
    fn test_collect_free_vars_let_shadow_preserves_value_free_var() {
        // choose(|x| let y = y + 1 in y > x)
        // value `y + 1` references outer y -> y is free
        // body `y > x` references let-bound y -> y is NOT free from body
        // Result: free = [y]
        let expr = TrustVcExpr::Let {
            name: "y".to_string(),
            ty: TrustVcType::Int { width: 32 },
            value: Box::new(add(var("y"), int_lit(1))),
            body: Box::new(gt(var("y"), var("x"))),
        };
        let free = collect_free_vars(&expr, "x");
        assert_eq!(
            free,
            vec!["y".to_string()],
            "y in value expression is free (outer scope), even though y is let-bound in body"
        );
    }

    /// REGRESSION: Inner quantifier bound vars must not leak as free.
    ///
    /// choose(|x| forall(|z: i32| z > x && z > y))
    /// z is bound by the inner forall, y is free.
    /// The old approach collected z as free then removed it post-hoc,
    /// which fails when z also appears free in a sibling expression.
    #[test]
    fn test_collect_free_vars_inner_quantifier_excludes_bound() {
        // choose(|x| forall(|z| z > x && z > y))
        // free = [y] (z is bound by inner forall)
        let body = TrustVcExpr::Logic {
            op: LogicOp::And,
            left: Box::new(gt(var("z"), var("x"))),
            right: Box::new(gt(var("z"), var("y"))),
        };
        let expr = TrustVcExpr::Quantifier {
            kind: QuantifierKind::Forall,
            bound_vars: vec![("z".to_string(), TrustVcType::Int { width: 32 })],
            body: Box::new(body),
            triggers: None,
            trigger_inference_mode: None,
        };
        let free = collect_free_vars(&expr, "x");
        assert_eq!(
            free,
            vec!["y".to_string()],
            "z is bound by inner forall, only y should be free"
        );
    }

    /// REGRESSION: Inner quantifier bound var that shares name with sibling free var.
    ///
    /// choose(|x| z > 0 && forall(|z: i32| z > x))
    /// First z is free, second z is bound by forall. Both must be handled correctly.
    #[test]
    fn test_collect_free_vars_quantifier_shadow_with_sibling_free() {
        // choose(|x| z > 0 && forall(|z| z > x))
        // The first z is free, the forall-bound z is not.
        // free = [z]
        let forall_expr = TrustVcExpr::Quantifier {
            kind: QuantifierKind::Forall,
            bound_vars: vec![("z".to_string(), TrustVcType::Int { width: 32 })],
            body: Box::new(gt(var("z"), var("x"))),
            triggers: None,
            trigger_inference_mode: None,
        };
        let expr = TrustVcExpr::Logic {
            op: LogicOp::And,
            left: Box::new(gt(var("z"), int_lit(0))),
            right: Box::new(forall_expr),
        };
        let free = collect_free_vars(&expr, "x");
        assert_eq!(
            free,
            vec!["z".to_string()],
            "z is free in left conjunct even though it's bound in the inner forall"
        );
    }

    /// REGRESSION: Match arm pattern bindings must not leak as free.
    ///
    /// choose(|x| match x { v => v > y })
    /// v is bound by the Ident pattern, y is free.
    #[test]
    fn test_collect_free_vars_match_pattern_excludes_bound() {
        // choose(|x| match x { v => v > y })
        // free = [y] (v is bound by the pattern)
        let expr = TrustVcExpr::Match {
            scrutinee: Box::new(var("x")),
            arms: vec![MatchArm {
                pattern: MatchPattern::Ident("v".to_string()),
                body: gt(var("v"), var("y")),
                guard: None,
            }],
            ty: TrustVcType::Bool,
        };
        let free = collect_free_vars(&expr, "x");
        assert_eq!(
            free,
            vec!["y".to_string()],
            "v is bound by match pattern, only y should be free"
        );
    }

    /// REGRESSION: Match Constructor pattern bindings excluded correctly.
    #[test]
    fn test_collect_free_vars_match_constructor_pattern() {
        // choose(|x| match x { Some(v) => v > y, _ => false })
        // free = [y]
        let expr = TrustVcExpr::Match {
            scrutinee: Box::new(var("x")),
            arms: vec![
                MatchArm {
                    pattern: MatchPattern::Constructor {
                        variant_name: "Some".to_string(),
                        bindings: vec!["v".to_string()],
                        has_rest: false,
                    },
                    body: gt(var("v"), var("y")),
                    guard: None,
                },
                MatchArm {
                    pattern: MatchPattern::Wildcard,
                    body: TrustVcExpr::BoolLit(false),
                    guard: None,
                },
            ],
            ty: TrustVcType::Bool,
        };
        let free = collect_free_vars(&expr, "x");
        assert_eq!(
            free,
            vec!["y".to_string()],
            "v is bound by Constructor pattern, only y should be free"
        );
    }

    /// REGRESSION: Nested choose bound variable must not leak.
    ///
    /// choose(|x| choose(|z| z > x && z > y) > 0)
    /// z is bound by inner choose, y is free.
    #[test]
    fn test_collect_free_vars_nested_choose_excludes_inner_bound() {
        // choose(|x| choose(|z| z > y) > 0)
        // free = [y] (z is bound by inner choose)
        let inner = TrustVcExpr::Choose {
            var_name: "z".to_string(),
            var_ty: TrustVcType::Int { width: 32 },
            condition: Box::new(gt(var("z"), var("y"))),
            key: "inner".to_string(),
            also_assert: None,
        };
        let expr = gt(inner, int_lit(0));
        let free = collect_free_vars(&expr, "x");
        assert_eq!(
            free,
            vec!["y".to_string()],
            "z is bound by inner choose, only y should be free"
        );
    }

    /// Let shadow with sibling: the post-hoc removal bug in action.
    ///
    /// choose(|x| (let y = 1 in y + x) + y)
    /// First y is let-bound (value is 1, body uses y). Second y is free (outer).
    /// The old code would remove "y" from free set after processing the Let,
    /// then the outer y would be blocked by `seen` still containing "y".
    #[test]
    fn test_collect_free_vars_let_shadow_with_outer_sibling() {
        // choose(|x| (let y = 1 in y + x) + y)
        // free = [y] — the outer y is free
        let let_expr = TrustVcExpr::Let {
            name: "y".to_string(),
            ty: TrustVcType::Int { width: 32 },
            value: Box::new(int_lit(1)),
            body: Box::new(add(var("y"), var("x"))),
        };
        let expr = add(let_expr, var("y"));
        let free = collect_free_vars(&expr, "x");
        assert_eq!(
            free,
            vec!["y".to_string()],
            "y outside the let is free, even though y is bound inside the let"
        );
    }

    /// ReadPlace root_name is collected as a free variable.
    #[test]
    fn test_collect_free_vars_read_place_root_name() {
        use crate::ir_place::TrustVcPlace;
        // choose(|x| read(c.count)) — c is free
        let place = TrustVcPlace::root("c", TrustVcType::Int { width: 32 })
            .field("count", TrustVcType::Int { width: 32 });
        let expr = TrustVcExpr::ReadPlace {
            place,
            ty: TrustVcType::Int { width: 32 },
        };
        let free = collect_free_vars(&expr, "x");
        assert_eq!(
            free,
            vec!["c".to_string()],
            "ReadPlace root_name 'c' should be free"
        );
    }

    /// ReadPlace root_name is excluded when bound.
    #[test]
    fn test_collect_free_vars_read_place_root_bound() {
        use crate::ir_place::TrustVcPlace;
        // choose(|c| read(c.count)) — c is bound, not free
        let place = TrustVcPlace::root("c", TrustVcType::Int { width: 32 })
            .field("count", TrustVcType::Int { width: 32 });
        let expr = TrustVcExpr::ReadPlace {
            place,
            ty: TrustVcType::Int { width: 32 },
        };
        let free = collect_free_vars(&expr, "c");
        assert!(
            free.is_empty(),
            "ReadPlace root_name 'c' is bound, should not be free"
        );
    }

    /// PlaceDisjoint root_names are collected as free variables.
    #[test]
    fn test_collect_free_vars_place_disjoint_root_names() {
        use crate::ir_place::TrustVcPlace;
        // choose(|x| disjoint(a, b)) — a and b are free
        let left = TrustVcPlace::root("a", TrustVcType::Int { width: 32 });
        let right = TrustVcPlace::root("b", TrustVcType::Int { width: 32 });
        let expr = TrustVcExpr::PlaceDisjoint { left, right };
        let free = collect_free_vars(&expr, "x");
        assert_eq!(free, vec!["a".to_string(), "b".to_string()]);
    }

    /// ReadPlace with index sub-expression collects both root and index var.
    #[test]
    fn test_collect_free_vars_read_place_root_and_index() {
        use crate::ir_place::TrustVcPlace;
        // choose(|x| read(s[i])) — both s and i are free
        let place = TrustVcPlace::root(
            "s",
            TrustVcType::Seq(Box::new(TrustVcType::Int { width: 32 })),
        )
        .index(var("i"), TrustVcType::Int { width: 32 });
        let expr = TrustVcExpr::ReadPlace {
            place,
            ty: TrustVcType::Int { width: 32 },
        };
        let free = collect_free_vars(&expr, "x");
        assert_eq!(free, vec!["s".to_string(), "i".to_string()]);
    }
}
