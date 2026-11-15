// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

/// Substitutes variable references in an expression with replacement expressions.
/// Used by inline body substitution to replace formal params with actual args,
/// and by every axiom-instantiation path (`witness_sort`). Migrated to
/// scope-aware folder as part of #2641.
///
/// A replacement keeps the replaced variable's type
/// (`ir_lowering::pin_substituted_value`): an untyped literal standing for an
/// `i32` binder is pinned, never left to be typed by its new peers.
pub(in crate::encoder) fn substitute_vars_in_expr(
    expr: &crate::ir::TrustVcExpr,
    subst: &std::collections::HashMap<&str, &crate::ir::TrustVcExpr>,
) -> crate::ir::TrustVcExpr {
    use crate::ir::TrustVcExpr;
    use crate::ir_expr_traversal::{fold_expr_scoped_children, ScopeAwareTrustVcExprFolder};
    use std::collections::{HashMap, HashSet};

    struct Substitutor<'a> {
        subst: &'a HashMap<&'a str, &'a TrustVcExpr>,
    }
    impl ScopeAwareTrustVcExprFolder for Substitutor<'_> {
        fn fold_expr_scoped(&mut self, expr: TrustVcExpr, bound: &HashSet<&str>) -> TrustVcExpr {
            if let TrustVcExpr::Var { ref name, ref ty } = expr {
                if !bound.contains(name.as_str()) {
                    if let Some(replacement) = self.subst.get(name.as_str()) {
                        return crate::ir_lowering::pin_substituted_value(ty, replacement);
                    }
                }
                return expr;
            }
            let mut folded = fold_expr_scoped_children(self, expr, bound);
            match &mut folded {
                TrustVcExpr::ReadPlace { place, .. }
                    if !bound.contains(place.root_name.as_str()) =>
                {
                    if let Some(TrustVcExpr::Var { name, .. }) =
                        self.subst.get(place.root_name.as_str())
                    {
                        place.root_name = name.clone();
                    }
                }
                TrustVcExpr::PlaceDisjoint { left, right } => {
                    for place in [left, right] {
                        if !bound.contains(place.root_name.as_str()) {
                            if let Some(TrustVcExpr::Var { name, .. }) =
                                self.subst.get(place.root_name.as_str())
                            {
                                place.root_name = name.clone();
                            }
                        }
                    }
                }
                _ => {}
            }
            folded
        }
    }

    let mut substitutor = Substitutor { subst };
    substitutor.fold_expr_scoped(expr.clone(), &HashSet::new())
}
