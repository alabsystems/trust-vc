// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Scope-aware variable reference queries for trigger inference.
//!
//! Both functions delegate to the shared scope-aware traversal infrastructure
//! in `ir_expr_traversal`. Part of #2641.

use std::collections::HashSet;

use crate::ir_expr::TrustVcExpr;
use crate::ir_expr_traversal::{
    expr_references_any_name, walk_expr_scoped, ScopeAwareTrustVcExprVisitor,
};

/// Check if an expression references any of the given bound variable names.
pub(super) fn expr_references_any_bound(expr: &TrustVcExpr, bound_names: &HashSet<&str>) -> bool {
    expr_references_any_name(expr, bound_names)
}

/// Collect the set of bound variable names referenced by an expression.
///
/// Stops at nested `Quantifier` nodes (trigger expressions should not
/// recurse into inner quantifier bodies for the purpose of determining
/// which outer bound variables are covered).
pub(super) fn referenced_bound_vars<'a>(
    expr: &TrustVcExpr,
    bound_names: &HashSet<&'a str>,
) -> HashSet<&'a str> {
    struct Collector<'a, 'b> {
        names: &'b HashSet<&'a str>,
        found: HashSet<&'a str>,
    }
    impl<'a, 'b> ScopeAwareTrustVcExprVisitor for Collector<'a, 'b> {
        fn visit_expr_scoped(&mut self, expr: &TrustVcExpr, bound: &HashSet<&str>) -> bool {
            match expr {
                TrustVcExpr::Var { name, .. } => {
                    if let Some(&bname) = self.names.get(name.as_str()) {
                        if !bound.contains(name.as_str()) {
                            self.found.insert(bname);
                        }
                    }
                    true
                }
                // Don't recurse into nested quantifiers — trigger coverage
                // analysis only considers the outermost quantifier's bound vars.
                TrustVcExpr::Quantifier { .. } => false,
                _ => true,
            }
        }
    }
    let mut collector = Collector {
        names: bound_names,
        found: HashSet::new(),
    };
    walk_expr_scoped(&mut collector, expr, &HashSet::new());
    collector.found
}
