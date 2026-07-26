//! Traversal traits for `TrustVcExpr`: visitor (shared borrow) and folder
//! (owned tree), with basic and scope-aware variants.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Follows the `syn::visit` / `syn::fold` pattern: trait hooks with default
//! implementations that delegate to free `walk_*` / `fold_*` helpers for child
//! recursion. The exhaustive match in `walk_expr` / `fold_expr_children` ensures
//! new `TrustVcExpr` variants produce a compile error until handled.
//!
//! Part of #2452.

mod folder;
mod scope_folder;
mod scope_visitor;
mod visitor;

use crate::ir_expr::TrustVcExpr;

pub(crate) use folder::{fold_expr_children, fold_expr_vec, TrustVcExprFolder};
pub(crate) use scope_folder::{fold_expr_scoped_children, ScopeAwareTrustVcExprFolder};
pub(crate) use scope_visitor::{
    expr_references_any_name, free_root_names, free_root_names_with_initial_bound,
    walk_expr_scoped, ScopeAwareTrustVcExprVisitor,
};
pub(crate) use visitor::{walk_expr, TrustVcExprVisitor};

/// True if `expr` contains a `FnCall` node (a function / spec-fn / opaque
/// predicate application) anywhere in its tree.
///
/// Used to trigger-gate multi-binder `choose` lowering: a predicate that
/// mentions a spec-fn takes the `no_mbqi` combined-axiom path (fail-closed
/// without a ground witness), while a purely decidable arithmetic predicate
/// keeps the nested-`exists` per-field path. The encoder mirrors this exact
/// predicate to decide whether to `mark_no_mbqi` the attached combined axiom.
pub(crate) fn expr_mentions_fncall(expr: &TrustVcExpr) -> bool {
    struct FnCallSeeker {
        found: bool,
    }
    impl TrustVcExprVisitor for FnCallSeeker {
        fn visit_expr(&mut self, expr: &TrustVcExpr) {
            if self.found {
                return;
            }
            if matches!(expr, TrustVcExpr::FnCall { .. }) {
                self.found = true;
                return;
            }
            walk_expr(self, expr);
        }
    }
    let mut seeker = FnCallSeeker { found: false };
    seeker.visit_expr(expr);
    seeker.found
}

#[cfg(test)]
mod tests;
