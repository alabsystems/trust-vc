//! Where a later pattern takes the name of an unsuffixed-literal binding
//! ([`super::infer_untyped_binding_type`]): a `let` shadows it for the rest of
//! its block, and any other pattern may stand anywhere.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::{macro_exprs, path_ident, peel, Constraint, Rebound, UseTypes, Uses};
use crate::ir::TrustVcType;
use syn::visit::Visit;
use syn::Stmt;

/// How the binding a reading types is reached through the name it follows.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::vc_extraction) enum Reading {
    /// The name is the binding.
    Name,
    /// The name is a reference to the binding (`let r = &w;`): the binding is
    /// `*r`.
    Deref,
    /// The name holds an array whose elements are typed (`let a = [200,
    /// 1];`): the binding is `a[i]` (or `r[i]` for `let r = &a;`).
    Element,
}

impl Uses<'_> {
    /// A bare mention of a name the binding is read through (`f(r)`, `r.max(1)`,
    /// `g(a)`): not a read of the binding this reading types.
    pub(super) fn is_bare_holder(&self, expr: &syn::Expr) -> bool {
        self.reading != Reading::Name
            && path_ident(peel(expr)).is_some_and(|ident| ident == self.name)
    }

    /// `a.len()` / `a.is_empty()` of an array read through its elements: it
    /// reads no element.
    pub(super) fn is_length_read(&self, call: &syn::ExprMethodCall) -> bool {
        self.reading == Reading::Element
            && call.args.is_empty()
            && matches!(call.method.to_string().as_str(), "len" | "is_empty")
            && path_ident(peel(&call.receiver)).is_some_and(|ident| ident == self.name)
    }
}

/// Every name a pattern other than a `let`'s binds: a closure or function
/// parameter, a `match` arm, an `if let` / `while let`, a `for` pattern.
pub(super) struct PatternRebound {
    pub(super) names: std::collections::BTreeSet<String>,
}

impl<'ast> Visit<'ast> for PatternRebound {
    fn visit_pat_ident(&mut self, ident: &'ast syn::PatIdent) {
        self.names.insert(ident.ident.to_string());
        syn::visit::visit_pat_ident(self, ident);
    }

    fn visit_local(&mut self, local: &'ast syn::Local) {
        if let Some(init) = &local.init {
            self.visit_expr(&init.expr);
            if let Some((_, diverge)) = &init.diverge {
                self.visit_expr(diverge);
            }
        }
    }

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        for expr in macro_exprs(mac).iter().flatten() {
            self.visit_expr(expr);
        }
    }
}

/// Whether `pat` binds `name`.
pub(super) fn pattern_binds(pat: &syn::Pat, name: &str) -> bool {
    let mut bound = Rebound {
        names: std::collections::BTreeSet::new(),
    };
    bound.visit_pat(pat);
    bound.names.contains(name)
}

/// The type Rust infers for the elements of the array the unascribed `let`
/// binding `name` holds (`let a = [200, 1];`, read as `a[i]`) — its uses in
/// `rest` read through its elements ([`Reading::Element`]) — or `None`.
pub(in crate::vc_extraction) fn infer_untyped_element_type(
    name: &str,
    rest: &[Stmt],
    types: &UseTypes<'_>,
) -> Option<TrustVcType> {
    match super::copy::binding_constraint_of(name, Reading::Element, rest, types) {
        Constraint::Fixed(ty) => Some(ty),
        Constraint::Free => Some(TrustVcType::Int { width: 32 }),
        Constraint::Unknown => None,
    }
}
