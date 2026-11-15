//! A binding COPIED into another by an unascribed `let` (`let z = w;`,
//! `let z = w - 1;`, `let z = w.max(1);`): the copy has the binding's type,
//! so the copy's own uses type the binding ([`super::infer_untyped_binding_type`]).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::{pattern_binds, Constraint, PatternRebound, Reading, Rebound, UseTypes, Uses};
use syn::visit::Visit;
use syn::Stmt;

/// What the uses of `name` in `rest` say about its type: the type they fix,
/// `Free` when every use is read and none fixes one, else `Unknown`.
pub(super) fn binding_constraint(name: &str, rest: &[Stmt], types: &UseTypes<'_>) -> Constraint {
    binding_constraint_of(name, Reading::Name, rest, types)
}

/// [`binding_constraint`] of the binding read through `name` as `reading`
/// says: `name` itself, `*name` for a reference to it, `name[i]` for an
/// array of it.
pub(super) fn binding_constraint_of(
    name: &str,
    reading: Reading,
    rest: &[Stmt],
    types: &UseTypes<'_>,
) -> Constraint {
    let mut rebound = Rebound {
        names: std::collections::BTreeSet::new(),
    };
    for stmt in rest {
        rebound.visit_stmt(stmt);
    }
    // A `let` that binds the name again shadows it for the rest of its block
    // (`Uses::visit_stmts` stops there); any other pattern binding it (a
    // closure parameter, a `match` arm, an `if let`) may stand anywhere, and
    // a use of the name there is not this binding's.
    let mut pattern_rebound = PatternRebound {
        names: std::collections::BTreeSet::new(),
    };
    for stmt in rest {
        pattern_rebound.visit_stmt(stmt);
    }
    if pattern_rebound.names.contains(name) {
        return Constraint::Unknown;
    }
    let mut uses = Uses {
        name,
        reading,
        rebound: &rebound.names,
        types,
        in_macro: false,
        typed_position: false,
        fixed: Vec::new(),
        macro_fixed: false,
        unknown: false,
    };
    uses.visit_stmts(rest);
    let mut fixed = uses.fixed.into_iter();
    if let Some(first) = fixed.next() {
        return if fixed.all(|ty| ty == first) {
            Constraint::Fixed(first)
        } else {
            Constraint::Unknown
        };
    }
    if !uses.unknown && !uses.macro_fixed {
        Constraint::Free
    } else {
        Constraint::Unknown
    }
}

impl Uses<'_> {
    /// Visit a statement list, reading a copy `let` through the statements
    /// after it.
    pub(super) fn visit_stmts(&mut self, stmts: &[Stmt]) {
        for (index, stmt) in stmts.iter().enumerate() {
            // `let <.. name ..> = init;` shadows the binding from here to the
            // end of the block: its initializer is the last use read here.
            if let Stmt::Local(local) = stmt {
                if pattern_binds(&local.pat, self.name) {
                    if let Some(init) = &local.init {
                        self.visit_expr(&init.expr);
                        if let Some((_, diverge)) = &init.diverge {
                            self.visit_expr(diverge);
                        }
                    }
                    return;
                }
            }
            if !self.visit_copy_let(stmt, &stmts[index + 1..]) {
                self.visit_stmt(stmt);
            }
        }
    }

    /// `let z = <the binding or an operation of its type>;` (a plain name
    /// pattern, no ascription, no `else`): the constraint the uses of `z` in
    /// `after` put on `z` is the binding's. It used to be read as undecided
    /// whatever `z`'s uses were, so the unused `let _m = x.max(1);` in a loop
    /// left `x` without a type. Returns whether `stmt` was such a `let`.
    fn visit_copy_let(&mut self, stmt: &Stmt, after: &[Stmt]) -> bool {
        let Stmt::Local(local) = stmt else {
            return false;
        };
        let syn::Pat::Ident(ident) = &local.pat else {
            return false;
        };
        let Some(init) = &local.init else {
            return false;
        };
        if ident.by_ref.is_some()
            || ident.subpat.is_some()
            || init.diverge.is_some()
            || self.in_macro
            || ident.ident == self.name
        {
            return false;
        }
        // `let r = &w;` / `&mut w`: `*r` is the binding, so the uses of `r`
        // read through it type it (`g8(*r + 100)`, `*r + 100 == 300`); a
        // reference to an array read by its elements is read by them too.
        if let syn::Expr::Reference(reference) = super::peel(&init.expr) {
            let through = match self.reading {
                Reading::Name if self.is_name(&reference.expr) => Some(Reading::Deref),
                Reading::Element if self.is_bare_holder(&reference.expr) => Some(Reading::Element),
                _ => None,
            };
            if let Some(through) = through {
                let constraint =
                    binding_constraint_of(&ident.ident.to_string(), through, after, self.types);
                self.record(constraint);
                return true;
            }
        }
        if !self.carries_name(&init.expr) {
            return false;
        }
        let constraint = binding_constraint(&ident.ident.to_string(), after, self.types);
        self.record(constraint);
        if !self.is_name(&init.expr) {
            self.visit_typed(&init.expr);
        }
        true
    }
}
