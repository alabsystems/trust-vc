//! Rust `#[action]` bodies to TLA+ (see [`super`] for the translated subset).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::{and, self_field, statements, translate, Ty, Vars};
use quote::ToTokens;
use syn::visit::Visit;
use syn::{Expr, Member, Stmt};

/// A translated `#[action]` body.
pub(in crate::protocol) struct Action {
    /// Conjuncts over the current state: the guards (each early return's
    /// condition negated), then `field' = value`.
    pub(in crate::protocol) clauses: Vec<String>,
    /// The fields the body assigns.
    pub(in crate::protocol) assigned: Vec<String>,
    /// When the body can overflow: the condition, over the current state, that
    /// running it does not. Statements after an early return run only when
    /// it does not return.
    pub(in crate::protocol) panic_free: Option<String>,
}

/// Translate an `#[action]` body: early returns `if <bool> { return; }`, then
/// assignments `self.field = value`, each reading the state before the
/// action. A field is assigned at most once and never read after it is.
///
/// An early return is read as the action being disabled in the states where
/// it returns: Rust then changes nothing, which is the model's stutter step.
/// It must come before every assignment, since an assignment before it has
/// already run when Rust returns. Any other statement is refused, a bare
/// `bool` expression in particular: Rust evaluates it, discards it and runs
/// the statements after it, so it is not a guard.
pub(in crate::protocol) fn action(body: &str, vars: &Vars) -> Result<Action, String> {
    let mut action = Action {
        clauses: Vec::new(),
        assigned: Vec::new(),
        panic_free: None,
    };
    let mut steps = Vec::new();
    for stmt in statements(body)? {
        let (read, target) = match &stmt {
            Stmt::Expr(Expr::Assign(assign), _) => {
                (&*assign.right, Some(self_field(&assign.left, vars)?))
            }
            Stmt::Expr(Expr::If(early), _) => (early_return(early)?, None),
            _ => {
                return Err(format!(
                    "`{}`: an action statement is `self.field = value` or an early return \
                     `if <bool> {{ return; }}` (Rust evaluates a bare expression statement \
                     and runs the statements after it: it is not a guard)",
                    stmt.to_token_stream()
                ))
            }
        };
        if let Some(field) = fields_read(read)
            .into_iter()
            .find(|field| action.assigned.contains(field))
        {
            return Err(format!(
                "state variable '{field}' is read after it is assigned in the same action"
            ));
        }
        match target {
            Some((field, ty)) => {
                if action.assigned.iter().any(|done| done == field) {
                    return Err(format!("state variable '{field}' is assigned twice"));
                }
                let tla = translate(read, ty, vars)?;
                action.clauses.push(format!("{field}' = {}", tla.value));
                action.assigned.push(field.to_string());
                steps.push((tla.defined, None));
            }
            None => {
                if let Some(field) = action.assigned.first() {
                    return Err(format!(
                        "`{}`: an early return must come before every assignment (state \
                         variable '{field}' is already assigned when Rust returns)",
                        stmt.to_token_stream()
                    ));
                }
                let tla = translate(read, Ty::Bool, vars)?;
                // The statements after it run where it does not return.
                let runs_on = format!("(~{})", tla.value);
                action.clauses.push(runs_on.clone());
                steps.push((tla.defined, Some(runs_on)));
            }
        }
    }
    for (defined, guard) in steps.into_iter().rev() {
        if let Some(guard) = guard {
            action.panic_free = action.panic_free.map(|rest| format!("({guard} => {rest})"));
        }
        action.panic_free = and(defined, action.panic_free.take());
    }
    Ok(action)
}

/// The condition of an early return `if <cond> { return; }`: no `else`, and
/// a block of exactly `return;` (or `return`) with no value.
fn early_return(early: &syn::ExprIf) -> Result<&Expr, String> {
    let returns = match early.then_branch.stmts.as_slice() {
        [Stmt::Expr(Expr::Return(ret), _)] => ret.expr.is_none(),
        _ => false,
    };
    if early.else_branch.is_some() || !returns {
        return Err(format!(
            "`{}`: the only `if` in an action is an early return `if <bool> {{ return; }}`",
            early.to_token_stream()
        ));
    }
    Ok(&early.cond)
}

/// The state fields an expression reads.
fn fields_read(expr: &Expr) -> Vec<String> {
    struct Reads(Vec<String>);
    impl<'ast> Visit<'ast> for Reads {
        fn visit_expr_field(&mut self, field: &'ast syn::ExprField) {
            if let (Expr::Path(base), Member::Named(name)) = (&*field.base, &field.member) {
                if base.path.is_ident("self") {
                    self.0.push(name.to_string());
                }
            }
            syn::visit::visit_expr_field(self, field);
        }
    }
    let mut reads = Reads(Vec::new());
    reads.visit_expr(expr);
    reads.0
}
