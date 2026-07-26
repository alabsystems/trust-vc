//! Source-level desugaring of a bounded, flat `for i in LO..HI { BODY }` range
//! loop into the equivalent counter-driven `while` loop that the extractor
//! already reasons about soundly.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//!   for i in LO..HI  { BODY }  →  { let mut i = LO; while i <  HI { invariant!(LO <= i); BODY  i = i + 1; } }
//!   for i in LO..=HI { BODY }  →  { let mut i = LO; while i <= HI { invariant!(LO <= i); BODY  i = i + 1; } }
//!
//! The rewrite FIRES ONLY when every one of these holds (else the `for` is left
//! verbatim and keeps its current — fail-closed — behavior):
//!   1. the pattern is a plain `Pat::Ident` (`i`) — no `mut`/`ref`/subpattern;
//!   2. the iterator is a `LO..HI` / `LO..=HI` range whose BOTH bounds are each a
//!      bare integer literal or a single identifier (stable + side-effect-free —
//!      a call/index/arith bound is left alone because the `while` guard
//!      re-evaluates HI every turn whereas the `for` range is built once);
//!   3. the body never assigns the loop var (a `for` rebinds `i` each turn; a
//!      `while` would carry the mutation);
//!   4. HI's identifier (if any) is not assigned in the body (else the guard
//!      tracks a moving bound — real divergence the single-eval `for` would not);
//!   5. the body is FLAT — every statement is a spec-assertion macro or a pure-
//!      arithmetic scalar/compound assignment (a strict subset of
//!      `loop_body_transition_is_exact`; `push` forms are excluded in v1). So
//!      break/continue/return/`?`/if/match/nested-loops/calls all make the body
//!      non-flat and the `for` is never rewritten — no non-flat loop regresses.
//!
//! It auto-injects ONLY the lower-bound invariant `LO <= i`, and only when LO's
//! identifiers are disjoint from the body-assigned set. That invariant is always
//! inductive (base `LO <= LO`; step `LO <= i ⇒ LO <= i+1`) and the `while`
//! machinery still checks it base + step, so it can never produce a false
//! `Verified`. The upper bound `i <= HI` is deliberately NOT injected: its base
//! check `LO <= HI` is unprovable for an unconstrained `a..b`, so injecting it
//! would spuriously reject empty/reversed no-op ranges (a completeness
//! regression); a proof that needs it writes `invariant!(i <= HI)` or uses the
//! negated-guard exit fact.
//!
//! SOUNDNESS (never a false `Verified`): the produced `while` is handled by the
//! existing loop machinery — base (establishment) + inductive-step invariant
//! checks, the flat single-iteration transition (or pure havoc for a non-flat
//! body), and the negated-guard exit fact. The desugar itself only ADDS a sound,
//! inductive invariant and a plain counter increment; it turns a previously
//! fail-closed range `for` into a soundly verified or soundly refuted `while`.
//! The increment is emitted as a plain `i = i + 1` (NOT `i += 1`) because the
//! untyped counter's single-iteration transition is captured only on the
//! plain-assign path.

use std::collections::BTreeSet;
use syn::visit_mut::{self, VisitMut};
use syn::{Expr, ExprForLoop, Ident, ItemFn, Pat, RangeLimits, Stmt};

/// Rewrite every qualifying bounded flat range `for` loop in `func` into its
/// counter-driven `while` equivalent. Returns `Some(rewritten)` iff at least one
/// loop was rewritten; `None` leaves the caller's borrow untouched.
pub(crate) fn desugar_for_range(func: &ItemFn) -> Option<ItemFn> {
    let mut rewritten = func.clone();
    let mut visitor = ForRangeVisitor { changed: false };
    visitor.visit_item_fn_mut(&mut rewritten);
    visitor.changed.then_some(rewritten)
}

struct ForRangeVisitor {
    changed: bool,
}

impl VisitMut for ForRangeVisitor {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        // Recurse first (bottom-up): a nested qualifying loop is rewritten in
        // isolation. Its containing loop, whose body now holds a `while` block,
        // is no longer flat and is therefore left as-is.
        visit_mut::visit_expr_mut(self, expr);

        if let Expr::ForLoop(for_loop) = expr {
            if let Some(replacement) = rewrite_for_loop(for_loop) {
                *expr = replacement;
                self.changed = true;
            }
        }
    }
}

/// Build the `{ let mut i = LO; while GUARD { [invariant!(LO<=i)] BODY i = i+1; } }`
/// block for a qualifying loop, or `None` if the loop does not qualify.
fn rewrite_for_loop(for_loop: &ExprForLoop) -> Option<Expr> {
    // (1) plain `Pat::Ident` loop variable.
    let loop_var = plain_loop_var(&for_loop.pat)?;

    // (2) `LO..HI` / `LO..=HI` with simple (literal-or-single-ident) bounds.
    let (lo, hi, inclusive) = match for_loop.expr.as_ref() {
        Expr::Range(range) => {
            let lo = range.start.as_deref()?;
            let hi = range.end.as_deref()?;
            if !is_simple_bound(lo) || !is_simple_bound(hi) {
                return None;
            }
            let inclusive = matches!(range.limits, RangeLimits::Closed(_));
            (lo, hi, inclusive)
        }
        _ => return None,
    };

    // (5) FLAT body — every statement a spec macro or pure-arith scalar assign.
    if !for_loop.body.stmts.iter().all(stmt_is_flat) {
        return None;
    }

    // Idents assigned anywhere in the (flat) body.
    let assigned = body_assigned_idents(&for_loop.body.stmts);

    // (3) body must not reassign the loop variable.
    if assigned.contains(&loop_var.to_string()) {
        return None;
    }

    // (4) HI's identifier (if any) must not be assigned in the body.
    if let Some(hi_ident) = bound_ident(hi) {
        if assigned.contains(&hi_ident.to_string()) {
            return None;
        }
    }

    // Auto-inject `LO <= i` only when LO's idents are disjoint from the
    // body-assigned set (else the lower bound is not stable).
    let inject_lower = ident_set(lo).is_disjoint(&assigned);

    let guard: Expr = if inclusive {
        syn::parse_quote!(#loop_var <= #hi)
    } else {
        syn::parse_quote!(#loop_var < #hi)
    };

    let mut while_body: Vec<Stmt> = Vec::new();
    if inject_lower {
        while_body.push(syn::parse_quote!(trust_vc::invariant!(#lo <= #loop_var);));
    }
    while_body.extend(for_loop.body.stmts.iter().cloned());
    while_body.push(syn::parse_quote!(#loop_var = #loop_var + 1;));

    Some(syn::parse_quote!({
        let mut #loop_var = #lo;
        while #guard {
            #(#while_body)*
        }
    }))
}

/// The loop variable of a plain `Pat::Ident` pattern (no `ref`, no `mut`, no
/// subpattern binding) — the only shape whose value is a fresh per-iteration
/// counter equivalent to a `while`-carried `let mut`.
fn plain_loop_var(pat: &Pat) -> Option<&Ident> {
    match pat {
        Pat::Ident(pat_ident)
            if pat_ident.by_ref.is_none()
                && pat_ident.mutability.is_none()
                && pat_ident.subpat.is_none() =>
        {
            Some(&pat_ident.ident)
        }
        _ => None,
    }
}

/// A range bound that is stable and side-effect-free across repeated evaluation:
/// a bare integer literal or a single identifier.
fn is_simple_bound(expr: &Expr) -> bool {
    match expr {
        Expr::Lit(lit) => matches!(lit.lit, syn::Lit::Int(_)),
        Expr::Path(path) => path.qself.is_none() && path.path.get_ident().is_some(),
        _ => false,
    }
}

/// The identifier of a single-ident bound (`None` for a literal bound).
fn bound_ident(expr: &Expr) -> Option<&Ident> {
    match expr {
        Expr::Path(path) if path.qself.is_none() => path.path.get_ident(),
        _ => None,
    }
}

/// True iff `stmt` is FLAT: a spec-assertion macro, or a scalar/compound
/// assignment whose right-hand side is pure arithmetic. A strict subset of
/// `body_extract::loop_body_transition_is_exact` (the `push` accumulate forms are
/// excluded here in v1).
fn stmt_is_flat(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Macro(stmt_macro) => is_spec_assertion_macro(&stmt_macro.mac.path),
        Stmt::Expr(expr, _) => match expr {
            Expr::Assign(assign) => {
                expr_is_ident(&assign.left) && expr_is_pure_arith(&assign.right)
            }
            Expr::Binary(binary) if is_assignment_binop(&binary.op) => {
                expr_is_ident(&binary.left) && expr_is_pure_arith(&binary.right)
            }
            Expr::Macro(expr_macro) => is_spec_assertion_macro(&expr_macro.mac.path),
            _ => false,
        },
        _ => false,
    }
}

/// The set of identifiers that are the target of an assignment in a flat body.
/// Because the body is flat, every assignment target is a bare path-ident.
fn body_assigned_idents(stmts: &[Stmt]) -> BTreeSet<String> {
    let mut assigned = BTreeSet::new();
    for stmt in stmts {
        if let Stmt::Expr(expr, _) = stmt {
            let target = match expr {
                Expr::Assign(assign) => ident_of(&assign.left),
                Expr::Binary(binary) if is_assignment_binop(&binary.op) => ident_of(&binary.left),
                _ => None,
            };
            if let Some(name) = target {
                assigned.insert(name);
            }
        }
    }
    assigned
}

/// Every identifier appearing in `expr` (used to test lower-bound stability).
fn ident_set(expr: &Expr) -> BTreeSet<String> {
    struct IdentCollector {
        idents: BTreeSet<String>,
    }
    impl<'ast> syn::visit::Visit<'ast> for IdentCollector {
        fn visit_ident(&mut self, ident: &'ast Ident) {
            self.idents.insert(ident.to_string());
        }
    }
    let mut collector = IdentCollector {
        idents: BTreeSet::new(),
    };
    syn::visit::Visit::visit_expr(&mut collector, expr);
    collector.idents
}

fn expr_is_ident(expr: &Expr) -> bool {
    ident_of(expr).is_some()
}

fn ident_of(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Path(path) if path.qself.is_none() => {
            path.path.get_ident().map(std::string::ToString::to_string)
        }
        _ => None,
    }
}

fn is_assignment_binop(op: &syn::BinOp) -> bool {
    matches!(
        op,
        syn::BinOp::AddAssign(_)
            | syn::BinOp::SubAssign(_)
            | syn::BinOp::MulAssign(_)
            | syn::BinOp::DivAssign(_)
            | syn::BinOp::RemAssign(_)
            | syn::BinOp::BitXorAssign(_)
            | syn::BinOp::BitAndAssign(_)
            | syn::BinOp::BitOrAssign(_)
            | syn::BinOp::ShlAssign(_)
            | syn::BinOp::ShrAssign(_)
    )
}

/// Pure arithmetic: identifiers, literals, parens/grouping, unary/binary
/// non-assignment operators, and numeric casts. Excludes calls, method calls,
/// indexing, field access, references, blocks, closures, and control flow.
fn expr_is_pure_arith(expr: &Expr) -> bool {
    match expr {
        Expr::Path(_) | Expr::Lit(_) => true,
        Expr::Paren(inner) => expr_is_pure_arith(&inner.expr),
        Expr::Group(inner) => expr_is_pure_arith(&inner.expr),
        Expr::Unary(unary) => expr_is_pure_arith(&unary.expr),
        Expr::Cast(cast) => expr_is_pure_arith(&cast.expr),
        Expr::Binary(binary) if !is_assignment_binop(&binary.op) => {
            expr_is_pure_arith(&binary.left) && expr_is_pure_arith(&binary.right)
        }
        _ => false,
    }
}

/// A spec-assertion macro whose invocation never mutates an exec scalar (so it is
/// admissible inside a flat body). Matches `body_extract::is_spec_assertion_macro_path`.
fn is_spec_assertion_macro(path: &syn::Path) -> bool {
    let Some(name) = path.segments.last().map(|seg| seg.ident.to_string()) else {
        return false;
    };
    name == "invariant"
        || name == "invariant_except_break"
        || name == "assume"
        || name == "assert"
        || name == "loop_decreases"
        || name == "loop_ensures"
        || name.starts_with("assert_")
}
