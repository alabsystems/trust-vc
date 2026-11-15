//! Source-level desugaring of a bounded, flat `for i in LO..HI { BODY }` range
//! loop into the equivalent counter-driven `while` loop that the extractor
//! already reasons about soundly.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//!   for i in LO..HI  { BODY }  →  { let mut i = LO; while i <  HI { invariant!(LO <= i); invariant!(!(LO <= HI) || i <= HI);     BODY  i = i + 1; } }
//!   for i in LO..=HI { BODY }  →  { let mut i = LO; while i <= HI { invariant!(LO <= i); invariant!(!(LO <= HI) || i <= HI + 1); BODY  i = i + 1; } }
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

    // (5) The body must not `continue` THIS loop: the counter increment is
    // appended at the END of the `while` body, and a `continue` would skip it
    // (an infinite loop the source does not have). Any other shape — `if`,
    // `match`, nested loops, `break`, `return`, calls — is fine: the produced
    // `while` is then handled by the ordinary loop machinery (exact lane when
    // flat, havoc lane otherwise), never a false `Verified`. (Relaxed
    // 2026-09-10 from "flat bodies only".)
    if continues_this_loop(&for_loop.body, for_loop.label.as_ref()) {
        return None;
    }

    // Idents assigned ANYWHERE in the body (nested blocks/branches/loops
    // included; a field/index write and a `&mut x` argument count for their
    // root — conservative).
    let assigned = assigned_idents_deep(&for_loop.body);

    // (3) body must not reassign the loop variable.
    if assigned.contains(&loop_var.to_string()) {
        return None;
    }

    // (4) HI's identifier (if any) must not be assigned in the body: Rust
    // evaluates the range ONCE, while the `while` guard re-reads it.
    if let Some(hi_ident) = bound_ident(hi) {
        if assigned.contains(&hi_ident.to_string()) {
            return None;
        }
    }

    // Auto-inject `LO <= i` only when LO's idents are disjoint from the
    // body-assigned set (else the lower bound is not stable).
    let inject_lower = ident_set(lo).is_disjoint(&assigned);
    // Auto-inject the UPPER bound (2026-09-10, row 433) when both bounds are
    // stable: `LO <= HI ==> i <= HI` for `..` and `LO <= HI ==> i <= HI + 1`
    // for `..=`, written with `||`. Base case: a tautology at `i == LO`, so an
    // empty range (`LO > HI`) never over-rejects. Step: from the guard alone
    // (`i < HI ⊢ i + 1 <= HI`; `i <= HI ⊢ i + 1 <= HI + 1`). With the negated
    // guard at exit this pins `i == HI` (resp. `HI + 1`) whenever `LO <= HI`,
    // which is what an accumulator invariant needs after the loop — the
    // Verus range iterator's `cur == end` fact.
    let inject_upper = inject_lower && ident_set(hi).is_disjoint(&assigned);

    let guard: Expr = if inclusive {
        syn::parse_quote!(#loop_var <= #hi)
    } else {
        syn::parse_quote!(#loop_var < #hi)
    };

    let mut while_body: Vec<Stmt> = Vec::new();
    if inject_lower {
        while_body.push(syn::parse_quote!(trust_vc::invariant!(#lo <= #loop_var);));
    }
    if inject_upper {
        if inclusive {
            while_body.push(
                syn::parse_quote!(trust_vc::invariant!(!(#lo <= #hi) || #loop_var <= #hi + 1);),
            );
        } else {
            while_body
                .push(syn::parse_quote!(trust_vc::invariant!(!(#lo <= #hi) || #loop_var <= #hi);));
        }
    }
    while_body.extend(for_loop.body.stmts.iter().cloned());
    while_body.push(syn::parse_quote!(#loop_var = #loop_var + 1;));

    // The loop's label (if any) moves onto the `while`, so a labeled `break`
    // inside the body keeps its target.
    let label = for_loop.label.clone();
    Some(syn::parse_quote!({
        let mut #loop_var = #lo;
        #label while #guard {
            #(#while_body)*
        }
    }))
}

/// True when `body` contains a `continue` that targets the `for` loop being
/// rewritten: an unlabeled `continue` outside any nested loop, or a labeled one
/// naming the loop's own label. Closures and nested items are not descended.
pub(crate) fn continues_this_loop(body: &syn::Block, label: Option<&syn::Label>) -> bool {
    struct ContinueVisitor<'a> {
        own_label: Option<&'a str>,
        nested_loops: usize,
        found: bool,
    }
    impl<'ast> syn::visit::Visit<'ast> for ContinueVisitor<'_> {
        fn visit_expr_continue(&mut self, expr: &'ast syn::ExprContinue) {
            match &expr.label {
                None => {
                    if self.nested_loops == 0 {
                        self.found = true;
                    }
                }
                Some(lifetime) => {
                    if Some(lifetime.ident.to_string().as_str()) == self.own_label {
                        self.found = true;
                    }
                }
            }
        }
        fn visit_expr_while(&mut self, expr: &'ast syn::ExprWhile) {
            self.nested_loops += 1;
            syn::visit::visit_expr_while(self, expr);
            self.nested_loops -= 1;
        }
        fn visit_expr_loop(&mut self, expr: &'ast syn::ExprLoop) {
            self.nested_loops += 1;
            syn::visit::visit_expr_loop(self, expr);
            self.nested_loops -= 1;
        }
        fn visit_expr_for_loop(&mut self, expr: &'ast syn::ExprForLoop) {
            self.nested_loops += 1;
            syn::visit::visit_expr_for_loop(self, expr);
            self.nested_loops -= 1;
        }
        fn visit_expr_closure(&mut self, _expr: &'ast syn::ExprClosure) {}
        fn visit_item(&mut self, _item: &'ast syn::Item) {}
    }
    let own = label.map(|l| l.name.ident.to_string());
    let mut visitor = ContinueVisitor {
        own_label: own.as_deref(),
        nested_loops: 0,
        found: false,
    };
    syn::visit::Visit::visit_block(&mut visitor, body);
    visitor.found
}

/// Every identifier that is the ROOT of an assignment target or of a `&mut`
/// borrow anywhere in `block` (nested blocks, branches and loops included;
/// closures and nested items excluded). Conservative: a field or index write
/// counts for its root variable.
pub(crate) fn assigned_idents_deep(block: &syn::Block) -> BTreeSet<String> {
    struct AssignCollector {
        idents: BTreeSet<String>,
    }
    fn root_ident(expr: &Expr) -> Option<String> {
        match expr {
            Expr::Path(path) if path.qself.is_none() => {
                path.path.get_ident().map(|ident| ident.to_string())
            }
            Expr::Field(field) => root_ident(&field.base),
            Expr::Index(index) => root_ident(&index.expr),
            Expr::Paren(paren) => root_ident(&paren.expr),
            Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Deref(_)) => {
                root_ident(&unary.expr)
            }
            _ => None,
        }
    }
    impl<'ast> syn::visit::Visit<'ast> for AssignCollector {
        fn visit_expr_assign(&mut self, expr: &'ast syn::ExprAssign) {
            if let Some(name) = root_ident(&expr.left) {
                self.idents.insert(name);
            }
            syn::visit::visit_expr_assign(self, expr);
        }
        fn visit_expr_binary(&mut self, expr: &'ast syn::ExprBinary) {
            if is_assignment_binop(&expr.op) {
                if let Some(name) = root_ident(&expr.left) {
                    self.idents.insert(name);
                }
            }
            syn::visit::visit_expr_binary(self, expr);
        }
        fn visit_expr_reference(&mut self, expr: &'ast syn::ExprReference) {
            if expr.mutability.is_some() {
                if let Some(name) = root_ident(&expr.expr) {
                    self.idents.insert(name);
                }
            }
            syn::visit::visit_expr_reference(self, expr);
        }
        fn visit_expr_closure(&mut self, _expr: &'ast syn::ExprClosure) {}
        fn visit_item(&mut self, _item: &'ast syn::Item) {}
    }
    let mut collector = AssignCollector {
        idents: BTreeSet::new(),
    };
    syn::visit::Visit::visit_block(&mut collector, block);
    collector.idents
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

pub(crate) fn is_assignment_binop(op: &syn::BinOp) -> bool {
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
