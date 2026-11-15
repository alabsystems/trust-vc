//! Source-level rotation of a `while` loop whose guard is a BLOCK with flat
//! scalar side effects into the equivalent pure-guard `while` loop that the
//! extractor already reasons about soundly — and, since 2026-09-11, the simpler
//! hoisting of an `if` guard block's statements in front of the `if`
//! (`rewrite_if`).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! ```text
//! 'l: while { S; c } { INV…; B }
//!   →
//! {
//!     let mut v__pre_guard = v;            // one per var S assigns
//!     S;                                   // the FIRST guard evaluation
//!     'l: while c {
//!         INV…[v ↦ v__pre_guard];          // invariant! / invariant_except_break! / loop_decreases!
//!         trust_vc::invariant!(v == S(v__pre_guard)…);   // the guard block's transition
//!         B                                // unchanged (loop_ensures! included)
//!         v__pre_guard = v;                // snapshot the head state …
//!         S;                               // … then the NEXT guard evaluation
//!     }
//! }
//! ```
//!
//! SEMANTICS. Verus (and Rust) evaluate the guard block — side effects and all —
//! at every loop head, including the last, failing evaluation: the user's
//! invariants hold at the head BEFORE the block runs, and the state after the
//! loop is a head state satisfying them, transformed by `S`, with `c` false.
//! The rotation states exactly that: each guard-assigned var `v` gets a
//! snapshot local `v__pre_guard` holding its value at the original head, every
//! head-state predicate (`invariant!`, `invariant_except_break!`,
//! `loop_decreases!`) is rewritten over the snapshots, and the injected
//! invariant `v == S(v__pre_guard)` (the composed effect of `S`, one equation
//! per assigned var) carries the guard block's transition to the rotated head.
//! `loop_ensures!` is about the EXIT state (after `S`), so it is kept verbatim.
//! Base case: the prologue `let mut v__pre_guard = v; S` establishes both the
//! rewritten user invariants (they are the originals over the entry state) and
//! the injected equations (by value numbering). Step: the body ends with
//! `v__pre_guard = v; S`, re-establishing the equations, and the rewritten
//! user invariants are the originals at the next original head. Exit: the
//! negated pure guard `!(c)` over the post-`S` state plus the invariants over
//! the snapshots — `i <= 10 ∧ x__pre_guard == i ∧ x == x__pre_guard + 1 ∧
//! !(i < 10)` pins `i == 10 ∧ x == 11` for upstream `complex_while`.
//!
//! The rewrite FIRES ONLY when every one of these holds (else the `while` is
//! left verbatim and keeps its current — fail-closed, no exit fact — behavior):
//!   1. the guard is an unlabeled block `{ S; c }` with a trailing expression
//!      `c` that is side-effect-free (no assignment, call, macro, block, `let`,
//!      closure, or control flow);
//!   2. every statement of `S` is a plain scalar assignment `v = rhs;` or a
//!      compound one `v op= rhs;` (normalized to `v = v op rhs`) whose target is
//!      a single identifier and whose right-hand side is pure arithmetic over
//!      literals and identifiers (`+ - * / % & | ^ << >>`, unary, parens,
//!      `as` casts) — so the composed transition is expressible as an
//!      invariant;
//!   3. the body never `continue`s THIS loop (the snapshot + `S` tail would be
//!      skipped — the source re-runs the guard block on `continue`);
//!   4. the body binds (`let` / pattern) no name that `S` or `c` reads or
//!      writes — the appended tail must read the loop's vars, not a shadow;
//!   5. every spec macro of the body parses as one expression (the snapshot
//!      substitution is done on the parsed expression, path-precisely).
//!
//! SOUNDNESS (never a false `Verified`): the produced `while` is checked by the
//! existing loop machinery — the rewritten invariants base + step, the injected
//! transition equations base + step (they are inductive by construction, but
//! they are CHECKED, not assumed), the flat single-iteration transition (or
//! havoc for a non-flat body), and the negated pure-guard exit fact. The
//! rewrite only restates the program: the prologue is the guard block's first
//! evaluation, the tail its next one, and a `break` (which skips the guard in
//! the source) skips the tail here too.

use std::collections::{BTreeMap, BTreeSet};
use syn::visit_mut::{self, VisitMut};
use syn::{Expr, ExprWhile, Ident, ItemFn, Stmt};

use crate::for_range_desugar::{continues_this_loop, is_assignment_binop};

/// Rewrite every qualifying side-effect-guard `while` in `func` into its
/// rotated pure-guard equivalent. Returns `Some(rewritten)` iff at least one
/// loop was rewritten; `None` leaves the caller's borrow untouched.
pub(crate) fn desugar_while_guard_blocks(func: &ItemFn) -> Option<ItemFn> {
    let mut rewritten = func.clone();
    let mut visitor = WhileGuardVisitor { changed: false };
    visitor.visit_item_fn_mut(&mut rewritten);
    visitor.changed.then_some(rewritten)
}

struct WhileGuardVisitor {
    changed: bool,
}

impl VisitMut for WhileGuardVisitor {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        // Bottom-up: a nested qualifying loop is rewritten first, so an outer
        // rewrite sees the already-rotated inner loop as ordinary body.
        visit_mut::visit_expr_mut(self, expr);
        if let Expr::While(expr_while) = expr {
            if let Some(replacement) = rewrite_while(expr_while) {
                *expr = replacement;
                self.changed = true;
            }
        }
    }

    /// `if { S; c } A else B` in STATEMENT position (a statement, a `let`
    /// initializer, or the block's tail) has `S` spliced in front of it as
    /// ordinary statements of the enclosing block and keeps `c` as its guard
    /// (see `hoist_if_guard`). Deeper expression positions are left alone: a
    /// wrapping block would itself become the rendered value there.
    fn visit_block_mut(&mut self, block: &mut syn::Block) {
        visit_mut::visit_block_mut(self, block);
        let mut out: Vec<Stmt> = Vec::with_capacity(block.stmts.len());
        for stmt in block.stmts.drain(..) {
            let mut stmt = stmt;
            let hoisted = match &mut stmt {
                Stmt::Expr(Expr::If(expr_if), _) => hoist_if_guard(expr_if),
                Stmt::Local(local) => match local.init.as_mut() {
                    Some(init) if init.diverge.is_none() => match init.expr.as_mut() {
                        Expr::If(expr_if) => hoist_if_guard(expr_if),
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            };
            if let Some(prefix) = hoisted {
                out.extend(prefix);
                self.changed = true;
            }
            out.push(stmt);
        }
        block.stmts = out;
    }
}

/// `if { S; c } A else B` → `S; if c A else B` (2026-09-11). An `if` guard
/// block runs exactly once, before the branch is chosen, so hoisting its
/// statements in front of the `if` is semantics-preserving; the rewrite FIRES
/// ONLY when the guard is an unlabeled block whose statements bind no name
/// (no `let` / pattern — a binding local to the guard block would otherwise
/// become visible to the branches), contain no nested control flow, and whose
/// tail condition is side-effect-free. The extractor previously rendered the
/// whole block as the path condition and failed closed on its side effect
/// ("compound assignment not supported in verification"); the hoisted
/// statements are ordinary straight-line code, value-numbered exactly as if
/// written before the `if`, and `c` is the plain branch condition. Returns the
/// statements to splice in front of the `if` (the `if`'s guard is replaced by
/// `c` in place), or `None` when the shape does not qualify.
fn hoist_if_guard(expr_if: &mut syn::ExprIf) -> Option<Vec<Stmt>> {
    let block = match expr_if.cond.as_ref() {
        Expr::Block(block) if block.label.is_none() => &block.block,
        _ => return None,
    };
    let (tail, prefix) = block.stmts.split_last()?;
    let cond = match tail {
        Stmt::Expr(expr, None) => expr.clone(),
        _ => return None,
    };
    if prefix.is_empty() || !is_effect_free(&cond) {
        return None;
    }
    for stmt in prefix {
        match stmt {
            Stmt::Expr(inner, _) => {
                if matches!(
                    inner,
                    Expr::Let(_)
                        | Expr::Block(_)
                        | Expr::Loop(_)
                        | Expr::While(_)
                        | Expr::ForLoop(_)
                        | Expr::If(_)
                        | Expr::Match(_)
                        | Expr::Closure(_)
                        | Expr::Return(_)
                        | Expr::Break(_)
                        | Expr::Continue(_)
                ) {
                    return None;
                }
            }
            Stmt::Macro(_) => {}
            _ => return None,
        }
    }
    let prefix: Vec<Stmt> = prefix.to_vec();
    *expr_if.cond = cond;
    Some(prefix)
}

/// One normalized guard-block assignment `target = rhs`.
struct GuardAssign {
    target: Ident,
    rhs: Expr,
}

fn rewrite_while(expr_while: &ExprWhile) -> Option<Expr> {
    // (1) an unlabeled block guard with a trailing pure expression.
    let block = match expr_while.cond.as_ref() {
        Expr::Block(block) if block.label.is_none() => &block.block,
        _ => return None,
    };
    let (tail, prefix) = block.stmts.split_last()?;
    let cond = match tail {
        Stmt::Expr(expr, None) => expr,
        _ => return None,
    };
    if !is_effect_free(cond) {
        return None;
    }

    // (2) `S` is a sequence of flat scalar assignments over pure arithmetic.
    let mut assigns = Vec::with_capacity(prefix.len());
    for stmt in prefix {
        assigns.push(guard_assignment(stmt)?);
    }
    let assigned: BTreeSet<String> = assigns
        .iter()
        .map(|assign| assign.target.to_string())
        .collect();
    let mut guard_reads = ident_set(cond);
    for assign in &assigns {
        guard_reads.extend(ident_set(&assign.rhs));
    }

    // (3) no `continue` targeting this loop.
    if continues_this_loop(&expr_while.body, expr_while.label.as_ref()) {
        return None;
    }
    // (4) the body binds none of the names the tail reads or writes.
    let tail_names: BTreeSet<String> = assigned.union(&guard_reads).cloned().collect();
    if body_binds_any(&expr_while.body, &tail_names) {
        return None;
    }

    // The composed effect of `S` over the snapshots: run the assignments in
    // order on a substitution map that starts at `v ↦ v__pre_guard`.
    let snapshot = |name: &str| {
        Ident::new(
            &format!("{name}__pre_guard"),
            proc_macro2::Span::call_site(),
        )
    };
    let mut sigma: BTreeMap<String, Expr> = assigned
        .iter()
        .map(|name| {
            let ident = snapshot(name);
            (name.clone(), syn::parse_quote!(#ident))
        })
        .collect();
    for assign in &assigns {
        let composed = substitute_paths(&assign.rhs, &sigma);
        sigma.insert(assign.target.to_string(), composed);
    }

    // The head-state substitution for the user's spec macros: `v ↦ v__pre_guard`.
    let head_subst: BTreeMap<String, Expr> = assigned
        .iter()
        .map(|name| {
            let ident = snapshot(name);
            (name.clone(), syn::parse_quote!(#ident))
        })
        .collect();

    // (5) rewrite the body: head-state spec macros over the snapshots, the
    // rest verbatim. The injected transition equations go AFTER the user's
    // leading spec macros: the body's arithmetic obligations are checked
    // under the invariants in written order, each addition inside an
    // invariant under the invariants BEFORE it — so the user's bounds (`x ==
    // i`, `i <= 10`) must precede `x == x__pre_guard + 1` for its `+ 1` to be
    // provably in range.
    let mut body_stmts: Vec<Stmt> =
        Vec::with_capacity(expr_while.body.stmts.len() + 2 * assigns.len() + 2);
    let leading_specs = expr_while
        .body
        .stmts
        .iter()
        .take_while(|stmt| is_loop_spec_macro_stmt(stmt))
        .count();
    for stmt in &expr_while.body.stmts[..leading_specs] {
        body_stmts.push(rewrite_head_spec_stmt(stmt, &head_subst)?);
    }
    for name in &assigned {
        let var = Ident::new(name, proc_macro2::Span::call_site());
        let composed = &sigma[name];
        body_stmts.push(syn::parse_quote!(trust_vc::invariant!(#var == #composed);));
    }
    for stmt in &expr_while.body.stmts[leading_specs..] {
        body_stmts.push(rewrite_head_spec_stmt(stmt, &head_subst)?);
    }
    for name in &assigned {
        let var = Ident::new(name, proc_macro2::Span::call_site());
        let snap = snapshot(name);
        body_stmts.push(syn::parse_quote!(#snap = #var;));
    }
    for assign in &assigns {
        let target = &assign.target;
        let rhs = &assign.rhs;
        body_stmts.push(syn::parse_quote!(#target = #rhs;));
    }

    let mut prologue: Vec<Stmt> = Vec::with_capacity(2 * assigns.len());
    for name in &assigned {
        let var = Ident::new(name, proc_macro2::Span::call_site());
        let snap = snapshot(name);
        prologue.push(syn::parse_quote!(let mut #snap = #var;));
    }
    for assign in &assigns {
        let target = &assign.target;
        let rhs = &assign.rhs;
        prologue.push(syn::parse_quote!(#target = #rhs;));
    }

    let label = expr_while.label.clone();
    let attrs = &expr_while.attrs;
    Some(syn::parse_quote!({
        #(#prologue)*
        #(#attrs)* #label while #cond {
            #(#body_stmts)*
        }
    }))
}

/// A guard-block statement as a normalized `target = rhs` assignment, or
/// `None` when it is anything else.
fn guard_assignment(stmt: &Stmt) -> Option<GuardAssign> {
    let expr = match stmt {
        Stmt::Expr(expr, Some(_)) => expr,
        _ => return None,
    };
    match expr {
        Expr::Assign(assign) => {
            let target = single_ident(&assign.left)?.clone();
            is_pure_arith(&assign.right).then(|| GuardAssign {
                target,
                rhs: (*assign.right).clone(),
            })
        }
        Expr::Binary(binary) if is_assignment_binop(&binary.op) => {
            let target = single_ident(&binary.left)?.clone();
            if !is_pure_arith(&binary.right) {
                return None;
            }
            let op = plain_binop(&binary.op)?;
            let rhs_inner = &binary.right;
            let rhs: Expr = syn::parse_quote!(#target #op (#rhs_inner));
            Some(GuardAssign { target, rhs })
        }
        _ => None,
    }
}

fn plain_binop(op: &syn::BinOp) -> Option<syn::BinOp> {
    use syn::BinOp;
    let span = proc_macro2::Span::call_site();
    Some(match op {
        BinOp::AddAssign(_) => BinOp::Add(syn::token::Plus(span)),
        BinOp::SubAssign(_) => BinOp::Sub(syn::token::Minus(span)),
        BinOp::MulAssign(_) => BinOp::Mul(syn::token::Star(span)),
        BinOp::DivAssign(_) => BinOp::Div(syn::token::Slash(span)),
        BinOp::RemAssign(_) => BinOp::Rem(syn::token::Percent(span)),
        BinOp::BitXorAssign(_) => BinOp::BitXor(syn::token::Caret(span)),
        BinOp::BitAndAssign(_) => BinOp::BitAnd(syn::token::And(span)),
        BinOp::BitOrAssign(_) => BinOp::BitOr(syn::token::Or(span)),
        BinOp::ShlAssign(_) => BinOp::Shl(syn::token::Shl(span)),
        BinOp::ShrAssign(_) => BinOp::Shr(syn::token::Shr(span)),
        _ => return None,
    })
}

fn single_ident(expr: &Expr) -> Option<&Ident> {
    match expr {
        Expr::Path(path) if path.qself.is_none() && path.attrs.is_empty() => path.path.get_ident(),
        Expr::Paren(paren) => single_ident(&paren.expr),
        _ => None,
    }
}

/// Pure arithmetic over literals and identifiers: the shapes whose composed
/// value is expressible as an invariant and re-evaluable without effects.
fn is_pure_arith(expr: &Expr) -> bool {
    match expr {
        Expr::Lit(lit) => matches!(lit.lit, syn::Lit::Int(_) | syn::Lit::Bool(_)),
        Expr::Path(_) => single_ident(expr).is_some(),
        Expr::Paren(paren) => is_pure_arith(&paren.expr),
        Expr::Unary(unary) => {
            matches!(unary.op, syn::UnOp::Neg(_) | syn::UnOp::Not(_)) && is_pure_arith(&unary.expr)
        }
        Expr::Cast(cast) => is_pure_arith(&cast.expr),
        Expr::Binary(binary) => {
            !is_assignment_binop(&binary.op)
                && is_pure_arith(&binary.left)
                && is_pure_arith(&binary.right)
        }
        _ => false,
    }
}

/// True when `expr` performs no assignment, call, macro, block, closure, `let`,
/// or control-flow transfer — safe to re-evaluate as a pure guard.
fn is_effect_free(expr: &Expr) -> bool {
    struct EffectVisitor {
        effect: bool,
    }
    impl<'ast> syn::visit::Visit<'ast> for EffectVisitor {
        fn visit_expr_assign(&mut self, _: &'ast syn::ExprAssign) {
            self.effect = true;
        }
        fn visit_expr_binary(&mut self, expr: &'ast syn::ExprBinary) {
            if is_assignment_binop(&expr.op) {
                self.effect = true;
            } else {
                syn::visit::visit_expr_binary(self, expr);
            }
        }
        fn visit_expr_block(&mut self, _: &'ast syn::ExprBlock) {
            self.effect = true;
        }
        fn visit_expr_call(&mut self, _: &'ast syn::ExprCall) {
            self.effect = true;
        }
        fn visit_expr_method_call(&mut self, _: &'ast syn::ExprMethodCall) {
            self.effect = true;
        }
        fn visit_expr_macro(&mut self, _: &'ast syn::ExprMacro) {
            self.effect = true;
        }
        fn visit_expr_let(&mut self, _: &'ast syn::ExprLet) {
            self.effect = true;
        }
        fn visit_expr_closure(&mut self, _: &'ast syn::ExprClosure) {
            self.effect = true;
        }
        fn visit_expr_break(&mut self, _: &'ast syn::ExprBreak) {
            self.effect = true;
        }
        fn visit_expr_continue(&mut self, _: &'ast syn::ExprContinue) {
            self.effect = true;
        }
        fn visit_expr_return(&mut self, _: &'ast syn::ExprReturn) {
            self.effect = true;
        }
        fn visit_expr_try(&mut self, _: &'ast syn::ExprTry) {
            self.effect = true;
        }
        fn visit_expr_if(&mut self, _: &'ast syn::ExprIf) {
            self.effect = true;
        }
        fn visit_expr_match(&mut self, _: &'ast syn::ExprMatch) {
            self.effect = true;
        }
        fn visit_expr_while(&mut self, _: &'ast syn::ExprWhile) {
            self.effect = true;
        }
        fn visit_expr_loop(&mut self, _: &'ast syn::ExprLoop) {
            self.effect = true;
        }
        fn visit_expr_for_loop(&mut self, _: &'ast syn::ExprForLoop) {
            self.effect = true;
        }
        fn visit_expr_reference(&mut self, expr: &'ast syn::ExprReference) {
            if expr.mutability.is_some() {
                self.effect = true;
            } else {
                syn::visit::visit_expr_reference(self, expr);
            }
        }
    }
    let mut visitor = EffectVisitor { effect: false };
    syn::visit::Visit::visit_expr(&mut visitor, expr);
    !visitor.effect
}

/// Every identifier appearing in `expr`.
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

/// True when any `let` / pattern binding anywhere in `block` (nested blocks,
/// branches, loops, closures, match arms and `if let`s included) binds one of
/// `names`.
fn body_binds_any(block: &syn::Block, names: &BTreeSet<String>) -> bool {
    struct BindVisitor<'a> {
        names: &'a BTreeSet<String>,
        found: bool,
    }
    impl<'ast> syn::visit::Visit<'ast> for BindVisitor<'_> {
        fn visit_pat_ident(&mut self, pat: &'ast syn::PatIdent) {
            if self.names.contains(&pat.ident.to_string()) {
                self.found = true;
            }
            syn::visit::visit_pat_ident(self, pat);
        }
    }
    let mut visitor = BindVisitor {
        names,
        found: false,
    };
    syn::visit::Visit::visit_block(&mut visitor, block);
    visitor.found
}

/// Replace every single-identifier path in `expr` that `subst` maps.
fn substitute_paths(expr: &Expr, subst: &BTreeMap<String, Expr>) -> Expr {
    struct Subst<'a> {
        subst: &'a BTreeMap<String, Expr>,
    }
    impl VisitMut for Subst<'_> {
        fn visit_expr_mut(&mut self, expr: &mut Expr) {
            if let Some(ident) = single_ident(expr) {
                if let Some(replacement) = self.subst.get(&ident.to_string()) {
                    *expr = syn::parse_quote!((#replacement));
                    return;
                }
            }
            visit_mut::visit_expr_mut(self, expr);
        }
        fn visit_expr_closure_mut(&mut self, _: &mut syn::ExprClosure) {}
    }
    let mut out = expr.clone();
    Subst { subst }.visit_expr_mut(&mut out);
    out
}

/// True for a loop-spec macro statement (`invariant!`, `invariant_except_break!`,
/// `loop_ensures!`, `loop_decreases!`), the statements a loop body leads with.
fn is_loop_spec_macro_stmt(stmt: &Stmt) -> bool {
    let mac = match stmt {
        Stmt::Macro(stmt_macro) => &stmt_macro.mac,
        Stmt::Expr(Expr::Macro(expr_macro), _) => &expr_macro.mac,
        _ => return false,
    };
    mac.path.segments.last().is_some_and(|segment| {
        matches!(
            segment.ident.to_string().as_str(),
            "invariant" | "invariant_except_break" | "loop_ensures" | "loop_decreases"
        )
    })
}

/// A body statement with any HEAD-state spec macro (`invariant!`,
/// `invariant_except_break!`, `loop_decreases!`) rewritten over the snapshots;
/// every other statement (`loop_ensures!`, `assert!`, `assume!`, code) is
/// returned verbatim. `None` when a head-state macro does not parse as one
/// expression (the whole rewrite is then refused).
fn rewrite_head_spec_stmt(stmt: &Stmt, subst: &BTreeMap<String, Expr>) -> Option<Stmt> {
    let (mac, semi) = match stmt {
        Stmt::Macro(stmt_macro) => (&stmt_macro.mac, stmt_macro.semi_token),
        Stmt::Expr(Expr::Macro(expr_macro), semi) => (&expr_macro.mac, *semi),
        _ => return Some(stmt.clone()),
    };
    let name = mac.path.segments.last()?.ident.to_string();
    if !matches!(
        name.as_str(),
        "invariant" | "invariant_except_break" | "loop_decreases"
    ) {
        return Some(stmt.clone());
    }
    let parsed: Expr = syn::parse2(mac.tokens.clone()).ok()?;
    let rewritten = substitute_paths(&parsed, subst);
    let mut mac = mac.clone();
    mac.tokens = quote::quote!(#rewritten);
    let expr = Expr::Macro(syn::ExprMacro {
        attrs: Vec::new(),
        mac,
    });
    Some(Stmt::Expr(expr, semi.or_else(|| Some(Default::default()))))
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::ToTokens;

    fn rewrite(src: &str) -> Option<String> {
        let func: ItemFn = syn::parse_str(src).expect("parse");
        desugar_while_guard_blocks(&func).map(|f| f.into_token_stream().to_string())
    }

    #[test]
    fn rotates_flat_side_effect_guard() {
        let out = rewrite(
            "fn f(mut i: u64, mut x: u64) { while { x = x + 1u64; i < 10u64 } { trust_vc::invariant!(x == i); i = i + 1u64; } }",
        )
        .expect("rewritten");
        assert!(out.contains("let mut x__pre_guard = x ;"), "{out}");
        assert!(out.contains("while i < 10u64"), "{out}");
        assert!(
            out.contains("invariant ! (x == (x__pre_guard) + 1u64)"),
            "{out}"
        );
        assert!(out.contains("invariant ! ((x__pre_guard) == i)"), "{out}");
        assert!(
            out.ends_with("x__pre_guard = x ; x = x + 1u64 ; } } }"),
            "{out}"
        );
    }

    #[test]
    fn compound_assignment_is_normalized_and_composed() {
        let out = rewrite("fn f(mut x: u64) { while { x += 2u64; x = x * 2u64; x < 10u64 } { } }")
            .expect("rewritten");
        assert!(
            out.contains("invariant ! (x == ((x__pre_guard) + (2u64)) * 2u64)"),
            "{out}"
        );
    }

    #[test]
    fn loop_ensures_is_kept_over_the_exit_state() {
        let out = rewrite(
            "fn f(mut x: u64) { while { x = x + 1u64; x < 10u64 } { trust_vc::loop_ensures!(x == 10u64); } }",
        )
        .expect("rewritten");
        assert!(out.contains("loop_ensures ! (x == 10u64)"), "{out}");
    }

    #[test]
    fn hoists_if_guard_block_statements() {
        let out = rewrite(
            "fn f() -> u64 { let mut x = 0u64; if { x += 1u64; x == 1u64 } { 1u64 } else { 2u64 } }",
        )
        .expect("rewritten");
        assert!(
            out.contains("let mut x = 0u64 ; x += 1u64 ; if x == 1u64 { 1u64 } else { 2u64 } }"),
            "{out}"
        );
        assert!(
            rewrite("fn f() -> u64 { let mut x = 0u64; if { let y = 1u64; x += y; x == 1u64 } { 1u64 } else { 2u64 } }")
                .is_none(),
            "a guard block that binds a name is left alone"
        );
        assert!(
            rewrite("fn f(x: u64) -> u64 { if { x == 1u64 } { 1u64 } else { 2u64 } }").is_none()
        );
    }

    #[test]
    fn refuses_continue_call_let_and_shadow() {
        assert!(
            rewrite("fn f(mut x: u64) { while { x = x + 1u64; x < 10u64 } { continue; } }")
                .is_none()
        );
        assert!(rewrite("fn f(mut x: u64) { while { x = g(x); x < 10u64 } { } }").is_none());
        assert!(
            rewrite("fn f(mut x: u64) { while { let t = x; x = t; x < 10u64 } { } }").is_none()
        );
        assert!(rewrite(
            "fn f(mut x: u64) { while { x = x + 1u64; x < 10u64 } { let x = 0u64; } }"
        )
        .is_none());
        assert!(rewrite("fn f(mut x: u64) { while { x = x + 1u64; g(x) } { } }").is_none());
        assert!(rewrite("fn f(mut x: u64) { while x < 10u64 { x = x + 1u64; } }").is_none());
    }
}
