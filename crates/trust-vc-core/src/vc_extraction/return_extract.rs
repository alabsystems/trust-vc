// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::BTreeSet;
use syn::{
    visit::{self, Visit},
    Block, Expr, ExprAsync, ExprBinary, ExprClosure, ExprField, ExprForLoop, ExprLoop, ExprMatch,
    ExprTuple, ExprWhile, Item, Local, Member, Pat, Stmt,
};

/// Conservative classification of a function body's return flow.
pub(super) enum ReturnExtraction<'a> {
    Single(ReturnValue<'a>),
    Multiple(Vec<ReturnValue<'a>>),
    Missing,
    Ambiguous(&'static str),
}

#[derive(Clone, Copy)]
pub(super) enum ReturnValue<'a> {
    Expr(&'a Expr),
    Unit,
    Conditional {
        /// The `let PAT = SCRUTINEE else { return … };` statement itself, always
        /// the second-to-last statement of the enclosing block (see
        /// [`tail_let_else_return`]). Carried so the renderer can hand the WHOLE
        /// local to the obligation collector's own let-else handler, which
        /// resolves the scrutinee's datatype and derives the match condition
        /// there — rather than re-deriving it from `pattern` alone, which cannot
        /// see the type and so cannot tell a refutable pattern from an
        /// irrefutable one.
        local: &'a Local,
        scrutinee: &'a Expr,
        then_value: &'a Expr,
        else_value: &'a Expr,
    },
}

/// Finds one or more canonical return expressions or rejects unsupported control flow.
///
/// `params` is the set of the function's parameter identifiers. It is consulted
/// only when admitting a loop-invariant `return X` from inside a
/// `loop`/`while`/`for` (see [`loop_invariant_return_values`]); the returned
/// `ReturnValue` borrows never point into `params`, so it may have any lifetime.
pub(super) fn classify_return_expression<'a>(
    block: &'a Block,
    allow_unit_bare_return: bool,
    params: &BTreeSet<String>,
) -> ReturnExtraction<'a> {
    let mut top_level_return_value = None;
    let mut top_level_return_count = 0usize;
    let tail_local_initializer = tail_local_initializer(block);
    let tail_let_else = tail_let_else_return(block);
    let mut nested_returns = NestedReturnScan::new(
        allow_unit_bare_return,
        tail_local_initializer
            .as_ref()
            .map(|initializer| initializer.local),
        tail_let_else.as_ref().map(|let_else| let_else.local),
        params,
    );

    for stmt in &block.stmts {
        match stmt {
            Stmt::Expr(Expr::Return(ret_expr), _) => {
                top_level_return_count += 1;
                if top_level_return_count == 1 {
                    top_level_return_value = match ret_expr.expr.as_deref() {
                        Some(expr) => Some(ReturnValue::Expr(expr)),
                        None if allow_unit_bare_return => Some(ReturnValue::Unit),
                        None => {
                            nested_returns.unsupported = Some("explicit return without value");
                            None
                        }
                    };
                }
                if ret_expr
                    .expr
                    .as_deref()
                    .is_some_and(contains_explicit_return_expr)
                {
                    nested_returns.unsupported = Some("nested explicit return in return value");
                }
            }
            _ => nested_returns.scan_stmt(stmt),
        }
    }

    if let Some(reason) = nested_returns.unsupported {
        return ReturnExtraction::Ambiguous(reason);
    }

    // A statement-level `return` unconditionally diverges, so the FIRST top-level
    // return dominates the block: it is the sole reachable return value and every
    // later statement (including further top-level `return`s) is dead code. This is
    // PRECISE, not an over-approximation. A reachable *nested* return that could run
    // before it is still caught by the `nested_returns.values` guard below (kept
    // fail-closed), so relaxing `> 1` to `>= 1` here only lifts the pure
    // multiple-top-level-returns conservatism guard — never a soundness guard.
    if top_level_return_count >= 1 {
        if !nested_returns.values.is_empty() {
            return ReturnExtraction::Ambiguous(
                "nested explicit return path after top-level return",
            );
        }
        return match top_level_return_value {
            Some(value) => ReturnExtraction::Single(value),
            None => ReturnExtraction::Missing,
        };
    }

    if !nested_returns.values.is_empty() {
        if tail_let_else.is_some() {
            return ReturnExtraction::Ambiguous(
                "let-else explicit return path with other nested returns",
            );
        }
        if let Some(Stmt::Expr(tail_expr, None)) = block.stmts.last() {
            if contains_explicit_return_expr(tail_expr) {
                if !is_return_only_tail_expr(tail_expr, allow_unit_bare_return) {
                    let Some(normal_values) =
                        expression_context_normal_return_values(tail_expr, allow_unit_bare_return)
                    else {
                        return ReturnExtraction::Ambiguous(
                            "nested explicit return in tail expression",
                        );
                    };
                    // Add unguarded normal-completion values only. This may
                    // admit infeasible paths, but it avoids unsoundly relying
                    // on branch-sensitive assumptions.
                    nested_returns.values.extend(normal_values);
                }
            } else if let Some(initializer) = &tail_local_initializer {
                let Some(normal_values) =
                    normal_completion_values(initializer.init_expr, allow_unit_bare_return)
                else {
                    return ReturnExtraction::Ambiguous(
                        "nested explicit return in local initializer",
                    );
                };
                nested_returns.values.extend(normal_values);
            } else {
                nested_returns.values.push(ReturnValue::Expr(tail_expr));
            }
        } else if allow_unit_bare_return {
            nested_returns.values.push(ReturnValue::Unit);
        } else {
            return ReturnExtraction::Ambiguous(
                "nested explicit return path without tail expression",
            );
        }

        if nested_returns
            .values
            .iter()
            .any(|value| value.contains_call_expr())
        {
            return ReturnExtraction::Ambiguous(
                "nested explicit return value with call expression",
            );
        }
        return if nested_returns.values.len() == 1 {
            ReturnExtraction::Single(nested_returns.values[0])
        } else {
            ReturnExtraction::Multiple(nested_returns.values)
        };
    }

    if let Some(let_else) = tail_let_else {
        return ReturnExtraction::Single(ReturnValue::Conditional {
            local: let_else.local,
            scrutinee: let_else.scrutinee,
            then_value: let_else.tail_expr,
            else_value: let_else.else_value,
        });
    }

    match block.stmts.last() {
        Some(Stmt::Expr(expr, None)) => ReturnExtraction::Single(ReturnValue::Expr(expr)),
        _ if allow_unit_bare_return => ReturnExtraction::Single(ReturnValue::Unit),
        _ => ReturnExtraction::Missing,
    }
}

struct NestedReturnScan<'a> {
    values: Vec<ReturnValue<'a>>,
    unsupported: Option<&'static str>,
    allow_unit_bare_return: bool,
    supported_local_initializer: Option<&'a Local>,
    supported_let_else_local: Option<&'a Local>,
    /// Function parameter identifiers, used only to admit a loop-invariant
    /// `return param` from inside a `loop`/`while`/`for`.
    params: BTreeSet<String>,
}

impl<'a> NestedReturnScan<'a> {
    fn new(
        allow_unit_bare_return: bool,
        supported_local_initializer: Option<&'a Local>,
        supported_let_else_local: Option<&'a Local>,
        params: &BTreeSet<String>,
    ) -> Self {
        Self {
            values: Vec::new(),
            unsupported: None,
            allow_unit_bare_return,
            supported_local_initializer,
            supported_let_else_local,
            params: params.clone(),
        }
    }

    fn scan_stmt(&mut self, stmt: &'a Stmt) {
        if self.unsupported.is_some() {
            return;
        }
        match stmt {
            Stmt::Local(local) => {
                if let Some(init) = local.init.as_ref() {
                    if self
                        .supported_let_else_local
                        .is_some_and(|supported| std::ptr::eq(supported, local))
                    {
                        if contains_explicit_return_expr(&init.expr) {
                            self.unsupported =
                                Some("nested explicit return in let-else initializer");
                        }
                        return;
                    }
                    if self
                        .supported_local_initializer
                        .is_some_and(|supported| std::ptr::eq(supported, local))
                    {
                        if init
                            .diverge
                            .as_ref()
                            .is_some_and(|(_, diverge)| contains_explicit_return_expr(diverge))
                        {
                            self.unsupported = Some("local initializer explicit return path");
                            return;
                        }
                        if contains_explicit_return_expr(&init.expr) {
                            self.scan_expr(&init.expr);
                        }
                        return;
                    }
                    if contains_explicit_return_expr(&init.expr)
                        || init
                            .diverge
                            .as_ref()
                            .is_some_and(|(_, diverge)| contains_explicit_return_expr(diverge))
                    {
                        self.unsupported = Some("local initializer explicit return path");
                    }
                }
            }
            Stmt::Expr(expr, _) => self.scan_expr(expr),
            Stmt::Macro(_) | Stmt::Item(_) => {}
        }
    }

    fn scan_block(&mut self, block: &'a Block) {
        for stmt in &block.stmts {
            self.scan_stmt(stmt);
            if self.unsupported.is_some() {
                break;
            }
        }
    }

    fn scan_expr(&mut self, expr: &'a Expr) {
        if self.unsupported.is_some() {
            return;
        }
        match expr {
            Expr::Return(ret) => {
                let Some(value) = ret.expr.as_deref() else {
                    if self.allow_unit_bare_return {
                        self.values.push(ReturnValue::Unit);
                    } else {
                        self.unsupported = Some("explicit return without value");
                    }
                    return;
                };
                if contains_explicit_return_expr(value) {
                    self.unsupported = Some("nested explicit return in return value");
                    return;
                }
                self.values.push(ReturnValue::Expr(value));
            }
            Expr::Block(block) => self.scan_block(&block.block),
            Expr::If(expr_if) => {
                if matches!(&*expr_if.cond, Expr::Let(_)) {
                    self.scan_if_let(expr_if);
                    return;
                }
                if contains_explicit_return_expr(&expr_if.cond)
                    && !self.scan_supported_short_circuit_condition(&expr_if.cond)
                {
                    self.unsupported = Some("explicit return in if condition");
                    return;
                }
                self.scan_block(&expr_if.then_branch);
                if let Some((_, else_branch)) = &expr_if.else_branch {
                    self.scan_expr(else_branch);
                }
            }
            Expr::Closure(_) | Expr::Async(_) => {}
            Expr::Loop(_) | Expr::While(_) | Expr::ForLoop(_) => {
                if contains_explicit_return_expr(expr) {
                    // A `loop`/`while`/`for` body is havoc'd across iterations
                    // (the invariant is the only carried fact), so an explicit
                    // `return X` inside it is a sound member of the return
                    // over-approximation ONLY when `X` is provably LOOP-INVARIANT
                    // — a literal constant or an immutable parameter never
                    // written or rebound in the loop. Such an `X` is identical
                    // regardless of the havoc, so `result == X` cannot false-
                    // verify. Admit those into the multiple-return disjunction
                    // (the existing sound over-approximation); fail closed
                    // (unchanged behavior) for any value we cannot prove
                    // loop-invariant.
                    match loop_invariant_return_values(
                        expr,
                        &self.params,
                        self.allow_unit_bare_return,
                    ) {
                        Some(values) => self.values.extend(values),
                        None => self.unsupported = Some("loop explicit return path"),
                    }
                }
            }
            Expr::Match(_) => {
                if contains_explicit_return_expr(expr) {
                    let Expr::Match(expr_match) = expr else {
                        return;
                    };
                    let Some(values) =
                        match_explicit_return_values(expr_match, self.allow_unit_bare_return)
                    else {
                        self.unsupported = Some("match explicit return path");
                        return;
                    };
                    self.values.extend(values);
                }
            }
            Expr::Field(field) if tuple_field_projection(field).is_some() => {
                let Some((tuple, _)) = tuple_field_projection(field) else {
                    return;
                };
                for elem in &tuple.elems {
                    self.scan_expr(elem);
                    if self.unsupported.is_some() {
                        break;
                    }
                }
            }
            _ => {
                if contains_explicit_return_expr(expr) {
                    self.unsupported = Some("unsupported nested explicit return path");
                }
            }
        }
    }

    fn scan_supported_short_circuit_condition(&mut self, expr: &'a Expr) -> bool {
        let Some(binary) = supported_short_circuit_condition(expr, self.allow_unit_bare_return)
        else {
            return false;
        };
        self.scan_expr(&binary.right);
        self.unsupported.is_none()
    }

    fn scan_if_let(&mut self, expr_if: &'a syn::ExprIf) {
        let Expr::Let(expr_let) = &*expr_if.cond else {
            return;
        };
        if contains_explicit_return_expr(&expr_let.expr) {
            self.unsupported = Some("explicit return in if-let condition");
            return;
        }
        if pattern_binds_names(&expr_let.pat) {
            if expr_if
                .then_branch
                .stmts
                .iter()
                .any(contains_explicit_return_stmt)
                || expr_if
                    .else_branch
                    .as_ref()
                    .is_some_and(|(_, else_branch)| contains_explicit_return_expr(else_branch))
            {
                self.unsupported = Some("if-let explicit return path");
            }
            return;
        }
        self.scan_block(&expr_if.then_branch);
        if let Some((_, else_branch)) = &expr_if.else_branch {
            self.scan_expr(else_branch);
        }
    }
}

/// Attempts to admit the explicit `return`s inside a `loop`/`while`/`for`
/// (`loop_expr`) by proving each returned value is LOOP-INVARIANT. Returns
/// `Some(values)` with the loop-invariant return values to feed the
/// multiple-return disjunction, or `None` when ANY returned value cannot be
/// proven loop-invariant (fail closed — the caller stays `Ambiguous`).
///
/// SOUNDNESS: a loop body is havoc'd — the invariant is the only fact carried
/// across iterations — so a `return X` whose `X` reads havoc'd (loop-mutated)
/// state has an INDETERMINATE value. Adding `result == X` to the return
/// disjunction would let a postcondition false-verify for the one havoc'd value
/// the solver happens to pick. Restricting `X` to a literal constant or a
/// parameter that is neither written (`x = ..`, `x += ..`, `&mut x`) nor rebound
/// anywhere in the loop guarantees `X` is identical regardless of the havoc, so
/// `result == X` is a sound member of the over-approximation.
fn loop_invariant_return_values<'a>(
    loop_expr: &'a Expr,
    params: &BTreeSet<String>,
    allow_unit_bare_return: bool,
) -> Option<Vec<ReturnValue<'a>>> {
    // Every explicit `return` reachable inside the loop, excluding those that
    // belong to a nested closure / async block / item (a different return scope).
    let mut collector = LoopReturnCollector::default();
    collector.visit_expr(loop_expr);

    // Identifiers assigned, compound-assigned, `&mut`-borrowed, or rebound
    // (pattern-bound: `let`, the for-loop variable, a closure parameter, a
    // match/if-let binding) ANYWHERE in the loop. Any such name is NOT
    // loop-invariant. Over-approximation here is safe — it only rejects more.
    let mut mutated_or_bound = LoopMutatedOrBoundIdents::default();
    mutated_or_bound.visit_expr(loop_expr);

    let mut values = Vec::new();
    for ret in collector.returns {
        match ret.expr.as_deref() {
            None => {
                // Bare `return;`. Unit is a constant → loop-invariant when unit
                // returns are admitted for this body; otherwise fail closed.
                if allow_unit_bare_return {
                    values.push(ReturnValue::Unit);
                } else {
                    return None;
                }
            }
            Some(value) => {
                // A nested explicit return in the value, or any value not
                // provably loop-invariant, fails the whole loop closed.
                if contains_explicit_return_expr(value)
                    || !is_loop_invariant_value(value, &mutated_or_bound.idents, params)
                {
                    return None;
                }
                values.push(ReturnValue::Expr(value));
            }
        }
    }
    Some(values)
}

/// Returns `true` when `expr`'s value is provably identical on every iteration
/// of the enclosing loop: a literal constant; an immutable parameter that is
/// never written or rebound inside the loop (`loop_mutated_or_bound`); or a pure
/// composition (unary neg/not, non-assign binary, cast, paren/group) of such
/// values. Anything else — reads of loop-mutated locals, loop variables, calls,
/// method calls, indexing, field access, unknown idents — is not provably
/// loop-invariant and yields `false` (fail closed).
fn is_loop_invariant_value(
    expr: &Expr,
    loop_mutated_or_bound: &BTreeSet<String>,
    params: &BTreeSet<String>,
) -> bool {
    match strip_group_paren_expr(expr) {
        Expr::Lit(_) => true,
        Expr::Path(path) => {
            // A single-segment path to a function parameter that is neither
            // written/`&mut`-borrowed nor rebound (shadowed) anywhere in the
            // loop reads its stable pre-loop value on every iteration, so the
            // loop's havoc cannot change it.
            if path.qself.is_some() || path.path.segments.len() != 1 {
                return false;
            }
            let name = path.path.segments[0].ident.to_string();
            params.contains(&name) && !loop_mutated_or_bound.contains(&name)
        }
        Expr::Unary(unary) if matches!(unary.op, syn::UnOp::Neg(_) | syn::UnOp::Not(_)) => {
            is_loop_invariant_value(&unary.expr, loop_mutated_or_bound, params)
        }
        Expr::Binary(binary) if !is_compound_assign_binop(&binary.op) => {
            is_loop_invariant_value(&binary.left, loop_mutated_or_bound, params)
                && is_loop_invariant_value(&binary.right, loop_mutated_or_bound, params)
        }
        Expr::Cast(cast) => is_loop_invariant_value(&cast.expr, loop_mutated_or_bound, params),
        _ => false,
    }
}

/// True for the in-place compound-assignment binary operators (`+=`, `-=`, …),
/// which in syn 2.x are `Expr::Binary` nodes rather than a distinct node kind.
fn is_compound_assign_binop(op: &syn::BinOp) -> bool {
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

/// Inserts every single-segment path identifier appearing in `expr` into `out`.
/// Used to over-approximate the base name(s) of an assignment / `&mut` target.
fn collect_path_idents(expr: &Expr, out: &mut BTreeSet<String>) {
    struct Collector<'a>(&'a mut BTreeSet<String>);
    impl<'ast> Visit<'ast> for Collector<'_> {
        fn visit_expr_path(&mut self, node: &'ast syn::ExprPath) {
            if node.qself.is_none() && node.path.segments.len() == 1 {
                self.0.insert(node.path.segments[0].ident.to_string());
            }
            visit::visit_expr_path(self, node);
        }
    }
    Collector(out).visit_expr(expr);
}

/// Collects every explicit `return` inside a loop, excluding those nested inside
/// a closure / async block / item (which belong to a different return scope).
/// The return VALUE is not descended into: it is inspected separately for
/// loop-invariance and nested returns by [`loop_invariant_return_values`].
#[derive(Default)]
struct LoopReturnCollector<'ast> {
    returns: Vec<&'ast syn::ExprReturn>,
}

impl<'ast> Visit<'ast> for LoopReturnCollector<'ast> {
    fn visit_expr_return(&mut self, node: &'ast syn::ExprReturn) {
        self.returns.push(node);
    }

    fn visit_expr_closure(&mut self, _node: &'ast ExprClosure) {}
    fn visit_expr_async(&mut self, _node: &'ast ExprAsync) {}
    fn visit_item(&mut self, _node: &'ast Item) {}
}

/// Collects identifiers that are assigned, compound-assigned, `&mut`-borrowed, or
/// pattern-bound, or the receiver of a method call anywhere within a loop — i.e.
/// names whose value is NOT provably loop-invariant. Descent is deliberately
/// unrestricted (including into nested closures) because that only widens the
/// set, which is the safe direction.
#[derive(Default)]
struct LoopMutatedOrBoundIdents {
    idents: BTreeSet<String>,
}

impl<'ast> Visit<'ast> for LoopMutatedOrBoundIdents {
    fn visit_expr_assign(&mut self, node: &'ast syn::ExprAssign) {
        collect_path_idents(&node.left, &mut self.idents);
        visit::visit_expr_assign(self, node);
    }

    fn visit_expr_binary(&mut self, node: &'ast ExprBinary) {
        if is_compound_assign_binop(&node.op) {
            collect_path_idents(&node.left, &mut self.idents);
        }
        visit::visit_expr_binary(self, node);
    }

    fn visit_expr_reference(&mut self, node: &'ast syn::ExprReference) {
        if node.mutability.is_some() {
            collect_path_idents(&node.expr, &mut self.idents);
        }
        visit::visit_expr_reference(self, node);
    }

    fn visit_expr_method_call(&mut self, node: &'ast syn::ExprMethodCall) {
        // A `&mut self` method mutates its receiver in place, and the classifier
        // has no type information to distinguish it from a `&self` reader. Treat
        // every method-call receiver as potentially mutated (over-approximation
        // — the safe direction), so `return receiver` from inside the loop fails
        // closed rather than admitting a value the method may have changed.
        collect_path_idents(&node.receiver, &mut self.idents);
        visit::visit_expr_method_call(self, node);
    }

    fn visit_pat_ident(&mut self, node: &'ast syn::PatIdent) {
        self.idents.insert(node.ident.to_string());
        visit::visit_pat_ident(self, node);
    }
}

struct TailLocalInitializer<'a> {
    local: &'a Local,
    init_expr: &'a Expr,
}

struct TailLetElseReturn<'a> {
    local: &'a Local,
    scrutinee: &'a Expr,
    else_value: &'a Expr,
    tail_expr: &'a Expr,
}

fn tail_local_initializer(block: &Block) -> Option<TailLocalInitializer<'_>> {
    let [.., Stmt::Local(local), Stmt::Expr(tail_expr, None)] = block.stmts.as_slice() else {
        return None;
    };
    let tail_name = expr_path_ident_name(tail_expr)?;
    let local_name = local_pat_ident_name(&local.pat)?;
    if tail_name != local_name {
        return None;
    }
    let init = local.init.as_ref()?;
    if init
        .diverge
        .as_ref()
        .is_some_and(|(_, diverge)| contains_explicit_return_expr(diverge))
    {
        return None;
    }
    contains_explicit_return_expr(&init.expr).then_some(TailLocalInitializer {
        local,
        init_expr: &init.expr,
    })
}

fn tail_let_else_return(block: &Block) -> Option<TailLetElseReturn<'_>> {
    let [.., Stmt::Local(local), Stmt::Expr(tail_expr, None)] = block.stmts.as_slice() else {
        return None;
    };
    let init = local.init.as_ref()?;
    let (_, diverge) = init.diverge.as_ref()?;
    let else_value = single_tail_return_expr(diverge)?;
    if contains_explicit_return_expr(&init.expr) || contains_explicit_return_expr(tail_expr) {
        return None;
    }
    Some(TailLetElseReturn {
        local,
        scrutinee: &init.expr,
        else_value,
        tail_expr,
    })
}

fn single_tail_return_expr(expr: &Expr) -> Option<&Expr> {
    match expr {
        Expr::Return(ret) => {
            let value = ret.expr.as_deref()?;
            (!contains_explicit_return_expr(value)).then_some(value)
        }
        Expr::Block(block) => {
            let Some(Stmt::Expr(Expr::Return(ret), _)) = block.block.stmts.last() else {
                return None;
            };
            let value = ret.expr.as_deref()?;
            if block
                .block
                .stmts
                .iter()
                .take(block.block.stmts.len().saturating_sub(1))
                .any(contains_explicit_return_stmt)
                || contains_explicit_return_expr(value)
            {
                return None;
            }
            Some(value)
        }
        Expr::Group(group) => single_tail_return_expr(&group.expr),
        Expr::Paren(paren) => single_tail_return_expr(&paren.expr),
        _ => None,
    }
}

fn expr_path_ident_name(expr: &Expr) -> Option<String> {
    let Expr::Path(path) = strip_group_paren_expr(expr) else {
        return None;
    };
    if path.qself.is_some() || path.path.segments.len() != 1 {
        return None;
    }
    Some(path.path.segments[0].ident.to_string())
}

fn local_pat_ident_name(pat: &Pat) -> Option<String> {
    match pat {
        Pat::Ident(ident) => Some(ident.ident.to_string()),
        Pat::Type(typed) => local_pat_ident_name(&typed.pat),
        Pat::Paren(paren) => local_pat_ident_name(&paren.pat),
        _ => None,
    }
}

fn pattern_binds_names(pat: &Pat) -> bool {
    match pat {
        Pat::Ident(_) => true,
        Pat::Or(pat_or) => pat_or.cases.iter().any(pattern_binds_names),
        Pat::Paren(paren) => pattern_binds_names(&paren.pat),
        Pat::Reference(reference) => pattern_binds_names(&reference.pat),
        Pat::Slice(slice) => slice.elems.iter().any(pattern_binds_names),
        Pat::Struct(strukt) => strukt
            .fields
            .iter()
            .any(|field| pattern_binds_names(&field.pat)),
        Pat::Tuple(tuple) => tuple.elems.iter().any(pattern_binds_names),
        Pat::TupleStruct(tuple_struct) => tuple_struct.elems.iter().any(pattern_binds_names),
        Pat::Type(pat_type) => pattern_binds_names(&pat_type.pat),
        _ => false,
    }
}

fn supported_no_binding_if_let(expr_if: &syn::ExprIf) -> Option<()> {
    let Expr::Let(expr_let) = &*expr_if.cond else {
        return None;
    };
    if pattern_binds_names(&expr_let.pat) || contains_explicit_return_expr(&expr_let.expr) {
        return None;
    }
    Some(())
}

impl ReturnValue<'_> {
    fn contains_call_expr(self) -> bool {
        match self {
            ReturnValue::Expr(expr) => contains_call_expr(expr),
            ReturnValue::Conditional {
                scrutinee,
                then_value,
                else_value,
                ..
            } => {
                contains_call_expr(scrutinee)
                    || contains_call_expr(then_value)
                    || contains_call_expr(else_value)
            }
            ReturnValue::Unit => false,
        }
    }
}

fn expression_context_normal_return_values<'a>(
    expr: &'a Expr,
    allow_unit_bare_return: bool,
) -> Option<Vec<ReturnValue<'a>>> {
    match expr {
        Expr::Field(field) => tuple_field_normal_return_values(field, allow_unit_bare_return),
        Expr::If(expr_if)
            if short_circuit_condition_normal_truth_values(
                &expr_if.cond,
                allow_unit_bare_return,
            )
            .is_some() =>
        {
            normal_completion_values(expr, allow_unit_bare_return)
        }
        Expr::If(expr_if)
            if !matches!(&*expr_if.cond, Expr::Let(_))
                && !contains_explicit_return_expr(&expr_if.cond) =>
        {
            normal_completion_values(expr, allow_unit_bare_return)
        }
        Expr::If(expr_if) if supported_no_binding_if_let(expr_if).is_some() => {
            normal_completion_values(expr, allow_unit_bare_return)
        }
        Expr::Block(_) => normal_completion_values(expr, allow_unit_bare_return),
        Expr::Match(_) => normal_completion_values(expr, allow_unit_bare_return),
        Expr::Group(group) => {
            expression_context_normal_return_values(&group.expr, allow_unit_bare_return)
        }
        Expr::Paren(paren) => {
            expression_context_normal_return_values(&paren.expr, allow_unit_bare_return)
        }
        _ => None,
    }
}

fn tuple_field_normal_return_values<'a>(
    field: &'a ExprField,
    allow_unit_bare_return: bool,
) -> Option<Vec<ReturnValue<'a>>> {
    let (tuple, selected_index) = tuple_field_projection(field)?;
    let selected = tuple.elems.iter().nth(selected_index)?;
    normal_completion_values(selected, allow_unit_bare_return)
}

fn normal_completion_values<'a>(
    expr: &'a Expr,
    allow_unit_bare_return: bool,
) -> Option<Vec<ReturnValue<'a>>> {
    if !contains_explicit_return_expr(expr) {
        return Some(vec![ReturnValue::Expr(expr)]);
    }

    match expr {
        Expr::Return(_) => Some(Vec::new()),
        Expr::Block(block) => {
            normal_completion_values_from_block(&block.block, allow_unit_bare_return)
        }
        Expr::Group(group) => normal_completion_values(&group.expr, allow_unit_bare_return),
        Expr::If(expr_if) => {
            if let Some(normal_truth_values) =
                short_circuit_condition_normal_truth_values(&expr_if.cond, allow_unit_bare_return)
            {
                let mut values = Vec::new();
                if normal_truth_values.contains(&true) {
                    values.extend(normal_completion_values_from_block(
                        &expr_if.then_branch,
                        allow_unit_bare_return,
                    )?);
                }
                if normal_truth_values.contains(&false) {
                    if let Some((_, else_branch)) = &expr_if.else_branch {
                        values.extend(normal_completion_values(
                            else_branch,
                            allow_unit_bare_return,
                        )?);
                    } else if allow_unit_bare_return {
                        values.push(ReturnValue::Unit);
                    } else {
                        return None;
                    }
                }
                Some(values)
            } else {
                if let Expr::Let(expr_let) = &*expr_if.cond {
                    if pattern_binds_names(&expr_let.pat)
                        || contains_explicit_return_expr(&expr_let.expr)
                    {
                        return None;
                    }
                } else if contains_explicit_return_expr(&expr_if.cond) {
                    return None;
                }

                let mut values = normal_completion_values_from_block(
                    &expr_if.then_branch,
                    allow_unit_bare_return,
                )?;
                if let Some((_, else_branch)) = &expr_if.else_branch {
                    values.extend(normal_completion_values(
                        else_branch,
                        allow_unit_bare_return,
                    )?);
                } else if allow_unit_bare_return {
                    values.push(ReturnValue::Unit);
                } else {
                    return None;
                }
                Some(values)
            }
        }
        Expr::Match(expr_match) => match_normal_return_values(expr_match, allow_unit_bare_return),
        Expr::Paren(paren) => normal_completion_values(&paren.expr, allow_unit_bare_return),
        _ => None,
    }
}

fn match_explicit_return_values<'a>(
    expr_match: &'a ExprMatch,
    allow_unit_bare_return: bool,
) -> Option<Vec<ReturnValue<'a>>> {
    supported_match_return_shape(expr_match)?;
    let mut values = Vec::new();
    for arm in &expr_match.arms {
        if !contains_explicit_return_expr(&arm.body) {
            continue;
        }
        values.push(match_direct_return_value(
            &arm.body,
            allow_unit_bare_return,
        )?);
    }
    Some(values)
}

fn match_normal_return_values<'a>(
    expr_match: &'a ExprMatch,
    allow_unit_bare_return: bool,
) -> Option<Vec<ReturnValue<'a>>> {
    supported_match_return_shape(expr_match)?;
    let mut values = Vec::new();
    for arm in &expr_match.arms {
        if contains_explicit_return_expr(&arm.body) {
            match_direct_return_value(&arm.body, allow_unit_bare_return)?;
            continue;
        }
        if !contains_path_expr(&arm.body) {
            values.push(ReturnValue::Expr(&arm.body));
        } else {
            return None;
        }
    }
    Some(values)
}

fn supported_match_return_shape(expr_match: &ExprMatch) -> Option<()> {
    if contains_explicit_return_expr(&expr_match.expr) {
        return None;
    }
    for arm in &expr_match.arms {
        if arm.guard.is_some() || pattern_binds_names(&arm.pat) {
            return None;
        }
    }
    Some(())
}

fn match_direct_return_value<'a>(
    expr: &'a Expr,
    allow_unit_bare_return: bool,
) -> Option<ReturnValue<'a>> {
    match expr {
        Expr::Return(ret) => match ret.expr.as_deref() {
            Some(value) if !contains_explicit_return_expr(value) && !contains_path_expr(value) => {
                Some(ReturnValue::Expr(value))
            }
            Some(_) => None,
            None if allow_unit_bare_return => Some(ReturnValue::Unit),
            None => None,
        },
        Expr::Block(block) => {
            let Some(Stmt::Expr(tail_expr, _)) = block.block.stmts.last() else {
                return None;
            };
            if block
                .block
                .stmts
                .iter()
                .take(block.block.stmts.len().saturating_sub(1))
                .any(contains_explicit_return_stmt)
            {
                return None;
            }
            match_direct_return_value(tail_expr, allow_unit_bare_return)
        }
        Expr::Group(group) => match_direct_return_value(&group.expr, allow_unit_bare_return),
        Expr::Paren(paren) => match_direct_return_value(&paren.expr, allow_unit_bare_return),
        _ => None,
    }
}

fn short_circuit_condition_normal_truth_values(
    expr: &Expr,
    allow_unit_bare_return: bool,
) -> Option<Vec<bool>> {
    let binary = supported_short_circuit_condition(expr, allow_unit_bare_return)?;
    match &binary.op {
        syn::BinOp::Or(_) => Some(vec![true]),
        syn::BinOp::And(_) => Some(vec![false]),
        _ => None,
    }
}

fn supported_short_circuit_condition(
    expr: &Expr,
    allow_unit_bare_return: bool,
) -> Option<&ExprBinary> {
    match strip_group_paren_expr(expr) {
        Expr::Binary(binary)
            if matches!(&binary.op, syn::BinOp::Or(_) | syn::BinOp::And(_))
                && !contains_explicit_return_expr(&binary.left)
                && expression_has_no_normal_completion_due_to_return(
                    &binary.right,
                    allow_unit_bare_return,
                ) =>
        {
            Some(binary)
        }
        _ => None,
    }
}

fn expression_has_no_normal_completion_due_to_return(
    expr: &Expr,
    allow_unit_bare_return: bool,
) -> bool {
    contains_explicit_return_expr(expr)
        && matches!(
            normal_completion_values(expr, allow_unit_bare_return),
            Some(values) if values.is_empty()
        )
}

fn normal_completion_values_from_block<'a>(
    block: &'a Block,
    allow_unit_bare_return: bool,
) -> Option<Vec<ReturnValue<'a>>> {
    match block.stmts.last() {
        Some(Stmt::Expr(Expr::Return(_), _)) => Some(Vec::new()),
        Some(Stmt::Expr(expr, None)) => normal_completion_values(expr, allow_unit_bare_return),
        _ if allow_unit_bare_return => Some(vec![ReturnValue::Unit]),
        _ => None,
    }
}

fn tuple_field_projection(field: &ExprField) -> Option<(&ExprTuple, usize)> {
    let Expr::Tuple(tuple) = strip_group_paren_expr(&field.base) else {
        return None;
    };
    let Member::Unnamed(index) = &field.member else {
        return None;
    };
    let index = index.index as usize;
    (index < tuple.elems.len()).then_some((tuple, index))
}

fn strip_group_paren_expr(expr: &Expr) -> &Expr {
    match expr {
        Expr::Group(group) => strip_group_paren_expr(&group.expr),
        Expr::Paren(paren) => strip_group_paren_expr(&paren.expr),
        _ => expr,
    }
}

fn is_return_only_tail_expr(expr: &Expr, allow_unit_bare_return: bool) -> bool {
    match expr {
        Expr::Return(ret) => ret
            .expr
            .as_deref()
            .map(|value| !contains_explicit_return_expr(value))
            .unwrap_or(allow_unit_bare_return),
        Expr::Block(block) => is_return_only_block(&block.block, allow_unit_bare_return),
        Expr::Group(group) => is_return_only_tail_expr(&group.expr, allow_unit_bare_return),
        Expr::Paren(paren) => is_return_only_tail_expr(&paren.expr, allow_unit_bare_return),
        Expr::If(expr_if) => {
            if contains_explicit_return_expr(&expr_if.cond)
                || matches!(&*expr_if.cond, Expr::Let(_))
            {
                return false;
            }

            is_return_only_block(&expr_if.then_branch, allow_unit_bare_return)
                && expr_if
                    .else_branch
                    .as_ref()
                    .map(|(_, else_branch)| {
                        is_return_only_tail_expr(else_branch, allow_unit_bare_return)
                    })
                    .unwrap_or(allow_unit_bare_return)
        }
        _ => false,
    }
}

fn is_return_only_block(block: &Block, allow_unit_bare_return: bool) -> bool {
    block.stmts.last().is_some_and(|stmt| {
        matches!(stmt, Stmt::Expr(expr, _) if is_return_only_tail_expr(expr, allow_unit_bare_return))
    })
}

fn contains_explicit_return_expr(expr: &Expr) -> bool {
    let mut visitor = ExplicitReturnFinder::default();
    visitor.visit_expr(expr);
    visitor.found
}

fn contains_explicit_return_stmt(stmt: &Stmt) -> bool {
    let mut visitor = ExplicitReturnFinder::default();
    visitor.visit_stmt(stmt);
    visitor.found
}

fn contains_call_expr(expr: &Expr) -> bool {
    let mut visitor = CallExprFinder::default();
    visitor.visit_expr(expr);
    visitor.found
}

fn contains_path_expr(expr: &Expr) -> bool {
    let mut visitor = PathExprFinder::default();
    visitor.visit_expr(expr);
    visitor.found
}

#[derive(Default)]
struct ExplicitReturnFinder {
    found: bool,
}

impl<'ast> Visit<'ast> for ExplicitReturnFinder {
    fn visit_expr(&mut self, expr: &'ast Expr) {
        if self.found {
            return;
        }
        visit::visit_expr(self, expr);
    }

    fn visit_expr_return(&mut self, _expr: &'ast syn::ExprReturn) {
        self.found = true;
    }

    fn visit_expr_closure(&mut self, _expr: &'ast ExprClosure) {}

    fn visit_expr_async(&mut self, _expr: &'ast ExprAsync) {}

    fn visit_expr_loop(&mut self, expr: &'ast ExprLoop) {
        visit::visit_expr_loop(self, expr);
    }

    fn visit_expr_while(&mut self, expr: &'ast ExprWhile) {
        visit::visit_expr_while(self, expr);
    }

    fn visit_expr_for_loop(&mut self, expr: &'ast ExprForLoop) {
        visit::visit_expr_for_loop(self, expr);
    }

    fn visit_expr_match(&mut self, expr: &'ast ExprMatch) {
        visit::visit_expr_match(self, expr);
    }

    fn visit_item(&mut self, _item: &'ast Item) {}
}

#[derive(Default)]
struct CallExprFinder {
    found: bool,
}

impl<'ast> Visit<'ast> for CallExprFinder {
    fn visit_expr(&mut self, expr: &'ast Expr) {
        if self.found {
            return;
        }
        visit::visit_expr(self, expr);
    }

    fn visit_expr_call(&mut self, _expr: &'ast syn::ExprCall) {
        self.found = true;
    }

    fn visit_expr_method_call(&mut self, _expr: &'ast syn::ExprMethodCall) {
        self.found = true;
    }

    fn visit_expr_closure(&mut self, _expr: &'ast ExprClosure) {}

    fn visit_expr_async(&mut self, _expr: &'ast ExprAsync) {}

    fn visit_item(&mut self, _item: &'ast Item) {}
}

#[derive(Default)]
struct PathExprFinder {
    found: bool,
}

impl<'ast> Visit<'ast> for PathExprFinder {
    fn visit_expr(&mut self, expr: &'ast Expr) {
        if self.found {
            return;
        }
        visit::visit_expr(self, expr);
    }

    fn visit_expr_path(&mut self, _expr: &'ast syn::ExprPath) {
        self.found = true;
    }

    fn visit_expr_closure(&mut self, _expr: &'ast ExprClosure) {}

    fn visit_expr_async(&mut self, _expr: &'ast ExprAsync) {}

    fn visit_item(&mut self, _item: &'ast Item) {}
}
