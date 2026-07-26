// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Core rewrite logic: block/stmt/expr traversal and BridgeState.

use super::control_flow::{expr_depends_on_symbolic_value, reject_control_flow_dependence};
use super::helpers::{local_binding_name, receiver_ident_name};
use super::prophecy::{
    try_rewrite_prophecy_new, try_rewrite_prophecy_resolve, try_rewrite_prophecy_view,
};
use std::collections::{HashMap, HashSet};
use syn::fold::Fold;
use syn::{BinOp, Block, Expr, Local, Stmt};

#[derive(Clone, Default)]
pub(super) struct BridgeState {
    pub(super) prophecy_locals: HashMap<String, String>,
    pub(super) bridged_locals: HashSet<String>,
    // Prophecy locals already resolved on the current control-flow path. A prophecy
    // may be resolved at most once; resolving twice would assume two equalities over
    // the same symbol (v == a and v == b), a contradiction that vacuously verifies
    // everything. This is branch-scoped for free: rewrite_expr clones BridgeState into
    // each branch body, so resolves in disjoint if/else or match arms do not collide,
    // while two resolves on one linear path share the set.
    pub(super) resolved_prophecies: HashSet<String>,
    pub(super) next_bridge_id_counter: usize,
}

impl BridgeState {
    pub(super) fn shadow_local_name(&mut self, name: &str) {
        self.prophecy_locals.remove(name);
        self.bridged_locals.remove(name);
        // Re-binding the name (incl. a fresh Proph::new()) clears resolvedness so the
        // new prophecy is resolvable again.
        self.resolved_prophecies.remove(name);
    }

    pub(super) fn next_bridge_id(&mut self) -> usize {
        let id = self.next_bridge_id_counter;
        self.next_bridge_id_counter += 1;
        id
    }
}

pub(crate) fn bridge_proof_statements(block: &Block) -> syn::Result<Block> {
    rewrite_block(block, BridgeState::default()).map(|(block, _state)| block)
}

fn rewrite_block(block: &Block, incoming: BridgeState) -> syn::Result<(Block, BridgeState)> {
    let mut state = incoming;
    let mut rewritten_stmts = Vec::with_capacity(block.stmts.len());
    for stmt in &block.stmts {
        rewritten_stmts.extend(rewrite_stmt(stmt, &mut state)?);
    }

    let mut rewritten = block.clone();
    rewritten.stmts = rewritten_stmts;
    Ok((rewritten, state))
}

fn rewrite_stmt(stmt: &Stmt, state: &mut BridgeState) -> syn::Result<Vec<Stmt>> {
    match stmt {
        Stmt::Local(local) => rewrite_local(local, state),
        Stmt::Expr(expr, semi) => {
            if let Some(rewritten) = try_rewrite_prophecy_resolve(expr, state)? {
                return Ok(rewritten);
            }
            Ok(vec![Stmt::Expr(rewrite_expr(expr, state)?, *semi)])
        }
        Stmt::Item(item) => Ok(vec![Stmt::Item(item.clone())]),
        Stmt::Macro(mac) => Ok(vec![Stmt::Macro(mac.clone())]),
    }
}

fn rewrite_local(local: &Local, state: &mut BridgeState) -> syn::Result<Vec<Stmt>> {
    if let Some(rewritten) = try_rewrite_prophecy_new(local, state)? {
        return Ok(rewritten);
    }
    if let Some(rewritten) = try_rewrite_prophecy_view(local, state)? {
        return Ok(rewritten);
    }

    let mut rewritten = local.clone();
    if let Some(init) = rewritten.init.as_mut() {
        if init.diverge.is_some() {
            reject_control_flow_dependence(
                init.expr.as_ref(),
                &state.prophecy_locals,
                &state.bridged_locals,
                "let-else initializer",
            )?;
        }
        *init.expr = rewrite_expr(init.expr.as_ref(), state)?;
        if let Some((_, diverge_expr)) = init.diverge.as_mut() {
            **diverge_expr = rewrite_expr(diverge_expr.as_ref(), state)?;
        }
    }

    if let Some(name) = local_binding_name(local) {
        let init_depends_on_symbolic_value = rewritten.init.as_ref().is_some_and(|init| {
            expr_depends_on_symbolic_value(
                init.expr.as_ref(),
                &state.prophecy_locals,
                &state.bridged_locals,
            )
        });
        state.shadow_local_name(&name);
        if init_depends_on_symbolic_value {
            state.bridged_locals.insert(name);
        }
    }

    Ok(vec![Stmt::Local(rewritten)])
}

fn rewrite_expr(expr: &Expr, state: &mut BridgeState) -> syn::Result<Expr> {
    match expr {
        Expr::Block(expr_block) => {
            let (block, inner_state) = rewrite_block(&expr_block.block, state.clone())?;
            state.next_bridge_id_counter = inner_state.next_bridge_id_counter;
            // A block executes unconditionally, so any prophecy it resolves is resolved
            // on the enclosing path too — propagate so a later resolve is rejected.
            state
                .resolved_prophecies
                .extend(inner_state.resolved_prophecies);
            let mut rewritten = expr_block.clone();
            rewritten.block = block;
            Ok(Expr::Block(rewritten))
        }
        Expr::If(expr_if) => {
            reject_control_flow_dependence(
                expr_if.cond.as_ref(),
                &state.prophecy_locals,
                &state.bridged_locals,
                "if condition",
            )?;

            let (then_block, then_state) = rewrite_block(&expr_if.then_branch, state.clone())?;
            state.next_bridge_id_counter = then_state.next_bridge_id_counter;

            let mut rewritten = expr_if.clone();
            rewritten.then_branch = then_block;
            if let Some((else_token, else_expr)) = &expr_if.else_branch {
                rewritten.else_branch = Some((
                    *else_token,
                    Box::new(rewrite_expr(else_expr.as_ref(), state)?),
                ));
            }
            // Union the then-branch resolutions AFTER the else branch (which mutates
            // `state` directly) so disjoint then/else resolves of the same prophecy are
            // both allowed, but a resolve after the whole `if` is rejected if either
            // branch resolved.
            state
                .resolved_prophecies
                .extend(then_state.resolved_prophecies);
            Ok(Expr::If(rewritten))
        }
        Expr::While(expr_while) => {
            reject_control_flow_dependence(
                expr_while.cond.as_ref(),
                &state.prophecy_locals,
                &state.bridged_locals,
                "while condition",
            )?;

            let (body, inner_state) = rewrite_block(&expr_while.body, state.clone())?;
            state.next_bridge_id_counter = inner_state.next_bridge_id_counter;
            state
                .resolved_prophecies
                .extend(inner_state.resolved_prophecies);

            let mut rewritten = expr_while.clone();
            rewritten.body = body;
            Ok(Expr::While(rewritten))
        }
        Expr::ForLoop(expr_for_loop) => {
            reject_control_flow_dependence(
                expr_for_loop.expr.as_ref(),
                &state.prophecy_locals,
                &state.bridged_locals,
                "for-loop iterator",
            )?;

            let (body, inner_state) = rewrite_block(&expr_for_loop.body, state.clone())?;
            state.next_bridge_id_counter = inner_state.next_bridge_id_counter;
            state
                .resolved_prophecies
                .extend(inner_state.resolved_prophecies);

            let mut rewritten = expr_for_loop.clone();
            rewritten.body = body;
            Ok(Expr::ForLoop(rewritten))
        }
        Expr::Loop(expr_loop) => {
            let (body, inner_state) = rewrite_block(&expr_loop.body, state.clone())?;
            state.next_bridge_id_counter = inner_state.next_bridge_id_counter;
            state
                .resolved_prophecies
                .extend(inner_state.resolved_prophecies);

            let mut rewritten = expr_loop.clone();
            rewritten.body = body;
            Ok(Expr::Loop(rewritten))
        }
        Expr::Match(expr_match) => {
            reject_control_flow_dependence(
                expr_match.expr.as_ref(),
                &state.prophecy_locals,
                &state.bridged_locals,
                "match scrutinee",
            )?;

            let mut rewritten = expr_match.clone();
            let mut next_id = state.next_bridge_id_counter;
            // Each arm starts from a clone of the pre-match state (arms are mutually
            // exclusive, so the same prophecy may be resolved once in each), then their
            // resolutions are unioned into `state` only AFTER the loop so a resolve
            // following the whole match is rejected.
            let mut arms_resolved: HashSet<String> = HashSet::new();
            for arm in &mut rewritten.arms {
                let mut arm_state = state.clone();
                if let Some((guard_token, guard)) = arm.guard.as_ref() {
                    reject_control_flow_dependence(
                        guard.as_ref(),
                        &state.prophecy_locals,
                        &state.bridged_locals,
                        "match guard",
                    )?;
                    let rewritten_guard = rewrite_expr(guard.as_ref(), &mut arm_state)?;
                    arm.guard = Some((*guard_token, Box::new(rewritten_guard)));
                }
                *arm.body = rewrite_expr(arm.body.as_ref(), &mut arm_state)?;
                next_id = next_id.max(arm_state.next_bridge_id_counter);
                arms_resolved.extend(arm_state.resolved_prophecies);
            }
            state.next_bridge_id_counter = next_id;
            state.resolved_prophecies.extend(arms_resolved);
            Ok(Expr::Match(rewritten))
        }
        Expr::Assign(expr_assign) => {
            let mut rewritten = expr_assign.clone();
            rewritten.left = Box::new(rewrite_expr(expr_assign.left.as_ref(), state)?);
            rewritten.right = Box::new(rewrite_expr(expr_assign.right.as_ref(), state)?);
            update_assigned_local_bridge_state(
                rewritten.left.as_ref(),
                rewritten.right.as_ref(),
                state,
                AssignmentKind::Plain,
            );
            Ok(Expr::Assign(rewritten))
        }
        Expr::Binary(expr_binary) if is_compound_assignment_op(&expr_binary.op) => {
            let mut rewritten = expr_binary.clone();
            rewritten.left = Box::new(rewrite_expr(expr_binary.left.as_ref(), state)?);
            rewritten.right = Box::new(rewrite_expr(expr_binary.right.as_ref(), state)?);
            update_assigned_local_bridge_state(
                rewritten.left.as_ref(),
                rewritten.right.as_ref(),
                state,
                AssignmentKind::Compound,
            );
            Ok(Expr::Binary(rewritten))
        }
        _ => rewrite_nested_expr(expr, state),
    }
}

#[derive(Clone, Copy)]
enum AssignmentKind {
    Plain,
    Compound,
}

fn update_assigned_local_bridge_state(
    left: &Expr,
    right: &Expr,
    state: &mut BridgeState,
    assignment_kind: AssignmentKind,
) {
    let Some(name) = receiver_ident_name(left) else {
        return;
    };

    let rhs_depends_on_symbolic_value =
        expr_depends_on_symbolic_value(right, &state.prophecy_locals, &state.bridged_locals);
    let depends_on_symbolic_value = match assignment_kind {
        AssignmentKind::Plain => rhs_depends_on_symbolic_value,
        AssignmentKind::Compound => {
            rhs_depends_on_symbolic_value || state.bridged_locals.contains(&name)
        }
    };

    state.prophecy_locals.remove(&name);
    if depends_on_symbolic_value {
        state.bridged_locals.insert(name);
    } else {
        state.bridged_locals.remove(&name);
    }
}

fn is_compound_assignment_op(op: &BinOp) -> bool {
    matches!(
        op,
        BinOp::AddAssign(_)
            | BinOp::SubAssign(_)
            | BinOp::MulAssign(_)
            | BinOp::DivAssign(_)
            | BinOp::RemAssign(_)
            | BinOp::BitXorAssign(_)
            | BinOp::BitAndAssign(_)
            | BinOp::BitOrAssign(_)
            | BinOp::ShlAssign(_)
            | BinOp::ShrAssign(_)
    )
}

fn rewrite_nested_expr(expr: &Expr, state: &mut BridgeState) -> syn::Result<Expr> {
    let mut folder = NestedExprFolder { state, error: None };
    let rewritten = folder.fold_expr(expr.clone());
    match folder.error {
        Some(err) => Err(err),
        None => Ok(rewritten),
    }
}

struct NestedExprFolder<'a> {
    state: &'a mut BridgeState,
    error: Option<syn::Error>,
}

impl NestedExprFolder<'_> {
    fn rewrite_special_expr(&mut self, expr: Expr) -> Expr {
        if self.error.is_some() {
            return expr;
        }

        match rewrite_expr(&expr, self.state) {
            Ok(rewritten) => rewritten,
            Err(err) => {
                self.error = Some(err);
                expr
            }
        }
    }

    fn rewrite_scoped_block(&mut self, block: Block) -> Block {
        if self.error.is_some() {
            return block;
        }

        match rewrite_block(&block, self.state.clone()) {
            Ok((rewritten, inner_state)) => {
                self.state.next_bridge_id_counter = inner_state.next_bridge_id_counter;
                rewritten
            }
            Err(err) => {
                self.error = Some(err);
                block
            }
        }
    }
}

impl Fold for NestedExprFolder<'_> {
    fn fold_expr(&mut self, expr: Expr) -> Expr {
        if self.error.is_some() {
            return expr;
        }

        match expr {
            Expr::If(_) | Expr::While(_) | Expr::ForLoop(_) | Expr::Loop(_) | Expr::Match(_) => {
                self.rewrite_special_expr(expr)
            }
            _ => syn::fold::fold_expr(self, expr),
        }
    }

    fn fold_block(&mut self, block: Block) -> Block {
        self.rewrite_scoped_block(block)
    }
}
