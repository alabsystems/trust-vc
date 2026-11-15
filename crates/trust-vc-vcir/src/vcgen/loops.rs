//! What the generator needs to know about a function's loops before it
//! walks the body.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Verus decides these syntactically, over the whole body in program order
//! (`vir/src/sst_vars.rs`: `stm_assign` for the locals a loop modifies,
//! `stm_mutations` for the parameters modified before or in it;
//! `vir/src/ast_to_sst.rs`, `loop_body_has_break`). They do not depend on
//! which paths are reachable, so neither do these; only the branches of an
//! `if` are walked apart, as `stm_mutations` walks them. The first two are
//! computed on SST, where `ast_to_sst.rs` has dropped the statements of a
//! block after one that never finishes in its sense (a `return`, a coerced
//! `!` expression, an `if` whose branches both never finish, a `loop`
//! without a `break`); the walks here skip those statements too
//! ([`live_prefix`]). The statements after a `break;` or `continue;`
//! statement stay: they are unreachable, yet their assignments count.
//! Whether a loop has a `break` is decided on the AST, dead code included.

use std::collections::{BTreeSet, HashMap};

use crate::ids::{LocalId, LoopId};
use crate::item::{Body, FnDecl};
use crate::stmt::{Block, Stmt, StmtKind};

/// Facts about one loop.
#[derive(Debug, Clone, Default)]
pub(crate) struct LoopInfo {
    /// Locals the loop's condition or body assigns (the root of every
    /// assignment target and call destination). Locals declared inside the
    /// loop are among them; the caller keeps the ones in scope before it.
    pub(crate) modified: BTreeSet<LocalId>,
    /// Parameters assigned on the way to the loop (in the statements before
    /// it and in the branches that enclose it, not in the other branches of
    /// an `if` it is in) or in it: in the loop's own query their entry
    /// values are unrelated to their current values.
    pub(crate) premodified: BTreeSet<LocalId>,
    /// A `break` of this loop appears in its body.
    pub(crate) has_break: bool,
}

/// The facts of every loop of `decl`.
pub(crate) fn loop_infos(decl: &FnDecl) -> HashMap<LoopId, LoopInfo> {
    let mut out = HashMap::new();
    if let Body::Stmts(block) = &decl.body {
        let params: BTreeSet<LocalId> = decl.params.iter().copied().collect();
        let mut assigned_params = BTreeSet::new();
        walk(block, &params, &mut assigned_params, &mut out);
    }
    out
}

fn walk(
    block: &Block,
    params: &BTreeSet<LocalId>,
    assigned_params: &mut BTreeSet<LocalId>,
    out: &mut HashMap<LoopId, LoopInfo>,
) {
    for stmt in live_prefix(block) {
        match &stmt.kind {
            StmtKind::Assign { place, .. } => {
                if params.contains(&place.local) {
                    assigned_params.insert(place.local);
                }
            }
            StmtKind::Call {
                dest: Some(dest), ..
            } => {
                if params.contains(&dest.local) {
                    assigned_params.insert(dest.local);
                }
            }
            // Each branch starts from what was assigned before the `if`;
            // after it, what either assigned.
            StmtKind::If {
                then_block,
                else_block,
                ..
            } => {
                let mut then_assigned = assigned_params.clone();
                walk(then_block, params, &mut then_assigned, out);
                walk(else_block, params, assigned_params, out);
                assigned_params.extend(then_assigned);
            }
            StmtKind::Ghost(inner) | StmtKind::Block(inner) => {
                walk(inner, params, assigned_params, out);
            }
            StmtKind::Loop(lp) => {
                let mut modified = BTreeSet::new();
                if let Some(cond) = &lp.cond {
                    assigned(&cond.block, &mut modified);
                }
                assigned(&lp.body, &mut modified);
                assigned_params.extend(modified.intersection(params).copied());
                if let Some(cond) = &lp.cond {
                    walk(&cond.block, params, assigned_params, out);
                }
                walk(&lp.body, params, assigned_params, out);
                let info = LoopInfo {
                    modified,
                    premodified: assigned_params.clone(),
                    has_break: breaks(&lp.body, lp.id),
                };
                out.insert(lp.id, info);
            }
            StmtKind::Let { .. }
            | StmtKind::Call { dest: None, .. }
            | StmtKind::Assert { .. }
            | StmtKind::AssertBitVector { .. }
            | StmtKind::Assume { .. }
            | StmtKind::Return { .. }
            | StmtKind::Reveal { .. }
            | StmtKind::Hide { .. }
            | StmtKind::Break { .. }
            | StmtKind::Continue { .. }
            | StmtKind::Unreachable => {}
        }
    }
}

/// Add the root of every place `block` assigns, at any depth, to `out`.
pub(crate) fn assigned(block: &Block, out: &mut BTreeSet<LocalId>) {
    for stmt in live_prefix(block) {
        match &stmt.kind {
            StmtKind::Assign { place, .. } => {
                out.insert(place.local);
            }
            StmtKind::Call {
                dest: Some(dest), ..
            } => {
                out.insert(dest.local);
            }
            StmtKind::If {
                then_block,
                else_block,
                ..
            } => {
                assigned(then_block, out);
                assigned(else_block, out);
            }
            StmtKind::Ghost(inner) | StmtKind::Block(inner) => assigned(inner, out),
            StmtKind::Loop(lp) => {
                if let Some(cond) = &lp.cond {
                    assigned(&cond.block, out);
                }
                assigned(&lp.body, out);
            }
            StmtKind::Let { .. }
            | StmtKind::Call { dest: None, .. }
            | StmtKind::Assert { .. }
            | StmtKind::AssertBitVector { .. }
            | StmtKind::Assume { .. }
            | StmtKind::Return { .. }
            | StmtKind::Reveal { .. }
            | StmtKind::Hide { .. }
            | StmtKind::Break { .. }
            | StmtKind::Continue { .. }
            | StmtKind::Unreachable => {}
        }
    }
}

/// Does a `break` of loop `id` appear anywhere in `block`?
fn breaks(block: &Block, id: LoopId) -> bool {
    block.stmts.iter().any(|stmt| match &stmt.kind {
        StmtKind::Break { target, .. } => *target == id,
        StmtKind::If {
            then_block,
            else_block,
            ..
        } => breaks(then_block, id) || breaks(else_block, id),
        StmtKind::Ghost(inner) | StmtKind::Block(inner) => breaks(inner, id),
        StmtKind::Loop(lp) => {
            lp.cond.as_ref().is_some_and(|cond| breaks(&cond.block, id)) || breaks(&lp.body, id)
        }
        _ => false,
    })
}

/// The statements of `block` that Verus keeps: up to and including the
/// first that never finishes ([`diverges`]).
pub(crate) fn live_prefix(block: &Block) -> &[Stmt] {
    live_prefix_of(&block.stmts)
}

/// [`live_prefix`] of a list of statements.
pub(crate) fn live_prefix_of(stmts: &[Stmt]) -> &[Stmt] {
    match stmts.iter().position(diverges) {
        Some(index) => &stmts[..=index],
        None => stmts,
    }
}

/// Does `stmt` never finish, in `ast_to_sst.rs`'s sense (its value is
/// `Maybe::Never`)? A `break` or `continue` statement finishes there
/// (`ExprX::BreakOrContinue` has a unit value); a coerced one is followed
/// by [`StmtKind::Unreachable`].
pub(crate) fn diverges(stmt: &Stmt) -> bool {
    match &stmt.kind {
        StmtKind::Return { .. } | StmtKind::Unreachable => true,
        StmtKind::If {
            then_block,
            else_block,
            ..
        } => block_diverges(then_block) && block_diverges(else_block),
        StmtKind::Ghost(inner) | StmtKind::Block(inner) => block_diverges(inner),
        StmtKind::Loop(lp) => lp.cond.is_none() && !breaks(&lp.body, lp.id),
        _ => false,
    }
}

fn block_diverges(block: &Block) -> bool {
    block.stmts.iter().any(diverges)
}
