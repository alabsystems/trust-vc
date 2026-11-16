// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Contextual value modes, independently of runtime-check placement.
use super::*;
use crate::place_mode::{allows, join, place_mode};
mod expressions;
mod origins;
use origins::Origin;

struct Walk<'a, 'k> {
    index: &'a Index<'k>,
    decl: &'k FnDecl,
    errors: Vec<WfError>,
    // This is expression transport, never ownership of Spec storage.
    origins: Vec<Origin>,
    eligible: &'a [bool],
    ambient: Mode,
}

// Compute layout eligibility once. Structural checking may permit a whole
// generated storage save, but only this walk derives the saved value's mode.
pub(super) fn transport_locals(index: &Index<'_>, decl: &FnDecl) -> Vec<bool> {
    decl.locals
        .iter()
        .map(|local| origins::eligible(index, local))
        .collect()
}

pub(super) fn check<'a, 'k>(
    index: &'a Index<'k>,
    decl: &'k FnDecl,
    eligible: &'a [bool],
) -> Vec<WfError> {
    let mut walk = Walk {
        index,
        decl,
        errors: Vec::new(),
        origins: vec![Origin::Absent; decl.locals.len()],
        eligible,
        ambient: Mode::Spec,
    };
    for clause in decl
        .requires
        .iter()
        .chain(&decl.ensures)
        .chain(&decl.recommends)
    {
        walk.value_has_mode(&clause.expr, Mode::Spec);
    }
    for hint in decl.broadcast_hints() {
        walk.value_has_mode(hint, Mode::Spec);
    }
    for expr in decl.decreases.iter().chain(decl.decreases_when.iter()) {
        walk.value_has_mode(expr, Mode::Spec);
    }
    if let Some(condition) = decl.unwind.as_ref().and_then(crate::UnwindSpec::condition) {
        walk.value_has_mode(condition, Mode::Spec);
    }
    match &decl.body {
        Body::None => {}
        Body::Spec(expr) => {
            walk.value_has_mode(expr, Mode::Spec);
        }
        Body::Constant(expr) => {
            walk.ambient = Mode::Exec;
            walk.value_has_mode(expr, Mode::Exec);
        }
        Body::Stmts(block) => {
            walk.ambient = decl.mode;
            walk.statements(block);
        }
    }
    walk.errors
}

impl Walk<'_, '_> {
    fn error(&mut self, span: SpanId, actual: Mode, expected: Mode) {
        self.errors.push(WfError {
            class: WfClass::User,
            function: Some(self.decl.id),
            span,
            message: format!(
                "expression has mode {}, expected mode {}",
                actual.name(),
                expected.name()
            ),
        });
    }
    fn value_has_mode(&mut self, expr: &Expr, expected: Mode) -> Mode {
        let actual = self.expression(expr, expected);
        // Upstream has-mode consumers clear Unit. Keep the raw producer mode
        // for transport and for other expression consumers nevertheless.
        if expr.ty != Ty::Unit && !allows(actual, expected) {
            self.error(expr.span, actual, expected);
        }
        actual
    }
    fn scoped(&mut self, block: &Block) {
        let bindings = self.statements(block);
        for (local, saved) in bindings.into_iter().rev() {
            self.origins[local] = saved;
        }
    }
    fn merge(&mut self, a: &[Origin], b: &[Origin]) {
        for ((slot, a), b) in self.origins.iter_mut().zip(a).zip(b) {
            *slot = origins::merge(*a, *b);
        }
    }
    fn arguments(&mut self, target: &FnDecl, args: &[Expr]) {
        for (argument, parameter) in args.iter().zip(&target.params) {
            if let Some(parameter) = target.local(*parameter) {
                self.value_has_mode(argument, parameter.mode);
            }
        }
    }
    fn statements(&mut self, block: &Block) -> Vec<(usize, Origin)> {
        let mut bindings = Vec::new();
        for stmt in &block.stmts {
            match &stmt.kind {
                StmtKind::Let { local, init } => {
                    if self.decl.local(*local).is_none() {
                        continue;
                    }
                    let mode = init.as_ref().map(|expr| self.producer_mode(*local, expr));
                    if self.transport_temp(*local) {
                        bindings.push((local.index(), self.origins[local.index()]));
                        self.origins[local.index()] =
                            if self.origins[local.index()] == Origin::Absent {
                                Origin::Declared {
                                    site: stmt as *const Stmt as usize,
                                    mode: None,
                                }
                            } else {
                                Origin::Invalid
                            };
                        if let (Some(mode), Some(value)) = (mode, init) {
                            self.save_origin(*local, mode, &value.ty);
                        }
                    }
                }
                StmtKind::Assign { place, value } => {
                    if let Some(target) = place_mode(self.decl, &self.index.adts, place) {
                        let actual =
                            if place.projections.is_empty() && self.transport_temp(place.local) {
                                self.producer_mode(place.local, value)
                            } else {
                                self.value_has_mode(value, target.mode)
                            };
                        if place.projections.is_empty() {
                            self.save_origin(place.local, actual, &value.ty);
                        } else if self.transport_temp(place.local) {
                            self.origins[place.local.index()] = Origin::Invalid;
                        }
                    }
                }
                StmtKind::Call {
                    callee,
                    type_args,
                    args,
                    dest,
                    ..
                } => {
                    let Some(target) = self.index.fns.get(callee).copied() else {
                        continue;
                    };
                    self.arguments(target, args);
                    if let Some(dest) = dest {
                        if let (Some(ret), Some(place)) = (
                            target.local(target.ret),
                            place_mode(self.decl, &self.index.adts, dest),
                        ) {
                            let unit = ret.ty == Ty::Unit
                                || matches!(&ret.ty, Ty::Param(index) if type_args.get(*index as usize) == Some(&Ty::Unit));
                            if !unit && !allows(ret.mode, place.mode) {
                                self.error(stmt.span, ret.mode, place.mode);
                            }
                            if dest.projections.is_empty() {
                                if let Some(actual) = self.decl.local(dest.local) {
                                    if origins::return_matches(&ret.ty, type_args, &actual.ty) {
                                        self.save_origin(dest.local, ret.mode, &actual.ty);
                                    } else if self.transport_temp(dest.local) {
                                        self.origins[dest.local.index()] = Origin::Invalid;
                                    }
                                }
                            } else if self.transport_temp(dest.local) {
                                self.origins[dest.local.index()] = Origin::Invalid;
                            }
                        }
                    }
                }
                StmtKind::BorrowMut { dest, .. } => {
                    if let Some(local) = self.decl.local(*dest) {
                        self.save_origin(*dest, local.mode, &local.ty);
                    }
                }
                StmtKind::If {
                    cond,
                    then_block,
                    else_block,
                } => {
                    self.value_has_mode(
                        cond,
                        if self.ambient == Mode::Exec {
                            Mode::Exec
                        } else {
                            Mode::Spec
                        },
                    );
                    let before = self.origins.clone();
                    self.scoped(then_block);
                    let yes = self.origins.clone();
                    self.origins = before;
                    self.scoped(else_block);
                    let no = self.origins.clone();
                    self.merge(&yes, &no);
                }
                StmtKind::Block(block) => self.scoped(block),
                StmtKind::Ghost(block) | StmtKind::GhostTail { block, .. } => {
                    let outer = self.ambient;
                    self.ambient = Mode::Proof;
                    let bindings = self.statements(block);
                    if let StmtKind::GhostTail { tail, .. } = &stmt.kind {
                        self.value_has_mode(tail, Mode::Spec);
                    }
                    for (local, saved) in bindings.into_iter().rev() {
                        self.origins[local] = saved;
                    }
                    self.ambient = outer;
                }
                StmtKind::Return {
                    value: Some(value), ..
                } => {
                    if let Some(ret) = self.decl.local(self.decl.ret) {
                        self.value_has_mode(value, ret.mode);
                    }
                }
                StmtKind::Assert { expr, .. } | StmtKind::Assume { expr, .. } => {
                    self.value_has_mode(expr, Mode::Spec);
                }
                StmtKind::AssertBitVector {
                    requires, ensures, ..
                } => {
                    for clause in requires.iter().chain(ensures) {
                        self.value_has_mode(&clause.expr, Mode::Spec);
                    }
                }
                StmtKind::Loop(lp) => {
                    for invariant in &lp.invariants {
                        self.value_has_mode(&invariant.expr, Mode::Spec);
                    }
                    for measure in &lp.decreases {
                        self.value_has_mode(measure, Mode::Spec);
                    }
                    let before = self.origins.clone();
                    if let Some(condition) = &lp.cond {
                        let bindings = self.statements(&condition.block);
                        self.value_has_mode(&condition.expr, Mode::Exec);
                        for (local, saved) in bindings.into_iter().rev() {
                            self.origins[local] = saved;
                        }
                    }
                    self.scoped(&lp.body);
                    let after = self.origins.clone();
                    self.merge(&before, &after);
                }
                StmtKind::Return { value: None, .. }
                | StmtKind::BroadcastUse { .. }
                | StmtKind::Reveal { .. }
                | StmtKind::Hide { .. }
                | StmtKind::Break { .. }
                | StmtKind::Continue { .. }
                | StmtKind::Unreachable => {}
            }
        }
        bindings
    }
}
