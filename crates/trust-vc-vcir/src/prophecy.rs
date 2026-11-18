//! Prophecy noninterference for the current, value-based IR.
//!
//! This is the effect discipline of Verus's `vir/src/modes.rs`: prophecy is
//! inferred once at declarations, propagated through values, and barred from
//! executable/tracked effects and termination measures. It grants no mutable
//! reference, future-value, resolution, or closure semantics.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashMap;

mod expressions;
mod value_modes;

use crate::{
    BinOp, Block, Body, DeclProphecy, Expr, ExprKind, FnDecl, FnId, LocalId, LocalKind, Mode,
    Place, SpanId, StmtKind, Ty, VcCrate, WfClass, WfError,
};

/// Both ordinary WF views use this same pass. The generator also preflights it
/// before building logical tables, so an invalid spec body supplies no equation.
pub(crate) fn check_crate(krate: &VcCrate) -> Vec<WfError> {
    let fns = krate.fns.iter().map(|decl| (decl.id, decl)).collect();
    krate
        .fns
        .iter()
        .flat_map(|decl| Checker::new(&fns, decl).check())
        .collect()
}

pub(crate) fn check_function(fns: &HashMap<FnId, &FnDecl>, decl: &FnDecl) -> Vec<WfError> {
    Checker::new(fns, decl).check()
}

pub(crate) fn ghost_tail_modes(krate: &VcCrate) -> Vec<crate::wf::GhostTailModeObservation> {
    let fns = krate.fns.iter().map(|decl| (decl.id, decl)).collect();
    krate
        .fns
        .iter()
        .flat_map(|decl| value_modes::analyze(&fns, decl).observations)
        .collect()
}

/// `None` is the upstream delayed-inference state, not a fresh arbitrary value.
type Classification = Option<bool>;

struct Checker<'a> {
    fns: &'a HashMap<FnId, &'a FnDecl>,
    decl: &'a FnDecl,
    locals: Vec<Classification>,
    errors: Vec<WfError>,
    tail_modes: HashMap<usize, Option<crate::wf::GhostTailModeClass>>,
}

impl<'a> Checker<'a> {
    fn new(fns: &'a HashMap<FnId, &'a FnDecl>, decl: &'a FnDecl) -> Self {
        Self {
            fns,
            decl,
            // Parameters and return binders start No, including spec params.
            // Explicit local markers are conservative even in malformed input
            // whose producer omitted the corresponding declaration statement.
            locals: decl
                .locals
                .iter()
                .map(|local| {
                    Some(
                        !matches!(local.kind, LocalKind::Param | LocalKind::Return)
                            && local.prophecy == DeclProphecy::Prophetic,
                    )
                })
                .collect(),
            errors: Vec::new(),
            tail_modes: value_modes::analyze(fns, decl).modes,
        }
    }

    fn report(&mut self, class: WfClass, span: SpanId, message: impl Into<String>) {
        self.errors.push(WfError {
            class,
            function: Some(self.decl.id),
            span,
            message: message.into(),
        });
    }

    fn forbid_value(&mut self, prophetic: bool, span: SpanId, reason: &str) {
        if prophetic {
            self.report(
                WfClass::User,
                span,
                format!("prophetic value not allowed for {reason}"),
            );
        }
    }

    fn forbid_control(&mut self, outer: bool, span: SpanId, operation: &str) {
        if outer {
            self.report(
                WfClass::User,
                span,
                format!("{operation} cannot occur in prophecy-conditional context"),
            );
        }
    }

    fn check(mut self) -> Vec<WfError> {
        let decl = self.decl;
        if decl.attrs.prophetic && decl.mode != Mode::Spec {
            self.report(
                WfClass::User,
                decl.span,
                "prophetic attribute can only be applied to 'spec' functions",
            );
        }
        for local in &decl.locals {
            if local.prophecy != DeclProphecy::Default {
                if local.mode != Mode::Spec {
                    self.report(
                        WfClass::User,
                        local.span,
                        "only a ghost variable can be prophetic",
                    );
                }
                if matches!(local.kind, LocalKind::Param | LocalKind::Return) {
                    self.report(
                        WfClass::Malformed,
                        local.span,
                        "a declaration prophecy marker on a parameter or return binder",
                    );
                }
            }
        }
        for clause in decl
            .requires
            .iter()
            .chain(&decl.ensures)
            .chain(&decl.recommends)
        {
            self.expr(&clause.expr, false);
        }
        for hint in decl.broadcast_hints() {
            self.expr(hint, false);
        }
        for measure in &decl.decreases {
            let prophetic = self.expr(measure, false);
            self.forbid_value(prophetic, measure.span, "'decreases' clause");
        }
        if let Some(when) = &decl.decreases_when {
            // Like other spec headers this is checked, but is not itself one
            // of the lexicographic measures checked by upstream mode checking.
            self.expr(when, false);
        }
        if let Some(condition) = decl.unwind_spec().condition() {
            self.expr(condition, false);
        }
        match &decl.body {
            Body::None => {}
            Body::Spec(body) | Body::Constant(body) => {
                let prophetic = self.expr(body, false);
                if !decl.attrs.prophetic && body.ty != Ty::Unit {
                    self.forbid_value(
                        prophetic,
                        body.span,
                        if decl.mode == Mode::Spec {
                            "body of non-prophetic spec function"
                        } else {
                            "return value"
                        },
                    );
                }
            }
            Body::Stmts(block) => self.block(block, false),
        }
        self.errors
    }

    fn classification(&mut self, local: LocalId, span: SpanId) -> bool {
        match self.locals.get(local.index()).copied() {
            Some(Some(prophetic)) => prophetic,
            Some(None) => {
                self.report(WfClass::User, span, "uninitialized infer-mode variable");
                false
            }
            // Ordinary WF reports dangling ids; this pass remains total on
            // diagnostic IR and must not mask other functions' diagnostics.
            None => false,
        }
    }

    fn set(&mut self, local: LocalId, value: Classification) {
        if let Some(slot) = self.locals.get_mut(local.index()) {
            *slot = value;
        }
    }

    fn declare(&mut self, local: LocalId, init: Option<bool>, outer: bool, span: SpanId) {
        let Some(declaration) = self.decl.local(local) else {
            return;
        };
        let init = if declaration.ty == Ty::Unit && !self.raw_result_temp(local) {
            init.map(|_| false)
        } else {
            init
        };
        if declaration.mode != Mode::Spec {
            // The current IR has already erased the mode coercion of an if
            // branch. Its executable declarations still cannot depend on that
            // branch's prophetic condition.
            self.forbid_value(
                init.unwrap_or(false) | outer,
                span,
                "declaration of non-ghost variables",
            );
        }
        let classification = match declaration.prophecy {
            DeclProphecy::Prophetic => Some(true),
            DeclProphecy::DelayedInfer if init.is_none() => None,
            DeclProphecy::Default | DeclProphecy::DelayedInfer => {
                Some(init.unwrap_or(false) | outer)
            }
        };
        self.set(local, classification);
    }

    fn assign(&mut self, place: &Place, prophetic: bool, outer: bool, span: SpanId) {
        let prophetic = if place.projections.is_empty()
            && !self.raw_result_temp(place.local)
            && self
                .decl
                .local(place.local)
                .is_some_and(|decl| decl.ty == Ty::Unit)
        {
            false
        } else {
            prophetic
        };
        if place.projections.is_empty() && self.locals.get(place.local.index()) == Some(&None) {
            // A source declaration infers RHS only. Generated expression
            // results stand for the value of the enclosing conditional, so
            // their separately checked branch initialization includes control.
            let result_temp = self.is_result_temp(place.local);
            self.set(place.local, Some(prophetic | (result_temp && outer)));
        }
        if !self.classification(place.local, span) {
            self.forbid_value(prophetic, span, "assignment to non-prophetic location");
            self.forbid_control(outer, span, "assignment to non-prophetic location");
        }
    }

    fn raw_result_temp(&self, local: LocalId) -> bool {
        self.decl
            .local(local)
            .is_some_and(|decl| decl.kind == LocalKind::Temp && decl.mode == Mode::Spec)
    }

    fn is_result_temp(&self, local: LocalId) -> bool {
        self.decl.local(local).is_some_and(|decl| {
            decl.kind == LocalKind::Temp
                && decl.mode == Mode::Spec
                && decl.prophecy == DeclProphecy::DelayedInfer
        })
    }

    fn conditional(&mut self, cond: &Expr, yes: &Block, no: &Block, outer: bool) {
        let condition = self.expr(cond, outer);
        // Ordinary delayed source declarations retain upstream's single
        // syntactic inference. Only still-uninitialized generated result temps
        // get independent branch initialization, checked and joined here.
        let pending: Vec<LocalId> = self
            .locals
            .iter()
            .enumerate()
            .filter_map(|(index, state)| {
                let local = LocalId(u32::try_from(index).ok()?);
                (state.is_none() && self.is_result_temp(local)).then_some(local)
            })
            .collect();
        self.block(yes, outer | condition);
        let yes_values: Vec<Classification> =
            pending.iter().map(|id| self.locals[id.index()]).collect();
        for local in &pending {
            self.set(*local, None);
        }
        self.block(no, outer | condition);
        for (local, yes_value) in pending.into_iter().zip(yes_values) {
            let no_value = self.locals[local.index()];
            let joined = match (yes_value, no_value) {
                (Some(yes), Some(no)) => Some(yes | no | condition),
                // Reading a result initialized on only one arm is rejected;
                // an incomplete branch never supplies a default No value.
                _ => None,
            };
            self.set(local, joined);
        }
    }

    fn call(&mut self, callee: FnId, args: &[Expr], outer: bool, span: SpanId) -> bool {
        let declaration = self.fns.get(&callee).copied();
        let prohibited = declaration.and_then(|decl| match decl.mode {
            Mode::Spec => None,
            Mode::Exec => Some((
                "argument to exec-mode function",
                "call to exec-mode function",
            )),
            Mode::Proof => {
                let tracked = decl
                    .params
                    .iter()
                    .any(|id| decl.local(*id).is_some_and(|p| p.mode != Mode::Spec))
                    || decl
                        .local(decl.ret)
                        .is_some_and(|r| r.mode != Mode::Spec && r.ty != Ty::Unit);
                tracked.then_some((
                    "argument to proof-mode function with tracked parameters",
                    "call to proof-mode function with tracked parameters",
                ))
            }
        });
        if let Some((_, operation)) = prohibited {
            self.forbid_control(outer, span, operation);
        }
        let mut prophetic = declaration.is_some_and(|decl| decl.attrs.prophetic);
        for argument in args {
            let raw = self.expr(argument, outer);
            let taint = argument.ty != Ty::Unit && raw;
            if let Some((reason, _)) = prohibited {
                self.forbid_value(taint, argument.span, reason);
            }
            prophetic |= taint;
        }
        prophetic
    }

    fn exprs(&mut self, expressions: &[Expr], outer: bool) -> bool {
        let mut prophetic = false;
        for expression in expressions {
            prophetic |= self.expr(expression, outer);
        }
        prophetic
    }

    fn bind(&mut self, vars: &[(LocalId, Ty)]) -> Vec<(LocalId, Classification)> {
        let mut saved = Vec::new();
        for (id, _) in vars {
            if let Some(old) = self.locals.get(id.index()).copied() {
                saved.push((*id, old));
                self.set(*id, Some(false));
            }
        }
        saved
    }

    fn restore(&mut self, saved: Vec<(LocalId, Classification)>) {
        for (id, value) in saved.into_iter().rev() {
            self.set(id, value);
        }
    }

    fn block(&mut self, block: &Block, outer: bool) {
        let saved = self.statements(block, outer);
        self.restore(saved);
    }

    /// Restore declarations, while preserving one-time inference of an outer
    /// local by an assignment inside a nested block or syntactic branch.
    fn statements(&mut self, block: &Block, outer: bool) -> Vec<(LocalId, Classification)> {
        let mut saved = Vec::new();
        for statement in &block.stmts {
            let span = statement.span;
            match &statement.kind {
                StmtKind::Let { local, init } => {
                    let value = init.as_ref().map(|expr| self.expr(expr, outer));
                    if let Some(old) = self.locals.get(local.index()).copied() {
                        saved.push((*local, old));
                    }
                    self.declare(*local, value, outer, span);
                }
                StmtKind::LetChecked { local, init } => {
                    let value = self.expr(init, outer);
                    if let Some(old) = self.locals.get(local.index()).copied() {
                        saved.push((*local, old));
                    }
                    self.declare(*local, Some(value), outer, span);
                }
                StmtKind::BorrowMut { dest, place } => {
                    let prophetic = self.classification(place.local, span);
                    self.forbid_control(outer, span, "mutable borrow");
                    self.assign(&Place::local(*dest), prophetic, outer, span);
                }
                StmtKind::Assign { place, value } | StmtKind::AssignSpec { place, value } => {
                    let raw = self.expr(value, outer);
                    let taint = if value.ty == Ty::Unit && !self.raw_result_temp(place.local) {
                        false
                    } else {
                        raw
                    };
                    self.assign(place, taint, outer, span);
                }
                StmtKind::Call {
                    callee, args, dest, ..
                } => {
                    let result = self.call(*callee, args, outer, span);
                    if let Some(dest) = dest {
                        self.assign(dest, result, outer, span);
                    }
                }
                StmtKind::Assert { expr, .. } | StmtKind::Assume { expr, .. } => {
                    self.expr(expr, outer);
                }
                StmtKind::AssertBitVector {
                    requires, ensures, ..
                } => {
                    for clause in requires.iter().chain(ensures) {
                        self.expr(&clause.expr, outer);
                    }
                }
                StmtKind::If {
                    cond,
                    then_block,
                    else_block,
                }
                | StmtKind::IfSpec {
                    cond,
                    then_block,
                    else_block,
                } => {
                    self.conditional(cond, then_block, else_block, outer);
                }
                StmtKind::Return { value, .. } => {
                    self.forbid_control(outer, span, "return");
                    if let Some(value) = value {
                        let taint = self.expr(value, outer);
                        self.forbid_value(value.ty != Ty::Unit && taint, span, "return value");
                    }
                }
                StmtKind::GhostTail { block, tail } => {
                    let saved = self.statements(block, outer);
                    let prophetic = self.expr(tail, outer);
                    match self
                        .tail_modes
                        .get(&(statement as *const crate::Stmt as usize))
                        .copied()
                        .flatten()
                    {
                        Some(crate::wf::GhostTailModeClass::Spec) => {}
                        Some(_) => self.forbid_value(prophetic, span, "'Ghost' wrapper"),
                        None => self.report(
                            WfClass::Malformed,
                            span,
                            "a proof block tail without a valid raw Unit value-mode origin",
                        ),
                    }
                    self.restore(saved);
                }
                StmtKind::Ghost(block) | StmtKind::Block(block) => self.block(block, outer),
                StmtKind::Loop(lp) => {
                    self.forbid_control(outer, span, "loop");
                    if let Some(cond) = &lp.cond {
                        let scope = self.statements(&cond.block, false);
                        let condition = self.expr(&cond.expr, false);
                        self.forbid_value(condition, cond.expr.span, "loop condition");
                        self.restore(scope);
                    }
                    self.block(&lp.body, false);
                    for invariant in &lp.invariants {
                        self.expr(&invariant.expr, outer);
                    }
                    for measure in &lp.decreases {
                        let taint = self.expr(measure, outer);
                        self.forbid_value(taint, measure.span, "'decreases' clause");
                    }
                }
                StmtKind::Break { .. } => self.forbid_control(outer, span, "break"),
                StmtKind::Continue { .. } => self.forbid_control(outer, span, "continue"),
                StmtKind::BroadcastUse { .. }
                | StmtKind::Reveal { .. }
                | StmtKind::Hide { .. }
                | StmtKind::Unreachable => {}
            }
        }
        saved
    }
}
