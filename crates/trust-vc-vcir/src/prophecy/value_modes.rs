//! Raw Unit-value provenance for proof-block tails.
//!
//! Storage modes of generated temporaries are not modes of their producers.
//! This ledger derives the latter; unknown or conflicting origins stay unknown.

use super::*;

mod expressions;
use crate::wf::{GhostTailModeClass as Class, GhostTailModeObservation};
use crate::{Lit, Stmt};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Origin {
    Absent,
    Declared {
        site: usize,
        mode: Option<Class>,
        assigned: bool,
    },
    Invalid,
}

pub(super) struct Report {
    pub(super) modes: HashMap<usize, Option<Class>>,
    pub(super) observations: Vec<GhostTailModeObservation>,
}

struct Walk<'a> {
    fns: &'a HashMap<FnId, &'a FnDecl>,
    decl: &'a FnDecl,
    report: Report,
}

fn join(a: Class, b: Class) -> Class {
    if a == Class::Spec || b == Class::Spec {
        Class::Spec
    } else {
        Class::NonSpec
    }
}

// Compare the same single-level substitution as ordinary call WF, borrowing
// the already materialized types instead of allocating an expanded return.
fn instantiated_type_matches(formal: &Ty, type_args: &[Ty], actual: &Ty) -> bool {
    match (formal, actual) {
        (Ty::Param(index), _) => type_args.get(*index as usize) == Some(actual),
        (Ty::Tuple(formal), Ty::Tuple(actual)) => {
            formal.len() == actual.len()
                && formal
                    .iter()
                    .zip(actual)
                    .all(|(formal, actual)| instantiated_type_matches(formal, type_args, actual))
        }
        (Ty::Adt(formal_id, formal), Ty::Adt(actual_id, actual)) => {
            formal_id == actual_id
                && formal.len() == actual.len()
                && formal
                    .iter()
                    .zip(actual)
                    .all(|(formal, actual)| instantiated_type_matches(formal, type_args, actual))
        }
        (
            Ty::Ref {
                mutable: formal_mut,
                inner: formal,
            },
            Ty::Ref {
                mutable: actual_mut,
                inner: actual,
            },
        ) => formal_mut == actual_mut && instantiated_type_matches(formal, type_args, actual),
        (Ty::MutRef(formal), Ty::MutRef(actual)) => {
            instantiated_type_matches(formal, type_args, actual)
        }
        (Ty::Bool | Ty::Int(_) | Ty::Unit, _) => formal == actual,
        _ => false,
    }
}

// The return mode remains the signature's mode. Type instantiation does not
// waive the original-signature effect policy in Checker::call.
fn instantiated_return_mode(decl: &FnDecl, type_args: &[Ty], actual: &Ty) -> Option<Mode> {
    if type_args.len() != decl.type_params.len() {
        return None;
    }
    let ret = decl.local(decl.ret)?;
    instantiated_type_matches(&ret.ty, type_args, actual).then_some(ret.mode)
}

fn merge(a: Origin, b: Origin) -> Origin {
    match (a, b) {
        (Origin::Absent, Origin::Absent) => Origin::Absent,
        (
            Origin::Declared {
                site: a,
                mode: am,
                assigned: aa,
            },
            Origin::Declared {
                site: b,
                mode: bm,
                assigned: ba,
            },
        ) if a == b => Origin::Declared {
            site: a,
            mode: am.zip(bm).map(|(a, b)| join(a, b)),
            assigned: aa && ba,
        },
        _ => Origin::Invalid,
    }
}

pub(super) fn analyze<'a>(fns: &'a HashMap<FnId, &'a FnDecl>, decl: &'a FnDecl) -> Report {
    let mut walk = Walk {
        fns,
        decl,
        report: Report {
            modes: HashMap::new(),
            observations: Vec::new(),
        },
    };
    let mut state = vec![Origin::Absent; decl.locals.len()];
    match &decl.body {
        Body::Stmts(block) => {
            walk.statements(block, &mut state);
        }
        Body::Spec(expr) | Body::Constant(expr) => {
            walk.expression(expr, &mut state);
        }
        Body::None => {}
    }
    walk.report
}

impl Walk<'_> {
    fn temporary(&self, local: LocalId) -> bool {
        self.decl
            .local(local)
            .is_some_and(|decl| decl.kind == LocalKind::Temp)
    }
    fn define(
        &self,
        state: &mut [Origin],
        local: LocalId,
        ty: Option<&Ty>,
        mode: Option<Class>,
        known: bool,
    ) {
        if !self.temporary(local) {
            return;
        }
        let declaration = &self.decl.locals[local.index()];
        let valid =
            known && ty == Some(&declaration.ty) && (declaration.ty != Ty::Unit || mode.is_some());
        if let Some(origin) = state.get_mut(local.index()) {
            *origin = match *origin {
                Origin::Declared {
                    site,
                    assigned: false,
                    ..
                } if valid => Origin::Declared {
                    site,
                    mode,
                    assigned: true,
                },
                _ => Origin::Invalid,
            };
        }
    }
    fn read(&self, state: &[Origin], place: &Place) -> Option<Class> {
        let declaration = self.decl.local(place.local)?;
        if declaration.kind != LocalKind::Temp {
            // Source ReadPlace in this Ghost-tail use is checked with
            // expected Spec. This is NOT a coercion of an ANF saved result.
            return Some(Class::Spec);
        }
        match state.get(place.local.index())? {
            Origin::Declared {
                mode,
                assigned: true,
                ..
            } if declaration.ty == Ty::Unit && place.projections.is_empty() => *mode,
            Origin::Declared { assigned: true, .. }
                if declaration.ty != Ty::Unit && !place.projections.is_empty() =>
            {
                Some(Class::Spec)
            }
            _ => None,
        }
    }
    fn known_projection_input(&self, expression: &Expr, state: &[Origin]) -> bool {
        if let ExprKind::Read(place) = &expression.kind {
            let Some(local) = self.decl.local(place.local) else {
                return false;
            };
            if local.kind != LocalKind::Temp {
                return true;
            }
            return matches!(state.get(place.local.index()),Some(Origin::Declared{assigned:true,mode,..}) if local.ty!=Ty::Unit || mode.is_some());
        }
        if let ExprKind::Call {
            callee, type_args, ..
        } = &expression.kind
        {
            if self.fns.get(callee).is_none_or(|callee| {
                callee.mode != Mode::Spec
                    || instantiated_return_mode(callee, type_args, &expression.ty).is_none()
            }) {
                return false;
            }
        }
        if matches!(
            expression.kind,
            ExprKind::ProofInSpec(_)
                | ExprKind::ProofInSpecTail { .. }
                | ExprKind::UntriggeredQuant { .. }
                | ExprKind::UntriggeredChoose { .. }
        ) {
            return false;
        }
        let mut known = true;
        expression.for_each_child(&mut |child| {
            known &= self.known_projection_input(child, state);
        });
        known
    }
    fn scoped(&mut self, block: &Block, state: &mut Vec<Origin>) {
        let saved = self.statements(block, state);
        for (local, origin) in saved.into_iter().rev() {
            state[local] = origin;
        }
    }
    fn conditional(&mut self, cond: &Expr, yes: &Block, no: &Block, state: &mut Vec<Origin>) {
        self.expression(cond, state);
        let mut a = state.clone();
        let mut b = state.clone();
        self.scoped(yes, &mut a);
        self.scoped(no, &mut b);
        for ((slot, a), b) in state.iter_mut().zip(a).zip(b) {
            *slot = merge(a, b);
        }
    }
    fn statements(&mut self, block: &Block, state: &mut Vec<Origin>) -> Vec<(usize, Origin)> {
        let mut saved = Vec::new();
        for stmt in &block.stmts {
            match &stmt.kind {
                StmtKind::Let { local, init } => {
                    let mode = init
                        .as_ref()
                        .and_then(|value| self.expression(value, state));
                    if self.temporary(*local) {
                        if let Some(origin) = state.get_mut(local.index()) {
                            saved.push((local.index(), *origin));
                            *origin = if *origin == Origin::Absent {
                                Origin::Declared {
                                    site: stmt as *const Stmt as usize,
                                    mode: None,
                                    assigned: false,
                                }
                            } else {
                                Origin::Invalid
                            };
                        }
                        if let Some(value) = init {
                            let known = self.known_projection_input(value, state);
                            self.define(state, *local, Some(&value.ty), mode, known);
                        }
                    }
                }
                StmtKind::Assign { place, value } => {
                    let mode = self.expression(value, state);
                    if place.projections.is_empty() {
                        let known = self.known_projection_input(value, state);
                        self.define(state, place.local, Some(&value.ty), mode, known);
                    } else if self.temporary(place.local) {
                        state[place.local.index()] = Origin::Invalid;
                    }
                }
                StmtKind::Call {
                    callee,
                    type_args,
                    args,
                    dest,
                    ..
                } => {
                    for arg in args {
                        self.expression(arg, state);
                    }
                    if let Some(dest) = dest {
                        if dest.projections.is_empty() {
                            let actual = self.decl.local(dest.local).map(|local| &local.ty);
                            let returned = actual.and_then(|ty| {
                                self.fns
                                    .get(callee)
                                    .filter(|decl| decl.mode != Mode::Spec)
                                    .and_then(|decl| instantiated_return_mode(decl, type_args, ty))
                            });
                            let mode = returned
                                .filter(|_| actual == Some(&Ty::Unit))
                                .map(Class::from);
                            let known = returned.is_some()
                                && args
                                    .iter()
                                    .all(|arg| self.known_projection_input(arg, state));
                            self.define(state, dest.local, actual, mode, known);
                        } else if self.temporary(dest.local) {
                            state[dest.local.index()] = Origin::Invalid;
                        }
                    }
                }
                StmtKind::GhostTail { block, tail } => {
                    let bindings = self.statements(block, state);
                    let mode = self.expression(tail, state);
                    self.report.modes.insert(stmt as *const Stmt as usize, mode);
                    self.report.observations.push(GhostTailModeObservation {
                        function: self.decl.id,
                        span: stmt.span,
                        class: mode,
                    });
                    for (local, origin) in bindings.into_iter().rev() {
                        state[local] = origin;
                    }
                }
                StmtKind::If {
                    cond,
                    then_block,
                    else_block,
                } => self.conditional(cond, then_block, else_block, state),
                StmtKind::Ghost(block) | StmtKind::Block(block) => self.scoped(block, state),
                StmtKind::Assert { expr, .. } | StmtKind::Assume { expr, .. } => {
                    self.expression(expr, state);
                }
                StmtKind::AssertBitVector {
                    requires, ensures, ..
                } => {
                    for clause in requires.iter().chain(ensures) {
                        self.expression(&clause.expr, state);
                    }
                }
                StmtKind::Return { value, .. } => {
                    if let Some(value) = value {
                        self.expression(value, state);
                    }
                }
                StmtKind::Loop(lp) => {
                    let before = state.clone();
                    if let Some(cond) = &lp.cond {
                        self.scoped(&cond.block, state);
                        self.expression(&cond.expr, state);
                    }
                    self.scoped(&lp.body, state);
                    for expr in lp
                        .invariants
                        .iter()
                        .map(|inv| &inv.expr)
                        .chain(&lp.decreases)
                    {
                        self.expression(expr, state);
                    }
                    for (slot, old) in state.iter_mut().zip(before) {
                        *slot = merge(*slot, old);
                    }
                }
                StmtKind::BorrowMut { dest, .. } => {
                    if self.temporary(*dest) {
                        state[dest.index()] = Origin::Invalid;
                    }
                }
                StmtKind::BroadcastUse { .. }
                | StmtKind::Reveal { .. }
                | StmtKind::Hide { .. }
                | StmtKind::Break { .. }
                | StmtKind::Continue { .. }
                | StmtKind::Unreachable => {}
            }
        }
        saved
    }
}
