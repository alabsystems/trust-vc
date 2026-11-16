// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Explicit entry, normal exits, backedges and scope-unwinding CFG edges.
use super::state::Work;
use super::*;
use crate::FnId;
use std::collections::HashMap;

pub(super) enum Event {
    Move(Place),
    Mutate(Place),
    Overwrite(Place),
}

pub(super) enum Action<'a> {
    None,
    Declare(LocalId, Option<&'a Expr>),
    Assign(Place, &'a Expr),
    Borrow(LocalId, Place),
    Call(FnId, &'a [Expr]),
    Result { call: usize, dest: Option<Place> },
    Drop(Vec<LocalId>),
    Return(Option<&'a Expr>),
}

pub(super) struct Node<'a> {
    pub(super) events: Vec<Event>,
    pub(super) action: Action<'a>,
    pub(super) next: Vec<usize>,
    pub(super) statement: Option<usize>,
}

pub(super) struct Builder<'a, 'ctx> {
    pub(super) ctx: &'a Ctx<'ctx>,
    pub(super) decl: &'a FnDecl,
    pub(super) nodes: Vec<Node<'a>>,
    targets: Vec<(LoopId, usize, usize, usize)>,
    scopes: Vec<Vec<LocalId>>,
    pub(super) loops: HashMap<LoopId, usize>,
    pub(super) exits: HashMap<LoopId, usize>,
    pub(super) tails: HashMap<usize, usize>,
    pub(super) after: HashMap<usize, usize>,
    pub(super) block_ends: HashMap<usize, usize>,
    pub(super) work: Work,
    pub(super) classifier: &'a Classifier<'a, 'ctx>,
    pub(super) place_modes: std::cell::RefCell<HashMap<Place, bool>>,
    pub(super) place_types: std::cell::RefCell<HashMap<Place, Option<Ty>>>,
    /// Immediate non-dereference children in this body's immutable universe.
    pub(super) initialization_children: Vec<Vec<usize>>,
}

impl<'a, 'ctx> Builder<'a, 'ctx> {
    pub(super) fn new(
        ctx: &'a Ctx<'ctx>,
        decl: &'a FnDecl,
        classifier: &'a Classifier<'a, 'ctx>,
    ) -> R<Self> {
        classifier.validate(ctx, decl)?;
        Ok(Self {
            ctx,
            decl,
            nodes: Vec::new(),
            targets: Vec::new(),
            scopes: Vec::new(),
            loops: HashMap::new(),
            exits: HashMap::new(),
            tails: HashMap::new(),
            after: HashMap::new(),
            block_ends: HashMap::new(),
            work: classifier.work(),
            classifier,
            place_modes: std::cell::RefCell::new(HashMap::new()),
            place_types: std::cell::RefCell::new(HashMap::new()),
            initialization_children: Vec::new(),
        })
    }
    pub(super) fn charge(&self, n: usize) -> R<()> {
        self.work.charge(n, self.decl.span)
    }
    pub(super) fn node(
        &mut self,
        statement: Option<usize>,
        events: Vec<Event>,
        action: Action<'a>,
        next: Vec<usize>,
    ) -> R<usize> {
        self.charge(1 + events.len() + next.len())?;
        let index = self.nodes.len();
        self.nodes.push(Node {
            events,
            action,
            next,
            statement,
        });
        Ok(index)
    }
    pub(super) fn value_moves(&self, expr: &Expr) -> R<Vec<Event>> {
        let remaining = self.work.remaining().get();
        super::super::aux_work::expression(self.work.remaining(), expr, expr.span)?;
        let size = remaining - self.work.remaining().get();
        self.charge(size.saturating_mul(size))?;
        let mut places = Vec::new();
        moves(self.ctx, expr, &mut places);
        self.work.places(&places, expr.span)?;
        let mut events = Vec::new();
        for place in places {
            if !self.kept_place(&place)? {
                continue;
            }
            let Some(ty) = self.typed_place(&place)? else {
                continue;
            };
            if self.owns(&ty)? {
                let slots = super::super::call_identity::owned_slots(
                    self.ctx,
                    &ty,
                    self.work.remaining(),
                    expr.span,
                )?;
                if slots.is_empty() {
                    events.push(Event::Move(place));
                } else {
                    for slot in slots {
                        self.charge(1 + place.projections.len() + slot.len())?;
                        let mut owner = place.clone();
                        owner.projections.extend(slot);
                        events.push(Event::Move(owner));
                    }
                }
            }
        }
        Ok(events)
    }
    pub(super) fn build(&mut self, block: &'a Block) -> R<usize> {
        self.node(None, Vec::new(), Action::None, Vec::new())?;
        let head = self.block(block, 0)?;
        self.node(None, Vec::new(), Action::None, vec![head])
    }
    fn locals(&self, block: &Block) -> R<Vec<LocalId>> {
        self.charge(block.stmts.len())?;
        Ok(block
            .stmts
            .iter()
            .filter_map(|stmt| match stmt.kind {
                StmtKind::Let { local, .. } => Some(local),
                _ => None,
            })
            .collect())
    }
    fn scope_exit(&mut self, locals: Vec<LocalId>, next: usize) -> R<usize> {
        self.charge(locals.len())?;
        let events = locals
            .iter()
            .map(|local| Event::Overwrite(Place::local(*local)))
            .collect();
        self.node(None, events, Action::Drop(locals), vec![next])
    }
    fn leave_scopes(&mut self, depth: usize, next: usize) -> R<usize> {
        self.charge(self.scopes.len())?;
        let count = self.scopes.iter().skip(depth).map(Vec::len).sum();
        self.charge(count)?;
        let locals = self.scopes.iter().skip(depth).flatten().copied().collect();
        self.scope_exit(locals, next)
    }
    fn block(&mut self, block: &'a Block, next: usize) -> R<usize> {
        let locals = self.locals(block)?;
        self.charge(locals.len())?;
        let mut head = self.scope_exit(locals.clone(), next)?;
        self.block_ends.insert(block as *const Block as usize, head);
        self.scopes.push(locals);
        for stmt in block.stmts.iter().rev() {
            head = self.statement(stmt, head)?;
        }
        self.scopes.pop();
        Ok(head)
    }
    fn statement(&mut self, stmt: &'a Stmt, next: usize) -> R<usize> {
        let statement = stmt as *const Stmt as usize;
        let key = Some(statement);
        let after = self.node(None, Vec::new(), Action::None, vec![next])?;
        self.after.insert(statement, after);
        match &stmt.kind {
            StmtKind::If {
                then_block,
                else_block,
                ..
            } => {
                let yes = self.block(then_block, after)?;
                let no = self.block(else_block, after)?;
                self.node(key, Vec::new(), Action::None, vec![yes, no])
            }
            StmtKind::Block(block) | StmtKind::Ghost(block) => {
                let head = self.block(block, after)?;
                self.node(key, Vec::new(), Action::None, vec![head])
            }
            StmtKind::GhostTail { block, tail } => {
                let locals = self.locals(block)?;
                self.charge(locals.len())?;
                let out = self.scope_exit(locals.clone(), after)?;
                super::super::aux_work::expression(self.work.remaining(), tail, tail.span)?;
                // The raw Unit tail is evaluated, never consumed as an owned
                // return. Its position still precedes the lexical scope drop.
                let tail_node = self.node(None, Vec::new(), Action::None, vec![out])?;
                self.block_ends
                    .insert(block as *const Block as usize, tail_node);
                self.tails.insert(statement, tail_node);
                let mut head = tail_node;
                self.scopes.push(locals);
                for stmt in block.stmts.iter().rev() {
                    head = self.statement(stmt, head)?;
                }
                self.scopes.pop();
                self.node(key, Vec::new(), Action::None, vec![head])
            }
            StmtKind::Loop(lp) => {
                let header = self.node(key, Vec::new(), Action::None, Vec::new())?;
                self.loops.insert(lp.id, header);
                self.exits.insert(lp.id, after);
                self.targets.push((lp.id, after, header, self.scopes.len()));
                let body = self.block(&lp.body, header)?;
                let condition = if let Some(condition) = &lp.cond {
                    let branch = self.node(None, Vec::new(), Action::None, vec![body, after])?;
                    self.block(&condition.block, branch)?
                } else {
                    body
                };
                self.targets.pop();
                self.charge(1)?;
                self.nodes[header].next = vec![condition];
                Ok(header)
            }
            StmtKind::Break { target, .. } | StmtKind::Continue { target, .. } => {
                self.charge(self.targets.len())?;
                let (_, out, again, depth) = *self
                    .targets
                    .iter()
                    .rev()
                    .find(|(id, _, _, _)| id == target)
                    .ok_or_else(|| {
                        refusal("resolution-control", "unbound loop target", stmt.span)
                    })?;
                let next = if matches!(stmt.kind, StmtKind::Break { .. }) {
                    out
                } else {
                    again
                };
                let next = self.leave_scopes(depth, next)?;
                self.node(key, Vec::new(), Action::None, vec![next])
            }
            StmtKind::Return { value, .. } => {
                let events = match value.as_ref().filter(|_| {
                    self.decl
                        .local(self.decl.ret)
                        .is_some_and(|local| local.mode != Mode::Spec)
                }) {
                    Some(value) => self.value_moves(value)?,
                    None => Vec::new(),
                };
                let next = self.leave_scopes(0, 0)?;
                self.node(key, events, Action::Return(value.as_ref()), vec![next])
            }
            StmtKind::Unreachable => self.node(key, Vec::new(), Action::None, Vec::new()),
            StmtKind::Call {
                callee, args, dest, ..
            } => self.call(stmt, *callee, args, dest.as_ref(), after),
            StmtKind::Let { local, init } => {
                let owned = self
                    .decl
                    .local(*local)
                    .is_some_and(|local| local.mode != Mode::Spec);
                let mut events = match (owned, init) {
                    (true, Some(value)) => self.value_moves(value)?,
                    _ => Vec::new(),
                };
                events.push(Event::Overwrite(Place::local(*local)));
                self.node(
                    key,
                    events,
                    Action::Declare(*local, init.as_ref()),
                    vec![after],
                )
            }
            StmtKind::Assign { place, value } => {
                let mut events = if self.kept_place(place)? {
                    self.value_moves(value)?
                } else {
                    Vec::new()
                };
                self.charge(2usize.saturating_mul(1 + place.projections.len()))?;
                events.push(Event::Overwrite(place.clone()));
                self.node(
                    key,
                    events,
                    Action::Assign(place.clone(), value),
                    vec![after],
                )
            }
            StmtKind::BorrowMut { dest, place } => {
                self.charge(2usize.saturating_mul(1 + place.projections.len()))?;
                self.node(
                    key,
                    vec![
                        Event::Mutate(place.clone()),
                        Event::Overwrite(Place::local(*dest)),
                    ],
                    Action::Borrow(*dest, place.clone()),
                    vec![after],
                )
            }
            _ => self.node(key, Vec::new(), Action::None, vec![after]),
        }
    }
}
