// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Loop cuts transport ownership by place, never by equating old and fresh refs.
use super::*;
use crate::vcgen::resolution::OwnershipState;
use std::collections::HashSet;

pub(super) struct JoinedOwnership {
    pub(super) moved: Vec<Place>,
    pub(super) loans: Vec<mut_refs::Loan>,
    pub(super) escaped: Vec<Place>,
    pub(super) resolved: Vec<Term>,
}

impl Gen<'_> {
    pub(super) fn price_ownership_term(&self, value: &Term, span: SpanId) -> R<()> {
        if let Some(work) = self.resolution.remaining() {
            super::super::inline_work::term(work, value, 1, span)?;
        }
        Ok(())
    }

    fn price_ownership_value(&self, value: &Val, span: SpanId) -> R<()> {
        if let Some(work) = self.resolution.remaining() {
            super::super::inline_work::value(work, value, 1, span)?;
        }
        Ok(())
    }

    pub(super) fn price_ownership_place(&self, place: &Place, span: SpanId) -> R<()> {
        self.resolution.charge(1, span)?;
        self.resolution.charge(place.projections.len(), span)
    }

    pub(super) fn price_ownership_path(&self, path: &Path, copies: usize, span: SpanId) -> R<()> {
        if self.resolution.remaining().is_none() {
            return Ok(());
        }
        for _ in 0..copies {
            self.resolution
                .charge(path.declared.len() + path.env.len(), span)?;
            for value in path.env.values() {
                self.price_ownership_value(value, span)?;
            }
            for term in path.guard.iter().chain(&path.resolved) {
                self.price_ownership_term(term, span)?;
            }
            for place in path.moved.iter().chain(&path.escaped_loans) {
                self.price_ownership_place(place, span)?;
            }
            for loan in &path.loans {
                self.price_ownership_term(&loan.reference, span)?;
                for place in &loan.places {
                    self.price_ownership_place(place, span)?;
                }
            }
        }
        Ok(())
    }

    fn fresh_loop_value(&mut self, local: LocalId, guard: &[Term], span: SpanId) -> R<Val> {
        let (shape, name) = self.local_shape(local, span)?;
        // Price the actual layout before constructing any fresh value or
        // membership. The cell is the analysis's remaining original budget.
        let mut work = vec![&shape];
        while let Some(shape) = work.pop() {
            self.resolution.charge(1, span)?;
            if let Shape::Node(children) = shape {
                self.resolution.charge(children.len(), span)?;
                work.extend(children);
            }
        }
        self.fresh_at(&shape, &name, guard)
    }

    fn bind_ownership(&mut self, path: &mut Path, state: OwnershipState, span: SpanId) -> R<()> {
        self.resolution.charge(state.initialized.len(), span)?;
        let mut initialized = HashSet::new();
        for place in state.initialized {
            self.price_ownership_place(&place, span)?;
            initialized.insert(place);
        }
        path.moved = state.moved;
        path.escaped_loans = state.escaped;
        path.loans.clear();
        // Resolved terms belong to the preceding representation. Resolution
        // is rederived on the current carriers at the next analyzed point.
        path.resolved.clear();
        for (owner, footprints) in state.loans {
            self.price_ownership_place(&owner, span)?;
            let mut unavailable = !initialized.contains(&owner);
            for moved in &path.moved {
                self.price_ownership_place(moved, span)?;
                unavailable |= super::super::resolution::overlaps(moved, &owner);
            }
            let root = path.env.get(&owner.local);
            if unavailable || !path.declared.contains(&owner.local) {
                // A loan with no available carrier cannot be discharged by
                // resolving an unrelated fresh reference.
                self.resolution.charge(footprints.len(), span)?;
                path.escaped_loans.extend(footprints);
                continue;
            }
            let Some(root) = root else {
                self.resolution.charge(footprints.len(), span)?;
                path.escaped_loans.extend(footprints);
                continue;
            };
            self.price_ownership_value(root, span)?;
            let local = self
                .decl
                .local(owner.local)
                .ok_or_else(|| refusal("loop-state", "a loan owner has no declaration", span))?;
            let reference =
                super::super::expr::project(self.ctx, &self.types, root, &local.ty, &owner, span, Some(&self.static_work))?;
            let Val::Leaf(reference) = reference else {
                return Err(refusal(
                    "loop-state",
                    "a loan owner is not an opaque carrier",
                    span,
                ));
            };
            self.resolution.charge(1, span)?;
            path.loans.push(mut_refs::Loan {
                places: footprints,
                reference,
            });
        }
        Ok(())
    }

    pub(super) fn isolated_loop_path(&mut self, outer: &Path, lp: &Loop, span: SpanId) -> R<Path> {
        let state = self.resolution.head_state(lp.id, span)?;
        self.resolution.charge(outer.declared.len(), span)?;
        let mut inner = Path {
            declared: outer.declared.clone(),
            live: true,
            ..Path::default()
        };
        let represented: HashSet<_> = match &state {
            Some(state) => {
                self.resolution.charge(state.represented.len(), span)?;
                state.represented.iter().copied().collect()
            }
            None => outer.env.keys().copied().collect(),
        };
        for local in &outer.declared {
            self.resolution.charge(1, span)?;
            if represented.contains(local) {
                let value = self.fresh_loop_value(*local, &[], span)?;
                inner.env.insert(*local, value);
            }
        }
        if let Some(state) = state {
            self.bind_ownership(&mut inner, state, span)?;
            let points = self.resolution.loop_points(lp.id, span)?;
            self.resolve_places(&mut inner, &points, span)?;
        } else if self.resolution.remaining().is_some() {
            // An independently checked loop in unreachable source has no
            // reachable CFG input. Preserve restrictions conservatively;
            // absence of a state is never a fresh ownership permission.
            self.price_ownership_path(outer, 1, span)?;
            inner.moved = outer.moved.clone();
            inner.escaped_loans = self.active_borrows(outer)?;
        }
        Ok(inner)
    }

    pub(super) fn joined_loop_ownership(
        &mut self,
        path: &mut Path,
        lp: &Loop,
        span: SpanId,
    ) -> R<()> {
        if let Some(state) = self.resolution.head_state(lp.id, span)? {
            self.bind_ownership(path, state, span)?;
            let points = self.resolution.loop_points(lp.id, span)?;
            self.resolve_places(path, &points, span)?;
        }
        Ok(())
    }

    pub(super) fn isolated_loop_exit(
        &mut self,
        path: &mut Path,
        lp: &Loop,
        info: &LoopInfo,
        span: SpanId,
    ) -> R<()> {
        let Some(state) = self.resolution.exit_state(lp.id, span)? else {
            if self.resolution.remaining().is_some() {
                // The analyzed loop has no reachable normal exit.
                path.live = false;
                return Ok(());
            }
            return self.havoc(path, info, span);
        };
        self.resolution.charge(state.represented.len(), span)?;
        let represented: HashSet<_> = state.represented.iter().copied().collect();
        self.resolution.charge(path.env.len(), span)?;
        path.env.retain(|local, _| represented.contains(local));
        self.resolution.charge(path.declared.len(), span)?;
        let locals: Vec<_> = path.declared.iter().copied().collect();
        for local in &locals {
            self.resolution.charge(1, span)?;
            if represented.contains(local)
                && (info.modified.contains(local) || !path.env.contains_key(local))
            {
                let value = self.fresh_loop_value(*local, &path.guard, span)?;
                path.env.insert(*local, value);
            }
        }
        self.bind_ownership(path, state, span)
    }

    pub(super) fn after_ownership_join(
        &mut self,
        path: &mut Path,
        statement: usize,
        span: SpanId,
    ) -> R<()> {
        if path.live {
            if let Some(state) = self.resolution.after_state(statement, span)? {
                self.bind_ownership(path, state, span)?;
            }
        }
        Ok(())
    }

    pub(super) fn after_loop_breaks(&mut self, path: &mut Path, lp: &Loop, span: SpanId) -> R<()> {
        if path.live {
            if let Some(state) = self.resolution.exit_state(lp.id, span)? {
                self.bind_ownership(path, state, span)?;
            }
        }
        Ok(())
    }

    pub(super) fn joined_ownership(&self, paths: &[&Path], span: SpanId) -> R<JoinedOwnership> {
        let mut moved = Vec::new();
        let mut escaped = Vec::new();
        let mut seen_moved = HashSet::new();
        let mut seen_escaped = HashSet::new();
        let mut loans = Vec::new();
        for path in paths {
            self.price_ownership_path(path, 1, span)?;
            for place in &path.moved {
                if seen_moved.insert(place) {
                    moved.push(place.clone());
                }
            }
            for place in &path.escaped_loans {
                if seen_escaped.insert(place) {
                    escaped.push(place.clone());
                }
            }
            for loan in &path.loans {
                if !self.reference_resolved(path, &loan.reference)? {
                    loans.push(loan.clone());
                }
            }
        }
        let mut resolved = Vec::new();
        if let Some(first) = paths.first() {
            for term in &first.resolved {
                let mut common = true;
                for path in &paths[1..] {
                    let mut found = false;
                    for candidate in &path.resolved {
                        self.price_ownership_term(term, span)?;
                        self.price_ownership_term(candidate, span)?;
                        found |= candidate == term;
                    }
                    common &= found;
                }
                if common {
                    self.price_ownership_term(term, span)?;
                    resolved.push(term.clone());
                }
            }
        }
        Ok(JoinedOwnership {
            moved,
            loans,
            escaped,
            resolved,
        })
    }
}
