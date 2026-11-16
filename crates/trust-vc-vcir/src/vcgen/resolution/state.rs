// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Finite place ownership states and the single shared analysis budget.
use super::*;
use crate::SpanId;
use std::cell::Cell;
use std::collections::HashMap;
use std::rc::Rc;

pub(super) fn place_order(left: &Place, right: &Place) -> std::cmp::Ordering {
    fn projection(value: &Projection) -> (u8, u32, u32) {
        match value {
            Projection::Deref => (0, 0, 0),
            Projection::TupleField(index) => (1, *index, 0),
            Projection::Field { variant, field } => (2, *variant, *field),
        }
    }
    left.local.0.cmp(&right.local.0).then_with(|| {
        left.projections
            .iter()
            .map(projection)
            .cmp(right.projections.iter().map(projection))
    })
}

#[derive(Clone)]
pub(super) struct Work(Rc<Cell<usize>>);

impl Work {
    pub(super) fn new() -> Self {
        Self(Rc::new(Cell::new(200_000)))
    }
    pub(super) fn remaining(&self) -> &Cell<usize> {
        self.0.as_ref()
    }
    pub(super) fn charge(&self, amount: usize, span: SpanId) -> R<()> {
        let remaining = self.0.get().checked_sub(amount).ok_or_else(|| {
            refusal(
                "resolution-size",
                "owned-value resolution work exhausted",
                span,
            )
        })?;
        self.0.set(remaining);
        Ok(())
    }
    pub(super) fn places(&self, places: &[Place], span: SpanId) -> R<()> {
        for place in places {
            self.charge(1 + place.projections.len(), span)?;
        }
        Ok(())
    }
    pub(super) fn ty(&self, ty: &Ty, span: SpanId, depth: usize) -> R<()> {
        self.charge(1, span)?;
        if depth > 64 {
            return Err(refusal(
                "resolution-type",
                "owned type pricing depth exhausted",
                span,
            ));
        }
        match ty {
            Ty::Tuple(fields) | Ty::Adt(_, fields) => {
                for field in fields {
                    self.ty(field, span, depth + 1)?;
                }
            }
            Ty::MutRef(inner) | Ty::Ref { inner, .. } => self.ty(inner, span, depth + 1)?,
            _ => {}
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(in crate::vcgen) struct OwnershipState {
    pub(in crate::vcgen) declared: Vec<LocalId>,
    pub(in crate::vcgen) represented: Vec<LocalId>,
    pub(in crate::vcgen) initialized: Vec<Place>,
    pub(in crate::vcgen) moved: Vec<Place>,
    pub(in crate::vcgen) loans: HashMap<Place, Vec<Place>>,
    /// Complete known pointee alternatives. Absence means unknown, so joins
    /// cannot create this row from a known alternative and an unknown one.
    pub(in crate::vcgen) aliases: HashMap<Place, Vec<Place>>,
    pub(in crate::vcgen) escaped: Vec<Place>,
    pub(super) pending_call: Option<PendingCall>,
}

impl OwnershipState {
    pub(super) fn copy(&self, work: &Work, span: SpanId) -> R<Self> {
        self.price(work, span)?;
        Ok(self.clone())
    }
    pub(super) fn price(&self, work: &Work, span: SpanId) -> R<()> {
        work.charge(
            1 + self.declared.len() + self.represented.len() + self.loans.len(),
            span,
        )?;
        work.places(&self.initialized, span)?;
        work.places(&self.moved, span)?;
        work.places(&self.escaped, span)?;
        for relation in [&self.loans, &self.aliases] {
            for (owner, footprints) in relation {
                work.charge(1 + owner.projections.len(), span)?;
                work.places(footprints, span)?;
            }
        }
        if let Some(pending) = &self.pending_call {
            pending.price(work, span)?;
        }
        Ok(())
    }
    pub(super) fn is_initialized(&self, place: &Place) -> bool {
        self.initialized.contains(place)
    }
}

#[derive(Default)]
pub(in crate::vcgen) struct Plan {
    pub(in crate::vcgen) before: HashMap<usize, Vec<Place>>,
    pub(in crate::vcgen) before_tail: HashMap<usize, Vec<Place>>,
    pub(in crate::vcgen) loops: HashMap<LoopId, Vec<Place>>,
    pub(in crate::vcgen) heads: HashMap<LoopId, OwnershipState>,
    pub(in crate::vcgen) exits: HashMap<LoopId, OwnershipState>,
    pub(in crate::vcgen) after: HashMap<usize, OwnershipState>,
    pub(in crate::vcgen) places: Vec<Place>,
    blocks: HashMap<usize, Vec<Place>>,
    work: Option<Work>,
}

impl Plan {
    pub(super) fn new(work: Work, places: Vec<Place>) -> Self {
        Self {
            work: Some(work),
            places,
            ..Self::default()
        }
    }
    pub(in crate::vcgen) fn charge(&self, amount: usize, span: SpanId) -> R<()> {
        self.work
            .as_ref()
            .map_or(Ok(()), |work| work.charge(amount, span))
    }
    pub(in crate::vcgen) fn remaining(&self) -> Option<&Cell<usize>> {
        self.work.as_ref().map(|work| work.0.as_ref())
    }
    fn copy(&self, state: Option<&OwnershipState>, span: SpanId) -> R<Option<OwnershipState>> {
        match (state, &self.work) {
            (Some(state), Some(work)) => state.copy(work, span).map(Some),
            (None, _) => Ok(None),
            (Some(_), None) => Err(refusal(
                "resolution-state",
                "ownership state has no analysis budget",
                span,
            )),
        }
    }
    pub(in crate::vcgen) fn head_state(
        &self,
        id: LoopId,
        span: SpanId,
    ) -> R<Option<OwnershipState>> {
        self.copy(self.heads.get(&id), span)
    }
    pub(in crate::vcgen) fn exit_state(
        &self,
        id: LoopId,
        span: SpanId,
    ) -> R<Option<OwnershipState>> {
        self.copy(self.exits.get(&id), span)
    }
    pub(in crate::vcgen) fn after_state(
        &self,
        statement: usize,
        span: SpanId,
    ) -> R<Option<OwnershipState>> {
        self.copy(self.after.get(&statement), span)
    }
    pub(in crate::vcgen) fn loop_points(&self, id: LoopId, span: SpanId) -> R<Vec<Place>> {
        let places = self.loops.get(&id).map_or(&[][..], Vec::as_slice);
        if let Some(work) = &self.work {
            work.places(places, span)?;
        }
        Ok(places.to_vec())
    }
    pub(in crate::vcgen) fn block_points(&self, block: usize, span: SpanId) -> R<Vec<Place>> {
        let places = self.blocks.get(&block).map_or(&[][..], Vec::as_slice);
        if let Some(work) = &self.work {
            work.places(places, span)?;
        }
        Ok(places.to_vec())
    }
    pub(in crate::vcgen) fn before_points(&self, statement: usize, span: SpanId) -> R<Vec<Place>> {
        let places = self.before.get(&statement).map_or(&[][..], Vec::as_slice);
        if let Some(work) = &self.work {
            work.places(places, span)?;
        }
        Ok(places.to_vec())
    }
    pub(in crate::vcgen) fn tail_points(&self, statement: usize, span: SpanId) -> R<Vec<Place>> {
        let places = self
            .before_tail
            .get(&statement)
            .map_or(&[][..], Vec::as_slice);
        if let Some(work) = &self.work {
            work.places(places, span)?;
        }
        Ok(places.to_vec())
    }
    pub(super) fn record_block(&mut self, block: usize, places: Vec<Place>) {
        self.blocks.insert(block, places);
    }
}
