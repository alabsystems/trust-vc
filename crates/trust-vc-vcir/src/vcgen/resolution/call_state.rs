// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! One call's captures are distinct from escapes which predate that call.
use super::state::Work;
use super::*;
use crate::SpanId;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ReturnBinding {
    pub(super) result: Vec<Projection>,
    pub(super) parameter: usize,
    pub(super) argument: Vec<Projection>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct CapturedRow {
    pub(super) path: Vec<Projection>,
    pub(super) source: Option<Place>,
    pub(super) loans: Vec<Place>,
    pub(super) aliases: Option<Vec<Place>>,
    pub(super) survivors: Option<Vec<Place>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ExtraOrigin {
    pub(super) source: Place,
    pub(super) loans: Vec<Place>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct CapturedArgument {
    pub(super) parameter: usize,
    pub(super) rows: Vec<CapturedRow>,
    pub(super) extras: Vec<ExtraOrigin>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct PendingCall {
    pub(super) call: usize,
    pub(super) escaped_before: Vec<Place>,
    pub(super) bindings: Vec<ReturnBinding>,
    pub(super) arguments: Vec<CapturedArgument>,
}

impl PendingCall {
    pub(super) fn price(&self, work: &Work, span: SpanId) -> R<()> {
        work.charge(1 + self.bindings.len() + self.arguments.len(), span)?;
        work.places(&self.escaped_before, span)?;
        for binding in &self.bindings {
            work.charge(1 + binding.result.len() + binding.argument.len(), span)?;
        }
        for argument in &self.arguments {
            work.charge(1 + argument.rows.len() + argument.extras.len(), span)?;
            for row in &argument.rows {
                work.charge(1 + row.path.len(), span)?;
                if let Some(source) = &row.source {
                    work.places(std::slice::from_ref(source), span)?;
                }
                work.places(&row.loans, span)?;
                if let Some(aliases) = &row.aliases {
                    work.places(aliases, span)?;
                }
                if let Some(survivors) = &row.survivors {
                    work.places(survivors, span)?;
                }
            }
            for origin in &argument.extras {
                work.places(std::slice::from_ref(&origin.source), span)?;
                work.places(&origin.loans, span)?;
            }
        }
        Ok(())
    }
}

impl Builder<'_, '_> {
    pub(super) fn join_pending(
        &self,
        left: &mut Option<PendingCall>,
        right: &Option<PendingCall>,
    ) -> R<()> {
        let compatible = match (left.as_ref(), right.as_ref()) {
            (Some(left), Some(right)) => {
                left.price(&self.work, self.decl.span)?;
                right.price(&self.work, self.decl.span)?;
                left.call == right.call
                    && left.bindings == right.bindings
                    && left.arguments.len() == right.arguments.len()
                    && left
                        .arguments
                        .iter()
                        .zip(&right.arguments)
                        .all(|(left, right)| left.parameter == right.parameter)
            }
            _ => false,
        };
        if !compatible {
            *left = None;
            return Ok(());
        }
        let (Some(left), Some(right)) = (left.as_mut(), right.as_ref()) else {
            return Ok(());
        };
        self.union(&mut left.escaped_before, &right.escaped_before)?;
        for (argument, incoming) in left.arguments.iter_mut().zip(&right.arguments) {
            for row in &mut argument.rows {
                self.charge(incoming.rows.len().saturating_mul(1 + row.path.len()))?;
                if let Some(other) = incoming.rows.iter().find(|other| other.path == row.path) {
                    self.union(&mut row.loans, &other.loans)?;
                    self.join_complete(&mut row.aliases, &other.aliases)?;
                    self.join_complete(&mut row.survivors, &other.survivors)?;
                    if row.source != other.source {
                        row.source = None;
                    }
                } else {
                    row.aliases = None;
                    row.survivors = None;
                }
            }
            for row in &incoming.rows {
                self.charge(argument.rows.len().saturating_mul(1 + row.path.len()))?;
                if !argument.rows.iter().any(|old| old.path == row.path) {
                    self.price_row(row)?;
                    let mut row = row.clone();
                    row.aliases = None;
                    row.survivors = None;
                    argument.rows.push(row);
                }
            }
            for origin in &incoming.extras {
                self.charge(
                    argument
                        .extras
                        .len()
                        .saturating_mul(1 + origin.source.projections.len()),
                )?;
                if let Some(old) = argument
                    .extras
                    .iter_mut()
                    .find(|old| old.source == origin.source)
                {
                    self.union(&mut old.loans, &origin.loans)?;
                } else {
                    self.work
                        .places(std::slice::from_ref(&origin.source), self.decl.span)?;
                    self.work.places(&origin.loans, self.decl.span)?;
                    argument.extras.push(origin.clone());
                }
            }
        }
        Ok(())
    }

    fn join_complete(&self, left: &mut Option<Vec<Place>>, right: &Option<Vec<Place>>) -> R<()> {
        if let (Some(left), Some(right)) = (left.as_mut(), right.as_ref()) {
            self.union(left, right)?;
        } else {
            *left = None;
        }
        Ok(())
    }

    pub(super) fn price_row(&self, row: &CapturedRow) -> R<()> {
        self.charge(1 + row.path.len())?;
        if let Some(source) = &row.source {
            self.work
                .places(std::slice::from_ref(source), self.decl.span)?;
        }
        self.work.places(&row.loans, self.decl.span)?;
        if let Some(aliases) = &row.aliases {
            self.work.places(aliases, self.decl.span)?;
        }
        if let Some(survivors) = &row.survivors {
            self.work.places(survivors, self.decl.span)?;
        }
        Ok(())
    }
}
