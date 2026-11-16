//! Exact occurrence lookups: missing facts never receive a default mode.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

impl<'tcx> AvailabilityFacts<'tcx> {
    pub(super) fn source(&self, id: HirId) -> Result<&'tcx hir::Expr<'tcx>, String> {
        self.nodes
            .get(&id)
            .copied()
            .ok_or_else(|| "a recorded availability source occurrence is missing".into())
    }
    fn contains(&self, expression: &hir::Expr<'_>) -> Result<(), String> {
        if !self
            .nodes
            .get(&expression.hir_id)
            .is_some_and(|actual| std::ptr::eq(*actual, expression))
        {
            return Err("the requested native occurrence has no checked availability facts".into());
        }
        Ok(())
    }

    /// First call `checked` in the consuming compiler context. A listed slice
    /// is not a coverage claim; consumers must look up every required access.
    pub(crate) fn use_for(
        &self,
        expression: &hir::Expr<'_>,
        access: AccessKind,
    ) -> Result<&PlaceUse, String> {
        self.contains(expression)?;
        index::get(
            &self.uses,
            &self.use_positions,
            &(expression.hir_id, access),
            |row| (row.place, row.access),
        )?
        .ok_or_else(|| "the requested access has no checked availability mode".into())
    }

    pub(crate) fn argument_for(
        &self,
        call: &hir::Expr<'_>,
        position: usize,
    ) -> Result<&ArgumentUse, String> {
        self.contains(call)?;
        index::get(
            &self.arguments,
            &self.argument_positions,
            &(call.hir_id, position),
            |row| (row.call, row.position),
        )?
        .ok_or_else(|| "the requested argument has no checked erasure mode".into())
    }

    pub(crate) fn operation_for(&self, expression: &hir::Expr<'_>) -> Result<&Operation, String> {
        self.contains(expression)?;
        index::get(
            &self.operations,
            &self.operation_positions,
            &expression.hir_id,
            |row| row.expression,
        )?
        .ok_or_else(|| "the requested operation has no checked availability mode".into())
    }

    pub(crate) fn adjustment_for(
        &self,
        expression: &hir::Expr<'_>,
    ) -> Result<&AdjustmentUse, String> {
        self.contains(expression)?;
        index::get(
            &self.adjustments,
            &self.adjustment_positions,
            &expression.hir_id,
            |row| row.expression,
        )?
        .ok_or_else(|| "the requested adjustment has no checked availability interpretation".into())
    }
}
