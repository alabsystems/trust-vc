//! Same-context mode observations needed by a future native shadow check.
//!
//! These are neither borrow-check results nor permission to admit references.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
mod index;
mod queries;
mod types;
pub(crate) use types::{
    AccessKind, AdjustmentKind, AdjustmentUse, ArgumentUse, Operation, PlaceUse,
    ReborrowDisposition, ReborrowPhase, ReborrowUse, VarErasure,
};

/// No serialization or cross-context constructor is provided. Every source
/// expression and binding is checked against the original compiler allocation.
#[derive(Clone)]
pub(crate) struct AvailabilityFacts<'tcx> {
    tcx: TyCtxt<'tcx>,
    definition: LocalDefId,
    owner: LocalDefId,
    new_mut_ref: bool,
    body: Option<&'tcx hir::Body<'tcx>>,
    nodes: HashMap<HirId, &'tcx hir::Expr<'tcx>>,
    uses: Vec<PlaceUse>,
    use_positions: HashMap<(HirId, AccessKind), usize>,
    arguments: Vec<ArgumentUse>,
    argument_positions: HashMap<(HirId, usize), usize>,
    operations: Vec<Operation>,
    operation_positions: HashMap<HirId, usize>,
    adjustments: Vec<AdjustmentUse>,
    adjustment_positions: HashMap<HirId, usize>,
}

impl std::fmt::Debug for AvailabilityFacts<'_> {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        out.debug_struct("AvailabilityFacts")
            .field("definition", &self.definition)
            .field("owner", &self.owner)
            .field("new_mut_ref", &self.new_mut_ref())
            .field("uses", &self.uses())
            .field("arguments", &self.arguments())
            .field("operations", &self.operations())
            .field("adjustments", &self.adjustments())
            .finish_non_exhaustive()
    }
}

impl<'tcx> AvailabilityFacts<'tcx> {
    pub(super) fn new(
        tcx: TyCtxt<'tcx>,
        definition: LocalDefId,
        owner: LocalDefId,
        new_mut_ref: bool,
    ) -> Self {
        Self {
            tcx,
            definition,
            owner,
            new_mut_ref,
            body: tcx.hir_maybe_body_owned_by(owner),
            nodes: HashMap::new(),
            uses: Vec::new(),
            use_positions: HashMap::new(),
            arguments: Vec::new(),
            argument_positions: HashMap::new(),
            operations: Vec::new(),
            operation_positions: HashMap::new(),
            adjustments: Vec::new(),
            adjustment_positions: HashMap::new(),
        }
    }

    /// Constant-scope current native allocation join. Completed table/index
    /// validation remains in checked(); indexed consumers use this only after
    /// the canonical whole-body producer has validated those immutable rows.
    pub(crate) fn in_context(
        &self,
        tcx: TyCtxt<'tcx>,
        definition: LocalDefId,
        owner: LocalDefId,
    ) -> Result<(), String> {
        if !std::ptr::eq(*tcx, *self.tcx)
            || definition != self.definition
            || owner != self.owner
            || tcx.dcx().has_errors().is_some()
            || crate::reader::function_identity_observer::body_is_quarantined(tcx.sess, owner)
        {
            return Err("availability modes belong to another compiler context or owner".into());
        }
        let body = self
            .body
            .ok_or("availability modes have no original body")?;
        let original = tcx
            .lower_to_hir(body.id().hir_id.owner.def_id)
            .as_owner()
            .and_then(|raw| raw.nodes.bodies.get(&body.id().hir_id.local_id).copied())
            .ok_or("availability modes lost their original lowered body")?;
        if !std::ptr::eq(body, original)
            || !tcx
                .hir_maybe_body_owned_by(owner)
                .is_some_and(|current| std::ptr::eq(body, current))
        {
            return Err("availability modes do not belong to the original body allocation".into());
        }
        Ok(())
    }

    pub(crate) fn checked(
        &self,
        tcx: TyCtxt<'tcx>,
        definition: LocalDefId,
        owner: LocalDefId,
    ) -> Result<&Self, String> {
        self.checked_using(tcx, definition, owner, |_| Ok(()))
    }

    pub(crate) fn checked_with_work(
        &self,
        tcx: TyCtxt<'tcx>,
        definition: LocalDefId,
        owner: LocalDefId,
        remaining: &mut usize,
    ) -> Result<&Self, String> {
        self.checked_using(tcx, definition, owner, |amount| {
            *remaining = remaining
                .checked_sub(amount)
                .ok_or("availability validation exceeds the caller's shared work bound")?;
            Ok(())
        })
    }

    fn checked_using(
        &self,
        tcx: TyCtxt<'tcx>,
        definition: LocalDefId,
        owner: LocalDefId,
        mut charge: impl FnMut(usize) -> Result<(), String>,
    ) -> Result<&Self, String> {
        charge(1)?;
        self.in_context(tcx, definition, owner)?;
        let body = self
            .body
            .ok_or("availability modes have no original body")?;
        // index::validate visits each physical row once. Price that exact
        // traversal before entering it; the native joins below stay intact.
        charge(self.uses.len())?;
        index::validate(&self.uses, &self.use_positions, |row| {
            (row.place, row.access)
        })?;
        charge(self.arguments.len())?;
        index::validate(&self.arguments, &self.argument_positions, |row| {
            (row.call, row.position)
        })?;
        charge(self.operations.len())?;
        index::validate(&self.operations, &self.operation_positions, |row| {
            row.expression
        })?;
        charge(self.adjustments.len())?;
        index::validate(&self.adjustments, &self.adjustment_positions, |row| {
            row.expression
        })?;
        for (id, expected) in &self.nodes {
            charge(1)?;
            if !matches!(tcx.hir_node(*id), hir::Node::Expr(actual) if std::ptr::eq(actual, *expected))
            {
                return Err("an availability expression changed original HIR allocation".into());
            }
        }
        for usage in &self.uses {
            charge(1)?;
            if !matches!(tcx.hir_node(usage.binding), hir::Node::Pat(_))
                || usage.binding.owner != body.id().hir_id.owner
                || !self.nodes.contains_key(&usage.place)
                || !self.nodes.contains_key(&usage.local_use)
            {
                return Err("an availability place lost its actual native binding".into());
            }
            self.use_for(self.source(usage.place)?, usage.access)?;
        }
        for argument in &self.arguments {
            charge(1)?;
            self.argument_for(self.source(argument.call)?, argument.position)?;
        }
        for operation in &self.operations {
            charge(1)?;
            self.operation_for(self.source(operation.expression)?)?;
        }
        for adjustment in &self.adjustments {
            charge(1)?;
            self.adjustment_for(self.source(adjustment.expression)?)?;
        }
        Ok(self)
    }

    pub(crate) fn uses(&self) -> &[PlaceUse] {
        &self.uses
    }
    pub(crate) fn new_mut_ref(&self) -> bool {
        self.new_mut_ref
    }
    pub(crate) fn arguments(&self) -> &[ArgumentUse] {
        &self.arguments
    }
    pub(crate) fn operations(&self) -> &[Operation] {
        &self.operations
    }
    pub(crate) fn adjustments(&self) -> &[AdjustmentUse] {
        &self.adjustments
    }

    fn remember(&mut self, expression: &'tcx hir::Expr<'tcx>) -> Result<(), String> {
        if self
            .body
            .is_none_or(|body| expression.hir_id.owner != body.id().hir_id.owner)
        {
            return Err("availability expression is outside its original HIR body owner".into());
        }
        if !matches!(self.tcx.hir_node(expression.hir_id), hir::Node::Expr(actual) if std::ptr::eq(actual, expression))
        {
            return Err(
                "availability recording requires the actual original HIR expression".into(),
            );
        }
        if let Some(previous) = self.nodes.insert(expression.hir_id, expression) {
            if !std::ptr::eq(previous, expression) {
                return Err("contradictory availability source occurrences".into());
            }
        }
        Ok(())
    }

    pub(super) fn place(
        &mut self,
        place: &'tcx hir::Expr<'tcx>,
        local: &'tcx hir::Expr<'tcx>,
        usage: PlaceUse,
    ) -> Result<(), String> {
        self.remember(place)?;
        self.remember(local)?;
        index::insert(
            &mut self.uses,
            &mut self.use_positions,
            (usage.place, usage.access),
            usage,
            |row| (row.place, row.access),
            "contradictory modes for one availability access",
        )
    }

    pub(super) fn argument(
        &mut self,
        call: &'tcx hir::Expr<'tcx>,
        argument: &'tcx hir::Expr<'tcx>,
        position: usize,
        mode: Mode,
    ) -> Result<(), String> {
        self.remember(call)?;
        self.remember(argument)?;
        let actual = match call.kind {
            hir::ExprKind::Call(_, arguments) | hir::ExprKind::Tup(arguments) => {
                arguments.get(position)
            }
            hir::ExprKind::MethodCall(_, receiver, arguments, _) => {
                if position == 0 {
                    Some(receiver)
                } else {
                    arguments.get(position - 1)
                }
            }
            hir::ExprKind::Struct(_, fields, _) => fields.get(position).map(|field| field.expr),
            _ => None,
        };
        if !actual.is_some_and(|actual| std::ptr::eq(actual, argument)) {
            return Err(
                "availability argument does not belong to this physical native call".into(),
            );
        }
        let fact = ArgumentUse {
            call: call.hir_id,
            argument: argument.hir_id,
            position,
            mode,
            erased: mode == Mode::Spec,
        };
        index::insert(
            &mut self.arguments,
            &mut self.argument_positions,
            (fact.call, fact.position),
            fact,
            |row| (row.call, row.position),
            "contradictory availability argument modes",
        )
    }

    pub(super) fn operation(
        &mut self,
        expression: &'tcx hir::Expr<'tcx>,
        place: &'tcx hir::Expr<'tcx>,
        kind: AccessKind,
        place_mode: Mode,
        mode: Mode,
    ) -> Result<(), String> {
        self.remember(expression)?;
        self.remember(place)?;
        let actual = match &expression.kind {
            hir::ExprKind::Assign(lhs, _, _) | hir::ExprKind::AssignOp(_, lhs, _)
                if kind == AccessKind::Assign =>
            {
                Some(*lhs)
            }
            hir::ExprKind::AddrOf(hir::BorrowKind::Ref, rustc_ast::Mutability::Mut, inner)
                if kind == AccessKind::MutBorrow =>
            {
                Some(*inner)
            }
            _ => None,
        };
        if !actual.is_some_and(|actual| std::ptr::eq(actual, place)) {
            return Err("availability operation does not own this native place".into());
        }
        let fact = Operation {
            expression: expression.hir_id,
            place: place.hir_id,
            kind,
            place_mode,
            mode,
        };
        index::insert(
            &mut self.operations,
            &mut self.operation_positions,
            fact.expression,
            fact,
            |row| row.expression,
            "contradictory availability operation modes",
        )
    }

    pub(super) fn adjustment(
        &mut self,
        expression: &'tcx hir::Expr<'tcx>,
        kinds: Vec<AdjustmentKind>,
        reborrow: Option<ReborrowUse>,
    ) -> Result<(), String> {
        self.remember(expression)?;
        let fact = AdjustmentUse {
            expression: expression.hir_id,
            kinds,
            reborrow,
        };
        index::insert(
            &mut self.adjustments,
            &mut self.adjustment_positions,
            fact.expression,
            fact,
            |row| row.expression,
            "contradictory availability adjustment kinds",
        )
    }
}
