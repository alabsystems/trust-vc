//! Completed source expression observations for native ownership translation.
//!
//! These are mode/type data. They neither describe a finished erasure nor
//! establish that the compiler has checked any ownership shadow.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ExpressionContext {
    pub(crate) outer: Mode,
    pub(crate) expected: Mode,
    pub(crate) pure: bool,
    pub(crate) proof_in_spec: bool,
    pub(crate) assert_by: bool,
    /// Block classification is distinct from logical outer/expected modes.
    pub(crate) block_ghost: bool,
    pub(crate) uses_ghost_blocks: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct ExpressionMode<'tcx> {
    pub(crate) expression: &'tcx hir::Expr<'tcx>,
    pub(crate) context: ExpressionContext,
    pub(crate) result: Mode,
    pub(crate) native_type: ty::Ty<'tcx>,
    pub(crate) adjusted_type: ty::Ty<'tcx>,
}

#[derive(Clone)]
pub(crate) struct ExpressionFacts<'tcx> {
    tcx: TyCtxt<'tcx>,
    definition: LocalDefId,
    owner: LocalDefId,
    body: Option<&'tcx hir::Body<'tcx>>,
    typeck: Option<&'tcx TypeckResults<'tcx>>,
    failure: Option<String>,
    observations: HashMap<HirId, Vec<ExpressionMode<'tcx>>>,
}

impl std::fmt::Debug for ExpressionFacts<'_> {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        out.debug_struct("ExpressionFacts")
            .field("definition", &self.definition)
            .field("owner", &self.owner)
            .field("expressions", &self.observations.len())
            .finish_non_exhaustive()
    }
}

impl<'tcx> ExpressionFacts<'tcx> {
    pub(super) fn new(tcx: TyCtxt<'tcx>, definition: LocalDefId, owner: LocalDefId) -> Self {
        let body = tcx.hir_maybe_body_owned_by(owner);
        Self {
            tcx,
            definition,
            owner,
            body,
            typeck: body.map(|_| tcx.typeck(owner)),
            failure: None,
            observations: HashMap::new(),
        }
    }

    fn current(
        &self,
        tcx: TyCtxt<'tcx>,
        definition: LocalDefId,
        owner: LocalDefId,
    ) -> Result<(), String> {
        if !std::ptr::eq(*tcx, *self.tcx)
            || definition != self.definition
            || owner != self.owner
            || tcx.dcx().has_errors().is_some()
            || self
                .typeck
                .is_some_and(|typeck| typeck.tainted_by_errors.is_some())
            || !self
                .typeck
                .is_some_and(|typeck| std::ptr::eq(typeck, tcx.typeck(owner)))
            || crate::reader::function_identity_observer::body_is_quarantined(tcx.sess, owner)
        {
            return Err("expression modes belong to another current native context".into());
        }
        let body = self
            .body
            .ok_or("expression modes have no native source body")?;
        let original = tcx
            .lower_to_hir(body.id().hir_id.owner.def_id)
            .as_owner()
            .and_then(|raw| raw.nodes.bodies.get(&body.id().hir_id.local_id).copied())
            .ok_or("expression modes lost the original lowering allocation")?;
        if !std::ptr::eq(body, original)
            || !tcx
                .hir_maybe_body_owned_by(owner)
                .is_some_and(|actual| std::ptr::eq(actual, body))
        {
            return Err("expression modes do not describe the original source body".into());
        }
        Ok(())
    }

    pub(super) fn record(
        &mut self,
        expression: &'tcx hir::Expr<'tcx>,
        context: ExpressionContext,
        result: Mode,
    ) -> Result<(), String> {
        self.current(self.tcx, self.definition, self.owner)?;
        if expression.hir_id.owner.def_id != self.owner
            || !matches!(self.tcx.hir_node(expression.hir_id), hir::Node::Expr(actual) if std::ptr::eq(actual, expression))
        {
            return Err("expression modes require the actual original expression".into());
        }
        if self.observations.len() >= 262_144 && !self.observations.contains_key(&expression.hir_id)
        {
            return Err("expression observation inventory exceeds its bound".into());
        }
        let typeck = self
            .typeck
            .ok_or("expression modes have no native typecheck results")?;
        let native_type = typeck.expr_ty(expression);
        let adjusted_type = typeck.expr_ty_adjusted(expression);
        let rows = self.observations.entry(expression.hir_id).or_default();
        if let Some(previous) = rows.iter().find(|row| row.context == context) {
            if !std::ptr::eq(previous.expression, expression)
                || previous.result != result
                || previous.native_type != native_type
                || previous.adjusted_type != adjusted_type
            {
                return Err(
                    "one source expression has contradictory mode/type observations".into(),
                );
            }
            return Ok(());
        }
        if rows.len() >= 8 {
            return Err("one expression has too many distinct mode contexts".into());
        }
        rows.push(ExpressionMode {
            expression,
            context,
            result,
            native_type,
            adjusted_type,
        });
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
                .ok_or("expression validation exceeds the caller's shared work bound")?;
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
        if let Some(failure) = &self.failure {
            return Err(failure.clone());
        }
        self.current(tcx, definition, owner)?;
        let typeck = self
            .typeck
            .ok_or("expression modes have no native typecheck results")?;
        for rows in self.observations.values() {
            charge(1)?;
            for row in rows {
                charge(1)?;
                let expression = row.expression;
                if !matches!(tcx.hir_node(expression.hir_id), hir::Node::Expr(actual) if std::ptr::eq(actual, expression))
                    || typeck.expr_ty(expression) != row.native_type
                    || typeck.expr_ty_adjusted(expression) != row.adjusted_type
                {
                    return Err(
                        "a completed expression mode lost its native source/type join".into(),
                    );
                }
            }
        }
        Ok(self)
    }

    pub(crate) fn observations(&self) -> impl Iterator<Item = &ExpressionMode<'tcx>> {
        self.observations.values().flat_map(|rows| rows.iter())
    }

    /// Rejoin one actual source occurrence without rescanning the whole body
    /// for each declaration. Recording admits at most eight contexts per HIR
    /// occurrence; none of these observations grants ownership or erasure.
    pub(crate) fn for_expression(
        &self,
        tcx: TyCtxt<'tcx>,
        definition: LocalDefId,
        owner: LocalDefId,
        expression: &'tcx hir::Expr<'tcx>,
    ) -> Result<&[ExpressionMode<'tcx>], String> {
        if let Some(failure) = &self.failure {
            return Err(failure.clone());
        }
        self.current(tcx, definition, owner)?;
        if expression.hir_id.owner.def_id != owner
            || !matches!(tcx.hir_node(expression.hir_id), hir::Node::Expr(actual) if std::ptr::eq(actual, expression))
        {
            return Err("expression modes require the actual original occurrence".into());
        }
        let rows = self
            .observations
            .get(&expression.hir_id)
            .ok_or("the original expression has no completed mode observation")?;
        let typeck = self
            .typeck
            .ok_or("expression modes have no native typecheck results")?;
        if rows.is_empty()
            || rows.len() > 8
            || rows.iter().any(|row| {
                !std::ptr::eq(row.expression, expression)
                    || typeck.expr_ty(expression) != row.native_type
                    || typeck.expr_ty_adjusted(expression) != row.adjusted_type
            })
        {
            return Err("the expression mode lost its current occurrence/type join".into());
        }
        Ok(rows)
    }
}

impl<'tcx> Checker<'_, 'tcx> {
    pub(super) fn expression_context(&self, outer: Mode, expected: Mode) -> ExpressionContext {
        ExpressionContext {
            outer,
            expected,
            pure: self.in_pure,
            proof_in_spec: self.in_proof_in_spec,
            assert_by: self.in_assert_by,
            block_ghost: self.block == Ghostness::Ghost,
            uses_ghost_blocks: self.uses_ghost_blocks(),
        }
    }

    pub(super) fn record_expression_mode(
        &mut self,
        expression: &'tcx hir::Expr<'tcx>,
        context: ExpressionContext,
        result: Mode,
    ) -> M<Mode> {
        // Auxiliary ownership data never changes an existing mode verdict.
        // A failed/incomplete inventory cannot construct a shadow plan.
        if self.expressions.failure.is_none() {
            if let Err(detail) = self.expressions.record(expression, context, result) {
                self.expressions.failure = Some(detail);
            }
        }
        Ok(result)
    }
}
