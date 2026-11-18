// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A discarded normal result drops its owned outer carrier, not its referent.
use super::*;
use crate::vcgen::call_identity;

impl Gen<'_> {
    pub(super) fn drop_identity_result(
        &mut self,
        path: &Path,
        target: &FnDecl,
        result_type: &Ty,
        result: &Val,
        span: SpanId,
    ) -> R<()> {
        let summary = {
            let Some(work) = self.resolution.remaining() else {
                // The old no-owned-work path never acquires a fresh grant.
                return Ok(());
            };
            call_identity::derive(target, self.ctx, work, span)?
        };
        for binding in summary.bindings {
            let fact = {
                let Some(work) = self.resolution.remaining() else {
                    return Err(refusal(
                        "call-result-type",
                        "identity result lost its work context",
                        span,
                    ));
                };
                let Some(ty) =
                    call_identity::slot_type(self.ctx, result_type, &binding.result, work, span)?
                else {
                    return Err(refusal(
                        "call-result-type",
                        "invalid returned identity slot",
                        span,
                    ));
                };
                if !matches!(ty, Ty::MutRef(_)) {
                    return Err(refusal(
                        "call-result-type",
                        "a returned identity is not a mutable reference",
                        span,
                    ));
                }
                super::super::inline_work::value(work, result, 1, span)?;
                // The actual callee return ID is only a typed projection cursor;
                // it is never installed as a local in the caller's ownership state.
                let place = Place {
                    local: target.ret,
                    projections: binding.result,
                };
                let value = super::super::expr::project(
                    self.ctx,
                    &self.types,
                    result,
                    result_type,
                    &place,
                    span,
                    Some(work),
                )?;
                self.ctx.has_resolved_with_work(&ty, &self.types, value, span, work)?
            };
            // Receipt has completed the argument moves. The unused outer
            // result is initialized and has no future move or mutation.
            // In particular this never resolves a value behind its Deref.
            self.fact(&path.guard, Source::Axiom, fact);
        }
        Ok(())
    }
}
