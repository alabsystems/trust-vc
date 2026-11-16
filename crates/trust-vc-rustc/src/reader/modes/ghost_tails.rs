//! Raw proof-wrapper modes retained from the completed native mode walk.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashMap;

use rustc_hir::def_id::LocalDefId;
use rustc_hir::{self as hir, HirId};
use rustc_middle::ty::TyCtxt;
use trust_vc_vcir::{FnId, Mode, SpanId};

#[derive(Clone, Debug)]
struct Tail<'tcx> {
    proof: &'tcx hir::Expr<'tcx>,
    tail: &'tcx hir::Expr<'tcx>,
    mode: Mode,
}

/// Native source facts, not an independently usable verification capability.
/// They retain the actual compiler context and original body allocation.
#[derive(Clone)]
pub(in crate::reader) struct GhostTailFacts<'tcx> {
    tcx: TyCtxt<'tcx>,
    definition: LocalDefId,
    owner: LocalDefId,
    body: Option<&'tcx hir::Body<'tcx>>,
    tails: HashMap<HirId, Tail<'tcx>>,
}

impl std::fmt::Debug for GhostTailFacts<'_> {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        out.debug_struct("GhostTailFacts")
            .field("definition", &self.definition)
            .field("owner", &self.owner)
            .field("body", &self.body.map(rustc_hir::Body::id))
            .field("tails", &self.tails.len())
            .finish_non_exhaustive()
    }
}

/// One physical lowering occurrence. Order and multiplicity are preserved;
/// equal source spans never merge different original HIR nodes.
#[derive(Debug)]
pub(in crate::reader) struct ExpectedGhostTail {
    pub(in crate::reader) function: FnId,
    pub(in crate::reader) span: SpanId,
    definition: LocalDefId,
    owner: LocalDefId,
    proof: HirId,
    tail: HirId,
}

impl ExpectedGhostTail {
    pub(in crate::reader) fn definition(&self) -> LocalDefId {
        self.definition
    }
}

impl<'tcx> GhostTailFacts<'tcx> {
    pub(in crate::reader) fn new(
        tcx: TyCtxt<'tcx>,
        definition: LocalDefId,
        owner: LocalDefId,
    ) -> Self {
        Self {
            tcx,
            definition,
            owner,
            body: tcx.hir_maybe_body_owned_by(owner),
            tails: HashMap::new(),
        }
    }

    fn current(
        &self,
        tcx: TyCtxt<'tcx>,
        definition: LocalDefId,
        owner: LocalDefId,
    ) -> Result<(), String> {
        if !std::ptr::eq(*self.tcx, *tcx)
            || definition != self.definition
            || owner != self.owner
            || tcx.dcx().has_errors().is_some()
            || crate::reader::function_identity_observer::body_is_quarantined(tcx.sess, owner)
        {
            return Err("the checked ghost-tail compiler context or owner changed".into());
        }
        let body = self
            .body
            .ok_or("a checked ghost tail has no original body")?;
        if body.id().hir_id.owner.def_id != self.owner {
            return Err("the checked body belongs to another native HIR owner".into());
        }
        let current = tcx
            .hir_maybe_body_owned_by(owner)
            .ok_or("the checked native body disappeared")?;
        let original = tcx
            .lower_to_hir(owner)
            .as_owner()
            .and_then(|raw| raw.nodes.bodies.get(&body.id().hir_id.local_id).copied())
            .ok_or("the ghost tail is outside its original owner body")?;
        if !std::ptr::eq(body, current) || !std::ptr::eq(body, original) {
            return Err("the ghost-tail body is not the checked original allocation".into());
        }
        Ok(())
    }

    fn nodes(
        &self,
        proof: &'tcx hir::Expr<'tcx>,
        tail: &'tcx hir::Expr<'tcx>,
    ) -> Result<(), String> {
        self.current(self.tcx, self.definition, self.owner)?;
        if proof.hir_id.owner.def_id != self.owner
            || tail.hir_id.owner.def_id != self.owner
            || !matches!(self.tcx.hir_node(proof.hir_id), hir::Node::Expr(actual) if std::ptr::eq(actual, proof))
            || !matches!(self.tcx.hir_node(tail.hir_id), hir::Node::Expr(actual) if std::ptr::eq(actual, tail))
        {
            return Err("the checked ghost-tail nodes changed original HIR owners".into());
        }
        let hir::ExprKind::Block(block, None) = proof.kind else {
            return Err("a checked ghost wrapper is no longer its native block".into());
        };
        if !block.expr.is_some_and(|actual| std::ptr::eq(actual, tail)) {
            return Err("the checked ghost wrapper no longer owns this exact tail".into());
        }
        Ok(())
    }

    pub(super) fn record(
        &mut self,
        proof: &'tcx hir::Expr<'tcx>,
        block: &'tcx hir::Block<'tcx>,
        mode: Mode,
    ) -> Result<(), String> {
        let Some(tail) = block.expr else {
            return Ok(());
        };
        self.nodes(proof, tail)?;
        if !matches!(proof.kind, hir::ExprKind::Block(actual, None) if std::ptr::eq(actual, block))
        {
            return Err("the mode walk's proof block allocation changed".into());
        }
        if let Some(previous) = self.tails.get(&proof.hir_id) {
            if previous.mode != mode
                || !std::ptr::eq(previous.proof, proof)
                || !std::ptr::eq(previous.tail, tail)
            {
                return Err("contradictory native raw ghost-tail modes".into());
            }
        } else {
            self.tails.insert(proof.hir_id, Tail { proof, tail, mode });
        }
        Ok(())
    }

    pub(in crate::reader) fn expected(
        &self,
        tcx: TyCtxt<'tcx>,
        definition: LocalDefId,
        owner: LocalDefId,
        proof: &'tcx hir::Expr<'tcx>,
        tail: &'tcx hir::Expr<'tcx>,
        location: (FnId, SpanId),
    ) -> Result<ExpectedGhostTail, String> {
        self.current(tcx, definition, owner)?;
        self.nodes(proof, tail)?;
        let fact = self
            .tails
            .get(&proof.hir_id)
            .ok_or("the completed mode walk did not check this ghost tail")?;
        if !std::ptr::eq(fact.proof, proof) || !std::ptr::eq(fact.tail, tail) {
            return Err("a different HIR occurrence supplied this ghost-tail mode".into());
        }
        Ok(ExpectedGhostTail {
            function: location.0,
            span: location.1,
            definition,
            owner,
            proof: proof.hir_id,
            tail: tail.hir_id,
        })
    }

    pub(in crate::reader) fn mode_for(
        &self,
        tcx: TyCtxt<'tcx>,
        expected: &ExpectedGhostTail,
    ) -> Result<Mode, String> {
        self.current(tcx, expected.definition, expected.owner)?;
        let fact = self
            .tails
            .get(&expected.proof)
            .ok_or("a lowered ghost tail lost its checked native occurrence")?;
        self.nodes(fact.proof, fact.tail)?;
        if fact.tail.hir_id != expected.tail {
            return Err("the lowered ghost tail names another original HIR expression".into());
        }
        Ok(fact.mode)
    }
}
