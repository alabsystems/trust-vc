//! Completed modes of original native value-pattern bindings.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[derive(Clone, Debug)]
struct Binding<'tcx> {
    pattern: &'tcx hir::Pat<'tcx>,
    mode: Mode,
}

/// These observations retain their compiler context and original body. A
/// matching HIR id alone never authenticates a copied or foreign pattern.
#[derive(Clone)]
pub(crate) struct BindingFacts<'tcx> {
    tcx: TyCtxt<'tcx>,
    definition: LocalDefId,
    owner: LocalDefId,
    body: Option<&'tcx hir::Body<'tcx>>,
    bindings: HashMap<HirId, Binding<'tcx>>,
}

impl std::fmt::Debug for BindingFacts<'_> {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        out.debug_struct("BindingFacts")
            .field("definition", &self.definition)
            .field("owner", &self.owner)
            .field("bindings", &self.bindings)
            .finish_non_exhaustive()
    }
}

impl<'tcx> BindingFacts<'tcx> {
    pub(super) fn new(tcx: TyCtxt<'tcx>, definition: LocalDefId, owner: LocalDefId) -> Self {
        Self {
            tcx,
            definition,
            owner,
            body: tcx.hir_maybe_body_owned_by(owner),
            bindings: HashMap::new(),
        }
    }

    fn original(&self, pattern: &hir::Pat<'tcx>) -> Result<HirId, String> {
        let PatKind::Binding(BindingMode(ByRef::No, _), binding, _, None) = pattern.kind else {
            return Err("checked value modes require an actual plain binding pattern".into());
        };
        if pattern.hir_id.owner.def_id != self.owner
            || binding != pattern.hir_id
            || !matches!(self.tcx.hir_node(pattern.hir_id), hir::Node::Pat(actual) if std::ptr::eq(actual, pattern))
        {
            return Err("a checked binding is not its original native pattern allocation".into());
        }
        Ok(binding)
    }

    pub(super) fn record(
        &mut self,
        pattern: &'tcx hir::Pat<'tcx>,
        mode: Mode,
    ) -> Result<(), String> {
        let binding = self.original(pattern)?;
        if let Some(previous) = self.bindings.get(&binding) {
            if previous.mode != mode || !std::ptr::eq(previous.pattern, pattern) {
                return Err(
                    "a native binding has contradictory completed mode observations".into(),
                );
            }
            return Ok(());
        }
        self.bindings.insert(binding, Binding { pattern, mode });
        Ok(())
    }

    fn current(
        &self,
        tcx: TyCtxt<'tcx>,
        definition: LocalDefId,
        owner: LocalDefId,
    ) -> Result<&Self, String> {
        if !std::ptr::eq(*self.tcx, *tcx)
            || definition != self.definition
            || owner != self.owner
            || tcx.dcx().has_errors().is_some()
            || crate::reader::function_identity_observer::body_is_quarantined(tcx.sess, owner)
        {
            return Err("binding modes belong to another compiler context or owner".into());
        }
        let body = self.body.ok_or("binding modes have no original body")?;
        let original = tcx
            .lower_to_hir(owner)
            .as_owner()
            .and_then(|raw| raw.nodes.bodies.get(&body.id().hir_id.local_id).copied())
            .ok_or("binding modes lost their original lowered body")?;
        if body.id().hir_id.owner.def_id != owner
            || !std::ptr::eq(body, original)
            || !tcx
                .hir_maybe_body_owned_by(owner)
                .is_some_and(|actual| std::ptr::eq(body, actual))
        {
            return Err("binding modes do not belong to the original body allocation".into());
        }
        Ok(self)
    }

    pub(crate) fn checked(
        &self,
        tcx: TyCtxt<'tcx>,
        definition: LocalDefId,
        owner: LocalDefId,
    ) -> Result<&Self, String> {
        self.current(tcx, definition, owner)?;
        for (id, binding) in &self.bindings {
            if self.original(binding.pattern)? != *id {
                return Err("a checked binding changed its original HIR identity".into());
            }
        }
        Ok(self)
    }

    pub(crate) fn mode_for(
        &self,
        tcx: TyCtxt<'tcx>,
        definition: LocalDefId,
        owner: LocalDefId,
        body: &hir::Body<'tcx>,
        pattern: &hir::Pat<'tcx>,
    ) -> Result<Mode, String> {
        self.current(tcx, definition, owner)?;
        if !self
            .body
            .is_some_and(|original| std::ptr::eq(original, body))
        {
            return Err("the binding mode query replaced its original native body".into());
        }
        let binding = self.original(pattern)?;
        let observation = self
            .bindings
            .get(&binding)
            .ok_or("the actual native binding has no completed mode observation")?;
        if !std::ptr::eq(observation.pattern, pattern) {
            return Err("the binding mode names another pattern allocation".into());
        }
        Ok(observation.mode)
    }
}
