//! Current native language context, separate from modes and ownership.

use super::*;

/// A source classification retained by the completed walk. It grants no
/// signature, erasure, ownership or body permission.
#[derive(Clone)]
pub(crate) struct LanguageFacts<'tcx> {
    tcx: TyCtxt<'tcx>,
    definition: LocalDefId,
    owner: LocalDefId,
    function_mode: Mode,
    body: &'tcx hir::Body<'tcx>,
    typeck: &'tcx TypeckResults<'tcx>,
    attributes: &'tcx [rustc_attr_ir::Attribute],
    parsed: Vec<(VerusAttr, Span)>,
    legacy: bool,
}

impl std::fmt::Debug for LanguageFacts<'_> {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        out.debug_struct("LanguageFacts")
            .field("definition", &self.definition)
            .field("owner", &self.owner)
            .field("legacy", &self.legacy)
            .finish_non_exhaustive()
    }
}

impl<'tcx> LanguageFacts<'tcx> {
    pub(super) fn capture(
        cx: &dyn ModeContext<'tcx>,
        definition: LocalDefId,
        owner: LocalDefId,
    ) -> Result<Self, String> {
        let tcx = cx.tcx();
        let function_mode = cx
            .function_mode(definition.to_def_id())
            .ok_or("language context lacks an admitted native declaration")?;
        let body = tcx
            .hir_maybe_body_owned_by(owner)
            .ok_or("language context has no original native body")?;
        let attributes = tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner));
        if attributes.len() > 4096 {
            return Err("native language attribute inventory exceeds its bound".into());
        }
        let value = Self {
            tcx,
            definition,
            owner,
            function_mode,
            body,
            typeck: tcx.typeck(owner),
            attributes,
            parsed: attrs::verus_attrs(attributes),
            legacy: cx.legacy_function(definition),
        };
        value.checked(cx, definition, owner)?;
        Ok(value)
    }

    pub(crate) fn legacy(&self) -> bool {
        self.legacy
    }
    pub(super) fn function_mode(&self) -> Mode {
        self.function_mode
    }

    pub(super) fn checked(
        &self,
        cx: &dyn ModeContext<'tcx>,
        definition: LocalDefId,
        owner: LocalDefId,
    ) -> Result<(), String> {
        self.checked_using(cx, definition, owner, None)
    }

    pub(super) fn checked_with_work(
        &self,
        cx: &dyn ModeContext<'tcx>,
        definition: LocalDefId,
        owner: LocalDefId,
        remaining: &mut usize,
    ) -> Result<(), String> {
        *remaining = remaining
            .checked_sub(1)
            .ok_or("native language validation exceeds the caller's shared work bound")?;
        self.checked_using(cx, definition, owner, Some(remaining))
    }

    fn same_attributes(
        &self,
        attributes: &[rustc_attr_ir::Attribute],
        remaining: Option<&mut usize>,
    ) -> Result<bool, String> {
        match remaining {
            Some(work) => {
                let current = attrs::verus_attrs_with_work(attributes, work)?;
                attrs::charge_comparison(&self.parsed, &current, work)?;
                Ok(self.parsed == current)
            }
            None => Ok(self.parsed == attrs::verus_attrs(attributes)),
        }
    }

    fn checked_using(
        &self,
        cx: &dyn ModeContext<'tcx>,
        definition: LocalDefId,
        owner: LocalDefId,
        mut remaining: Option<&mut usize>,
    ) -> Result<(), String> {
        let tcx = cx.tcx();
        let attributes = tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner));
        if !std::ptr::eq(*tcx, *self.tcx)
            || definition != self.definition
            || owner != self.owner
            || cx.body_owner(definition) != Some(owner)
            || cx.function_mode(definition.to_def_id()) != Some(self.function_mode)
            || cx.legacy_function(definition) != self.legacy
            || tcx.dcx().has_errors().is_some()
            || self.typeck.tainted_by_errors.is_some()
            || !std::ptr::eq(self.typeck, tcx.typeck(owner))
            || !std::ptr::eq(self.attributes, attributes)
            || !self.same_attributes(attributes, remaining.as_deref_mut())?
            || crate::reader::function_identity_observer::body_is_quarantined(tcx.sess, owner)
        {
            return Err(
                "language context lost its current native declaration/body/typecheck join".into(),
            );
        }
        let original = tcx
            .lower_to_hir(self.body.id().hir_id.owner.def_id)
            .as_owner()
            .and_then(|raw| {
                raw.nodes
                    .bodies
                    .get(&self.body.id().hir_id.local_id)
                    .copied()
            })
            .ok_or("language context lost its original lowering allocation")?;
        if !std::ptr::eq(original, self.body)
            || !tcx
                .hir_maybe_body_owned_by(owner)
                .is_some_and(|body| std::ptr::eq(body, self.body))
            || self.legacy
                && (definition != owner
                    || match remaining.as_deref_mut() {
                        Some(work) => cx.declaration_attrs_with_work(owner, work)?.verus_macro,
                        None => cx.declaration_attrs(owner).verus_macro,
                    }
                    || !match remaining.as_deref_mut() {
                        Some(work) => {
                            crate::reader::legacy::eligible_with_work(tcx, definition, true, work)?
                        }
                        None => crate::reader::legacy::eligible(tcx, definition, true),
                    })
        {
            return Err(
                "language context does not describe the original eligible native owner".into(),
            );
        }
        Ok(())
    }
}

impl<'tcx> CheckedModes<'tcx> {
    /// Consumers still rejoin the canonical Rc and their own occurrence facts.
    pub(crate) fn legacy_context(
        &self,
        cx: &Cx<'tcx>,
        definition: LocalDefId,
        owner: LocalDefId,
    ) -> Result<bool, String> {
        let language = self
            .language
            .as_ref()
            .ok_or("mode facts have no body-language observation")?;
        language.checked(cx, definition, owner)?;
        Ok(language.legacy())
    }

    pub(crate) fn legacy_context_with_work(
        &self,
        cx: &Cx<'tcx>,
        definition: LocalDefId,
        owner: LocalDefId,
        remaining: &mut usize,
    ) -> Result<bool, String> {
        let language = self
            .language
            .as_ref()
            .ok_or("mode facts have no body-language observation")?;
        language.checked_with_work(cx, definition, owner, remaining)?;
        Ok(language.legacy())
    }
}

#[cfg(test)]
mod tests;
