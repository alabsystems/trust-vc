//! Native generic Copy premises, rather than a permission bit on an expression.
//!
//! The IR checks these as caller obligations after substitution. This packet
//! does not replace the real native mode, erasure or MIR ownership checks.
use super::*;

impl<'tcx> FnReader<'_, 'tcx> {
    pub(super) fn native_copy_premises(&self) -> R<Vec<Ty>> {
        // Existing mathematical/dual constants have no kept generic body to
        // license with this rule. Preserve their independently checked pure
        // initializer semantics rather than inventing an executable mode walk.
        if matches!(
            self.cx.constants.mode(self.def_id),
            Some(ConstMode::Spec | ConstMode::Dual)
        ) {
            return Ok(Vec::new());
        }
        let tcx = self.tcx;
        let span = tcx.def_span(self.body_def);
        let mut candidates = ty::GenericArgs::identity_for_item(tcx, self.body_def)
            .types()
            .collect::<Vec<_>>();
        // Also retain explicit compound requirements such as Wrapper<T>: Copy.
        // These are actual current compiler clauses, never a synthetic ParamEnv.
        if let Some(copy_trait) = tcx.lang_items().copy_trait() {
            for clause in tcx.param_env(self.body_def).caller_bounds() {
                let ty::ClauseKind::Trait(predicate) = clause.kind().skip_binder() else {
                    continue;
                };
                if predicate.polarity == ty::ClausePolarity::Positive
                    && predicate.def_id() == copy_trait
                {
                    let native = predicate.self_ty();
                    if native.has_escaping_bound_vars() {
                        return refuse(
                            "copy-premise",
                            "a higher-ranked Copy premise needs its own binder correspondence",
                            span,
                        );
                    }
                    if !candidates.contains(&native) {
                        candidates.push(native);
                    }
                }
            }
        }
        if candidates.len() > 4096 {
            return refuse(
                "copy-premise",
                "native Copy premise inventory exhausted",
                span,
            );
        }
        if candidates.is_empty() || self.mode_rejected {
            return Ok(Vec::new());
        }
        let checked = self.checked_modes.as_ref();
        // An explicitly bodyless/trusted declaration can have native generic
        // typing requirements without a completed executable body walk. Its
        // signature is still checked; these requirements authorize no body or
        // ownership check. Ordinary executable bodies need the completed Rc.
        let required_trait_header = matches!(
            tcx.hir_node_by_def_id(self.def_id),
            hir::Node::TraitItem(item)
                if matches!(item.kind, hir::TraitItemKind::Fn(_, hir::TraitFn::Required(_)))
        );
        let signature_only = checked.is_none()
            && (self.cx.declaration_attrs(self.body_def).external_body || required_trait_header);
        if checked.is_none() && !signature_only {
            return refuse(
                "copy-premise",
                "generic Copy premises require the complete current native mode walk",
                span,
            );
        }
        let revalidate = || -> R<()> {
            if tcx.dcx().has_errors().is_some()
                || self.typeck.tainted_by_errors.is_some()
                || !std::ptr::eq(self.typeck, tcx.typeck(self.body_def))
                || super::super::function_identity_observer::body_is_quarantined(
                    tcx.sess,
                    self.def_id,
                )
                || super::super::function_identity_observer::body_is_quarantined(
                    tcx.sess,
                    self.body_def,
                )
            {
                return refuse(
                    "copy-premise",
                    "Copy premises lost their current original native body, typeck or mode context",
                    span,
                );
            }
            if let Some(checked) = checked {
                if !self
                    .cx
                    .checked_modes
                    .borrow()
                    .get(&self.def_id)
                    .is_some_and(|actual| std::rc::Rc::ptr_eq(actual, checked))
                {
                    return refuse(
                        "copy-premise",
                        "the canonical completed mode Rc changed",
                        span,
                    );
                }
                checked
                    .availability
                    .checked(tcx, self.def_id, self.body_def)
                    .map_err(|detail| {
                        FnProblem::Refused(Refusal::new("copy-premise", detail, span))
                    })?;
            } else {
                // Required trait methods use their real provided spec
                // companion. The ordinary declaration helper intentionally
                // recognizes only free/impl functions; join this header's raw
                // allocation directly without declaring an executable check.
                let body = tcx.hir_maybe_body_owned_by(self.body_def).ok_or_else(|| {
                    FnProblem::Refused(Refusal::new(
                        "copy-premise",
                        "a Copy header has no native body allocation",
                        span,
                    ))
                })?;
                let original = tcx
                    .lower_to_hir(self.body_def)
                    .as_owner()
                    .and_then(|raw| raw.nodes.bodies.get(&body.id().hir_id.local_id).copied());
                if !original.is_some_and(|raw| std::ptr::eq(raw, body))
                    || super::super::function_identity_observer::body_is_quarantined(
                        tcx.sess,
                        self.body_def,
                    )
                    || (required_trait_header
                        && self
                            .cx
                            .spec_methods
                            .get(&self.def_id)
                            .copied()
                            .unwrap_or(self.def_id)
                            != self.body_def)
                {
                    return refuse(
                        "copy-premise",
                        "a Copy header lost its original native allocation or spec-companion join",
                        span,
                    );
                }
                match super::super::modes::signature_modes(self.cx, self.def_id.to_def_id(), span) {
                    super::super::modes::SignatureModeResult::Known(signature)
                        if signature.def_id == self.def_id.to_def_id()
                            && signature.body_owner == self.body_def => {}
                    _ => {
                        return refuse(
                            "copy-premise",
                            "a bodyless Copy header lost its native signature modes",
                            span,
                        )
                    }
                }
            }
            Ok(())
        };
        revalidate()?;
        let environment = ty::TypingEnv::post_typeck_through_borrowck(tcx, self.body_def);
        let mut premises = Vec::new();
        for native in candidates {
            if !tcx.type_is_copy_modulo_regions(environment, native) {
                continue;
            }
            let instantiated = self.at(native);
            let Some(translated) = self.vc_ty(instantiated)? else {
                return refuse(
                    "copy-premise",
                    "a native Copy premise has no exact represented type",
                    span,
                );
            };
            // Instance premises are the original premises at the actual native
            // arguments. WF checks their correspondence and discharges each;
            // a ground or opaque premise cannot authorize itself.
            // Preserve the declaration's premise positions after substitution:
            // distinct T:Copy and U:Copy both become u8 for f::<u8,u8>.
            // Deduplicating only the instantiated result would change the
            // generic instance's correspondence with its source declaration.
            premises.push(translated);
        }
        revalidate()?;
        Ok(premises)
    }
}
