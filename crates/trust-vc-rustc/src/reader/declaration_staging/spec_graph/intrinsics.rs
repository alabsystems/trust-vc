//! Fresh construction and native identity for the bounded Spec graph seams.
//!
//! The diagnostic item locates a definition. Its spelling supplies no token:
//! the current CStore selection must be the actual freshly built artifact.

use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Kind {
    IsVariant,
    VariantField,
    Recommends,
    Language(crate::verus_items::VerusItem),
}

impl Kind {
    fn diagnostic(self) -> &'static str {
        match self {
            Self::IsVariant => "verus::verus_builtin::is_variant",
            Self::VariantField => "verus::verus_builtin::get_variant_field",
            Self::Recommends => "verus::verus_builtin::recommends",
            Self::Language(_) => {
                unreachable!("language items are captured from native diagnostics")
            }
        }
    }
}

pub(in crate::reader::declaration_staging) struct Intrinsics<'scope, 'tcx> {
    tcx: TyCtxt<'tcx>,
    pub(super) inputs: &'scope Inputs,
    metadata: &'scope Metadata,
    definitions: Vec<(Kind, DefId)>,
    items: std::collections::HashMap<DefId, crate::verus_items::VerusItem>,
    names: std::collections::HashMap<DefId, Symbol>,
    validated_members: std::cell::RefCell<HashSet<DefId>>,
    artifacts: Vec<build_origin::BuiltArtifact>,
}

impl<'scope, 'tcx> Intrinsics<'scope, 'tcx> {
    pub(in crate::reader::declaration_staging) fn capture(
        tcx: TyCtxt<'tcx>,
        inputs: &'scope Inputs,
        metadata: &'scope Metadata,
    ) -> Result<Self, String> {
        diagnostics(tcx)?;
        let fresh = inputs
            .build_origin
            .as_ref()
            .ok_or("Spec graph intrinsics require the actual fresh builtin construction")?;
        inputs.revalidate()?;
        metadata.revalidate()?;
        if tcx.sess.trust_verification_enabled()
            || tcx.sess.trust_ir_lower_enabled()
            || tcx.sess.opts.unstable_opts.trust_targo_test_monitor
            || tcx.sess.opts.unstable_opts.trust_certified_test_monitors
            || tcx.sess.opts.incremental.is_some()
            || std::env::var("VSTD_KIND").as_deref() != Ok("IsVstd")
            || ["verus_keep_ghost", "verus_keep_ghost_body"]
                .into_iter()
                .any(|name| !tcx.sess.config.contains(&(Symbol::intern(name), None)))
        {
            return Err("Spec graph capture requires the original unverified Keep session".into());
        }
        let mut artifacts = Vec::new();
        for file in [&inputs.builtin].into_iter().chain(&inputs.macros) {
            // A BuiltArtifact can only come from the maintained build owner.
            artifacts.push(fresh.selected(&inputs.sources, &file.path, file.sha256)?);
        }
        let mut definitions = Vec::new();
        for kind in [Kind::IsVariant, Kind::VariantField, Kind::Recommends] {
            let definition = tcx
                .get_diagnostic_item(Symbol::intern(kind.diagnostic()))
                .ok_or("a required Spec graph intrinsic is absent")?;
            if definition.is_local() || tcx.def_kind(definition) != DefKind::Fn {
                return Err("a Spec graph intrinsic is not a foreign native function".into());
            }
            let native = tcx.used_crate_source(definition.krate);
            let path = native
                .rmeta
                .as_ref()
                .or(native.rlib.as_ref())
                .or(native.dylib.as_ref())
                .ok_or("a Spec graph intrinsic lacks selected native metadata")?;
            if path.canonicalize().map_err(|error| error.to_string())? != inputs.builtin.path
                || declaration_native::selected(tcx, definition.krate, metadata)?
                    != inputs.builtin.sha256
            {
                return Err("a Spec graph intrinsic is from a different selected artifact".into());
            }
            definitions.push((kind, definition));
        }
        let mut items = std::collections::HashMap::new();
        let mut names = std::collections::HashMap::new();
        for (name, definition) in &tcx.all_diagnostic_items(()).name_to_id {
            if !name.as_str().starts_with("verus::verus_builtin::") {
                continue;
            }
            let Some(item) = crate::verus_items::VerusItem::from_name(name.as_str()) else {
                continue;
            };
            // The spelling classifies a candidate. Its actual CStore artifact
            // and the retained fresh build owner supply the language meaning.
            meaning::validate_builtin_member(tcx, *definition, inputs, metadata)?;
            items.insert(*definition, item);
            names.insert(*definition, *name);
            if !definitions.iter().any(|(_, actual)| actual == definition) {
                definitions.push((Kind::Language(item), *definition));
            }
        }
        let result = Self {
            tcx,
            inputs,
            metadata,
            definitions,
            validated_members: std::cell::RefCell::new(items.keys().copied().collect()),
            items,
            names,
            artifacts,
        };
        result.current(tcx)?;
        Ok(result)
    }

    pub(super) fn current(&self, tcx: TyCtxt<'tcx>) -> Result<(), String> {
        diagnostics(tcx)?;
        if !std::ptr::eq(*tcx, *self.tcx)
            || std::env::var("VSTD_KIND").as_deref() != Ok("IsVstd")
            || self
                .definitions
                .iter()
                .any(|(kind, definition)| match kind {
                    Kind::Language(_) => self
                        .names
                        .get(definition)
                        .is_none_or(|name| tcx.get_diagnostic_item(*name) != Some(*definition)),
                    _ => {
                        tcx.get_diagnostic_item(Symbol::intern(kind.diagnostic()))
                            != Some(*definition)
                    }
                })
        {
            return Err("the original Spec graph intrinsic context changed".into());
        }
        Ok(())
    }

    pub(super) fn kind(&self, definition: DefId) -> Option<Kind> {
        self.definitions
            .iter()
            .find_map(|(kind, actual)| (*actual == definition).then_some(*kind))
    }

    pub(super) fn reader_items(
        &self,
    ) -> std::collections::HashMap<DefId, crate::verus_items::VerusItem> {
        self.items.clone()
    }

    /// Trait operators are resolved in the caller's actual generic context.
    /// Their selected implementation and member must belong to the same fresh
    /// builtin image as the diagnostic declaration before they are intrinsic.
    pub(super) fn validate_selection(&self, definition: DefId) -> Result<(), String> {
        self.current(self.tcx)?;
        if self.validated_members.borrow().contains(&definition) {
            return Ok(());
        }
        meaning::validate_builtin_member(self.tcx, definition, self.inputs, self.metadata)?;
        self.validated_members.borrow_mut().insert(definition);
        Ok(())
    }

    /// Bind a consumer to this exact live construction context. This grants
    /// no representation, header, expression-lowering or imported-body fact.
    pub(in crate::reader::declaration_staging) fn belongs(
        &self,
        tcx: TyCtxt<'tcx>,
        inputs: &Inputs,
        metadata: &Metadata,
    ) -> Result<(), String> {
        self.current(tcx)?;
        if !std::ptr::eq(inputs, self.inputs) || !std::ptr::eq(metadata, self.metadata) {
            return Err("the Spec intrinsic scope belongs to different producer inputs".into());
        }
        Ok(())
    }

    pub(in crate::reader::declaration_staging) fn revalidate(&self) -> Result<(), String> {
        self.current(self.tcx)?;
        self.inputs.revalidate()?;
        self.metadata.revalidate()?;
        let fresh = self
            .inputs
            .build_origin
            .as_ref()
            .ok_or("the Spec graph build owner disappeared")?;
        for artifact in &self.artifacts {
            let file = artifact.file();
            file.read()?;
            fresh.selected(&self.inputs.sources, &file.path, file.sha256)?;
        }
        Ok(())
    }
}
