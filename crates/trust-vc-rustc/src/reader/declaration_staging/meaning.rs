//! Bind mathematical scalar and Box WF meanings to actual native origins.
//!
//! A diagnostic item identifies a candidate; only the fresh builtin build
//! supplies scalar meaning. No observation can construct these sealed values.
//! Box has a separate native compiler origin and grants only language/WF
//! meaning, never allocation, constructor, body or ownership permission.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::BTreeMap;
use std::path::Path;

use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::Symbol;
use serde_json::{json, Value};

use crate::declaration_alignment::source_bindings::{Metadata, PinnedFile};
use crate::declaration_alignment::{Digest, NativeKey};

use super::super::{declaration_native, declaration_wf};
use super::build_origin::BuiltArtifact;
use super::inputs::Inputs;

#[cfg(test)]
mod tests;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ScalarKind {
    Integer,
    Natural,
}

impl ScalarKind {
    fn diagnostic(self) -> &'static str {
        match self {
            Self::Integer => "verus::verus_builtin::int",
            Self::Natural => "verus::verus_builtin::nat",
        }
    }
}

struct SelectedDefinition {
    key: NativeKey,
    svh: u128,
    file: PinnedFile,
}

impl SelectedDefinition {
    fn capture(tcx: TyCtxt<'_>, definition: DefId, metadata: &Metadata) -> Result<Self, String> {
        if definition.is_local() {
            return Err("a builtin meaning cannot come from a local declaration".into());
        }
        let key = declaration_native::key(tcx, definition);
        let svh = tcx.crate_hash(definition.krate).as_u128();
        let source = tcx.used_crate_source(definition.krate);
        let path = source
            .rmeta
            .as_ref()
            .or(source.rlib.as_ref())
            .or(source.dylib.as_ref())
            .ok_or("a builtin meaning has no actual selected metadata")?
            .canonicalize()
            .map_err(|e| e.to_string())?;
        let file = PinnedFile {
            sha256: metadata.selected(key.stable_crate_id, svh, &path)?,
            path,
        };
        file.read()?;
        Ok(Self { key, svh, file })
    }

    fn same_selection(&self, other: &Self) -> bool {
        self.key == other.key
            && self.svh == other.svh
            && self.file.path == other.file.path
            && self.file.sha256 == other.file.sha256
    }

    fn observation(&self) -> Value {
        json!({"stable_crate_id": format!("{:016x}", self.key.stable_crate_id),
            "def_path_hash": format!("{:032x}", self.key.def_path_hash),
            "svh": format!("{:032x}", self.svh),
            "selected_path": self.file.path, "selected_sha256": self.file.sha256})
    }
}

/// Retains the actual fresh construction token, not just matching file bytes.
pub(super) struct ScalarBinding {
    kind: ScalarKind,
    definition: SelectedDefinition,
    origin: BuiltArtifact,
}

impl ScalarBinding {
    pub(super) fn kind(&self) -> ScalarKind {
        self.kind
    }
    pub(super) fn key(&self) -> NativeKey {
        self.definition.key
    }
    pub(super) fn svh(&self) -> u128 {
        self.definition.svh
    }
    pub(super) fn artifact(&self) -> Digest {
        self.definition.file.sha256
    }
    pub(super) fn path(&self) -> &Path {
        &self.definition.file.path
    }
    pub(super) fn origin(&self) -> &BuiltArtifact {
        &self.origin
    }
}

/// This is independent of a fresh upstream builtin build. Its meaning is
/// restricted to the actual compiler-owned Box language item and selected
/// native sysroot metadata, with no allocator or field-representation grant.
pub(super) struct OwnedBoxBinding {
    definition: SelectedDefinition,
    compiler_driver: PinnedFile,
}

impl OwnedBoxBinding {
    pub(super) fn key(&self) -> NativeKey {
        self.definition.key
    }
    pub(super) fn svh(&self) -> u128 {
        self.definition.svh
    }
    pub(super) fn artifact(&self) -> Digest {
        self.definition.file.sha256
    }
    pub(super) fn path(&self) -> &Path {
        &self.definition.file.path
    }
    pub(super) fn covers(&self, requirement: &declaration_wf::BuiltinRequirement) -> bool {
        requirement.role == declaration_wf::BuiltinRole::OwnedBox
            && requirement.definition == self.definition.key
            && requirement.crate_svh == self.definition.svh
    }
}

/// Created in an actual compiler callback. The final client must revalidate
/// against its own native diagnostic/lang-item and CStore selections before
/// using these meanings to lower a signature. No DefId escapes this packet.
pub(super) struct ScalarBindings {
    scalars: BTreeMap<NativeKey, ScalarBinding>,
    owned_box: Option<OwnedBoxBinding>,
}

/// Successful revalidation in one actual client/producer compiler context.
/// Signature lowering should accept this scoped projection, rather than use
/// an owned inventory as a substitute for matching the current CStore.
pub(super) struct MatchedBindings<'facts, 'tcx> {
    bindings: &'facts ScalarBindings,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> MatchedBindings<'_, 'tcx> {
    fn current(&self, tcx: TyCtxt<'tcx>) -> bool {
        std::ptr::eq(*self.tcx, *tcx) && tcx.dcx().has_errors().is_none()
    }
    pub(super) fn get(&self, tcx: TyCtxt<'tcx>, key: NativeKey) -> Option<&ScalarBinding> {
        if !self.current(tcx) {
            return None;
        }
        self.bindings.scalars.get(&key)
    }
    pub(super) fn owned_box(&self, tcx: TyCtxt<'tcx>) -> Option<&OwnedBoxBinding> {
        if !self.current(tcx) {
            return None;
        }
        self.bindings.owned_box.as_ref()
    }
}

impl ScalarBindings {
    /// Owned producer fact only. Use for_context before native IR conversion.
    pub(super) fn get(&self, key: NativeKey) -> Option<&ScalarBinding> {
        self.scalars.get(&key)
    }
    pub(super) fn owned_box(&self) -> Option<&OwnedBoxBinding> {
        self.owned_box.as_ref()
    }

    pub(super) fn for_context<'facts, 'tcx>(
        &'facts self,
        tcx: TyCtxt<'tcx>,
        inputs: &Inputs,
        metadata: &Metadata,
    ) -> Result<MatchedBindings<'facts, 'tcx>, String> {
        self.revalidate(tcx, inputs, metadata)?;
        Ok(MatchedBindings {
            bindings: self,
            tcx,
        })
    }

    pub(super) fn revalidate(
        &self,
        tcx: TyCtxt<'_>,
        inputs: &Inputs,
        metadata: &Metadata,
    ) -> Result<(), String> {
        preflight(tcx, inputs, metadata)?;
        for binding in self.scalars.values() {
            let current = scalar_definition(tcx, binding.kind)?
                .ok_or("a captured scalar diagnostic item disappeared")?;
            let selected = SelectedDefinition::capture(tcx, current, metadata)?;
            if !binding.definition.same_selection(&selected) {
                return Err("a scalar native key, SVH, metadata path or artifact changed".into());
            }
            let cohort = inputs
                .build_origin
                .as_ref()
                .ok_or("a scalar meaning lost its genuine fresh build")?;
            exact_builtin(&selected, inputs)?;
            // Recheck the complete source/build/token relationship, not an
            // observation or a caller-provided authenticated flag.
            let _current =
                cohort.selected(&inputs.sources, &selected.file.path, selected.file.sha256)?;
        }
        if let Some(binding) = &self.owned_box {
            let current = capture_box(tcx, &inputs.compiler_driver, metadata)?
                .ok_or("the captured native Box language item disappeared")?;
            if !binding.definition.same_selection(&current.definition)
                || binding.compiler_driver.path != current.compiler_driver.path
                || binding.compiler_driver.sha256 != current.compiler_driver.sha256
            {
                return Err("the native Box compiler or selected definition changed".into());
            }
        }
        preflight(tcx, inputs, metadata)
    }

    pub(super) fn observation(&self) -> Value {
        json!({"state": "CapturedNativeTypeMeanings",
            "scalars": self.scalars.values().map(|binding| json!({
                "kind": format!("{:?}", binding.kind), "definition": binding.definition.observation(),
                "fresh_build": binding.origin.observation(),
            })).collect::<Vec<_>>(),
            "owned_box": self.owned_box.as_ref().map(|binding| json!({
                "definition": binding.definition.observation(),
                "compiler_driver_sha256": binding.compiler_driver.sha256,
                "meaning_scope": "native Box language and WF only",
            })),
            "client_native_revalidation": "required before signature lowering",
            "import_authorized": false, "body_verified": false,
            "constructor_or_ownership_authority": false})
    }
}

fn preflight(tcx: TyCtxt<'_>, inputs: &Inputs, metadata: &Metadata) -> Result<(), String> {
    if tcx.dcx().has_errors().is_some() {
        return Err("native diagnostics reject builtin meanings".into());
    }
    inputs.revalidate()?;
    metadata.revalidate()
}

fn foreign_struct(tcx: TyCtxt<'_>, definition: DefId, arity: usize) -> Result<(), String> {
    if definition.is_local() || tcx.def_kind(definition) != DefKind::Struct {
        return Err("a builtin meaning needs an actual foreign struct".into());
    }
    let generics = tcx.generics_of(definition);
    if generics.parent.is_some()
        || generics.own_params.len() != arity
        || generics.own_params.iter().any(|parameter| {
            !matches!(
                parameter.kind,
                ty::GenericParamDefKind::Type {
                    synthetic: false,
                    ..
                }
            )
        })
    {
        return Err("a builtin meaning needs the expected actual foreign struct/binders".into());
    }
    Ok(())
}

fn scalar_definition(tcx: TyCtxt<'_>, kind: ScalarKind) -> Result<Option<DefId>, String> {
    let Some(definition) = tcx.get_diagnostic_item(Symbol::intern(kind.diagnostic())) else {
        return Ok(None);
    };
    foreign_struct(tcx, definition, 0)?;
    Ok(Some(definition))
}

fn exact_builtin(selected: &SelectedDefinition, inputs: &Inputs) -> Result<(), String> {
    if selected.file.path != inputs.builtin.path || selected.file.sha256 != inputs.builtin.sha256 {
        return Err(
            "a scalar diagnostic item is outside the exact selected fresh builtin artifact".into(),
        );
    }
    Ok(())
}

/// Bind an actual resolved language builtin used by a live ghost-only body.
/// Its diagnostic classification alone is never this fresh artifact license.
pub(super) fn validate_builtin_member(
    tcx: TyCtxt<'_>,
    definition: DefId,
    inputs: &Inputs,
    metadata: &Metadata,
) -> Result<(), String> {
    preflight(tcx, inputs, metadata)?;
    let selected = SelectedDefinition::capture(tcx, definition, metadata)?;
    exact_builtin(&selected, inputs)?;
    let cohort = inputs
        .build_origin
        .as_ref()
        .ok_or("a builtin lost its actual fresh construction")?;
    let _origin = cohort.selected(&inputs.sources, &selected.file.path, selected.file.sha256)?;
    if tcx.dcx().has_errors().is_some() {
        return Err("native diagnostics revoked the builtin binding".into());
    }
    Ok(())
}

fn capture_box(
    tcx: TyCtxt<'_>,
    driver: &PinnedFile,
    metadata: &Metadata,
) -> Result<Option<OwnedBoxBinding>, String> {
    let Some(definition) = tcx.lang_items().owned_box() else {
        return Ok(None);
    };
    foreign_struct(tcx, definition, 2)?;
    let selected = SelectedDefinition::capture(tcx, definition, metadata)?;
    let sysroot = Path::new(env!("VC_SHIM_COMPILER_SYSROOT"))
        .canonicalize()
        .map_err(|e| e.to_string())?;
    driver.read()?;
    if !selected.file.path.starts_with(sysroot)
        || super::identity::loaded_driver_path()? != driver.path
    {
        return Err(
            "the actual Box language item is not bound to this native sysroot/compiler image"
                .into(),
        );
    }
    Ok(Some(OwnedBoxBinding {
        definition: selected,
        compiler_driver: driver.clone(),
    }))
}

pub(super) fn capture(
    tcx: TyCtxt<'_>,
    inputs: &Inputs,
    metadata: &Metadata,
) -> Result<ScalarBindings, String> {
    preflight(tcx, inputs, metadata)?;
    let mut scalars = BTreeMap::new();
    // Legacy request@1 can still measure native facts but has no scalar
    // meaning, even when a foreign diagnostic item looks genuine.
    if let Some(cohort) = &inputs.build_origin {
        for kind in [ScalarKind::Integer, ScalarKind::Natural] {
            let Some(definition) = scalar_definition(tcx, kind)? else {
                continue;
            };
            let selected = SelectedDefinition::capture(tcx, definition, metadata)?;
            exact_builtin(&selected, inputs)?;
            let origin =
                cohort.selected(&inputs.sources, &selected.file.path, selected.file.sha256)?;
            let key = selected.key;
            if scalars
                .insert(
                    key,
                    ScalarBinding {
                        kind,
                        definition: selected,
                        origin,
                    },
                )
                .is_some()
            {
                return Err("one native definition has conflicting scalar meanings".into());
            }
        }
    }
    let owned_box = capture_box(tcx, &inputs.compiler_driver, metadata)?;
    if owned_box
        .as_ref()
        .is_some_and(|binding| scalars.contains_key(&binding.definition.key))
    {
        return Err("a scalar meaning conflicts with the native Box language item".into());
    }
    let bindings = ScalarBindings { scalars, owned_box };
    bindings.revalidate(tcx, inputs, metadata)?;
    Ok(bindings)
}
