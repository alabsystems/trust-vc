//! Prepare native facts for a later authenticated declaration producer.
//!
//! A prepared value is not an import capability. In particular, caller-pinned
//! views and files do not authenticate their producer or its effective cfg.
//! The staging owner must still supply that authority and the native generic
//! predicate/nominal well-formedness facts before admitting a declaration.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use rustc_hir::def::DefKind;
use rustc_hir::def_id::{LocalDefId, LOCAL_CRATE};
use rustc_hir::{self as hir};
use rustc_middle::ty::TyCtxt;
use rustc_span::{FileName, Pos};
use serde_json::{json, Value};
use trust_vc_vcir::Mode;

use crate::declaration_alignment::observation::ObservedAnchor;
use crate::declaration_alignment::source_bindings::{Metadata, SourceIdentity, Sources};
use crate::declaration_alignment::{
    self as alignment, Candidate, Declaration, DeclarationShape, Digest, FunctionOrigin, NativeKey,
    Observation, View,
};

use super::declaration_headers::{CheckedHeaders, EmptyHeader};
use super::declaration_modes::{original_body_available, DeclarationModes};
use super::modes::{CheckedModes, ModeCheck};

mod types;

/// Byte selections supplied by the staging owner. Native IDs and SVHs here
/// are claims to check against its future trusted invocation handoff, not
/// evidence created by the file checker itself.
pub(super) struct ByteInputs<'a> {
    pub(super) sources: &'a Sources,
    pub(super) dependencies: &'a Metadata,
    pub(super) erase_artifact: &'a Metadata,
    pub(super) erase_svh: u128,
    pub(super) erase_path: &'a Path,
}

/// Structural matches tied to the exact two immutable views compared here.
/// This value authenticates no files, compiler invocation, or import authority.
pub(super) struct ComparedViews<'a> {
    keep: &'a View,
    erase: &'a View,
    candidates: alignment::Candidates,
    pairs: BTreeMap<NativeKey, NativeKey>,
    keep_declarations: BTreeMap<NativeKey, &'a Declaration>,
    erase_declarations: BTreeMap<NativeKey, &'a Declaration>,
}

impl<'a> ComparedViews<'a> {
    pub(super) fn compare(keep: &'a View, erase: &'a View) -> Result<Self, String> {
        let candidates = alignment::compare(keep, erase)?;
        let pairs = candidates
            .matches
            .iter()
            .map(|candidate| (candidate.keep, candidate.erase))
            .collect::<BTreeMap<_, _>>();
        if pairs.len() != candidates.matches.len() {
            return Err("the structural comparison repeated a Keep owner".into());
        }
        Ok(Self {
            keep,
            erase,
            candidates,
            pairs,
            keep_declarations: keep.declarations.iter().map(|v| (v.key, v)).collect(),
            erase_declarations: erase.declarations.iter().map(|v| (v.key, v)).collect(),
        })
    }

    pub(super) fn candidates(&self) -> &alignment::Candidates {
        &self.candidates
    }

    pub(super) fn into_candidates(self) -> alignment::Candidates {
        self.candidates
    }

    fn declarations(
        &self,
        requested: &Candidate,
    ) -> Result<(&'a Declaration, &'a Declaration), String> {
        if self.pairs.get(&requested.keep) != Some(&requested.erase) {
            return Err("the requested native keys have no unique structural/source match".into());
        }
        let keep = self
            .keep_declarations
            .get(&requested.keep)
            .copied()
            .ok_or("the Keep declaration is absent")?;
        let erase = self
            .erase_declarations
            .get(&requested.erase)
            .copied()
            .ok_or("the Erase declaration is absent")?;
        if !matches!(
            keep.shape,
            Observation::Observed(DeclarationShape::Function { .. })
        ) || !matches!(
            erase.shape,
            Observation::Observed(DeclarationShape::Function { .. })
        ) {
            return Err("this factory prepares function declarations only".into());
        }
        Ok((keep, erase))
    }
}

/// A source/structure match with checked bytes. There is deliberately no
/// Deserialize implementation, authority flag, or import conversion.
pub(super) struct PreparedCorrespondence<'a> {
    keep: &'a Declaration,
    erase: &'a Declaration,
    sources: &'a Sources,
    dependencies: &'a Metadata,
    source_identity: SourceIdentity,
    keep_cfg: Digest,
    erase_cfg: Digest,
    erase_rmeta: Digest,
}

fn target_is_separate(
    target: &Metadata,
    dependencies: &Metadata,
    crate_id: u64,
    selected: Digest,
) -> bool {
    target.crate_ids() == BTreeSet::from([crate_id])
        && !dependencies.crate_ids().contains(&crate_id)
        && !dependencies.digests().contains(&selected)
}

pub(super) fn prepare_correspondence<'a>(
    bytes: &ByteInputs<'a>,
    compared: &ComparedViews<'a>,
    requested: &Candidate,
) -> Result<PreparedCorrespondence<'a>, String> {
    bytes.sources.revalidate()?;
    bytes.dependencies.revalidate()?;
    bytes.erase_artifact.revalidate()?;
    let identity = bytes.sources.identity();
    // Match the entire checked graph and policy. Unmodified is explicit;
    // applied compatibility must match the recipe as well as the patch.
    if identity != compared.keep.common.source
        || bytes.dependencies.digests() != compared.keep.common.dependency_artifacts
    {
        return Err("candidate inputs differ from the checked staging bytes".into());
    }
    let (keep, erase) = compared.declarations(requested)?;
    for declaration in [keep, erase] {
        let Observation::Observed(anchor) = &declaration.source else {
            return Err("an authored declaration anchor is Unknown".into());
        };
        bytes.sources.validate_anchor(&anchor.identifier)?;
        for scope in &anchor.enclosing_declarations {
            bytes.sources.validate_anchor(scope)?;
        }
    }
    let selected = bytes.erase_artifact.selected(
        compared.erase.stable_crate_id,
        bytes.erase_svh,
        bytes.erase_path,
    )?;
    if compared.erase.selected_rmeta_sha256 != Some(selected)
        || !target_is_separate(
            bytes.erase_artifact,
            bytes.dependencies,
            compared.erase.stable_crate_id,
            selected,
        )
    {
        return Err("the selected Erase target is not the separate exact artifact".into());
    }
    Ok(PreparedCorrespondence {
        keep,
        erase,
        sources: bytes.sources,
        dependencies: bytes.dependencies,
        source_identity: identity,
        keep_cfg: compared.keep.cfg_sha256,
        erase_cfg: compared.erase.cfg_sha256,
        erase_rmeta: selected,
    })
}

/// These native facts are scoped to the actual original body in this TyCtxt.
/// They grant no function body, ownership, reveal, private axiom, constructor,
/// or import permission, and do not count as a verified function.
pub(super) struct PreparedFunction<'facts, 'tcx> {
    owner: LocalDefId,
    body: &'tcx hir::Body<'tcx>,
    modes: CheckedModes,
    empty_header: &'facts EmptyHeader<'tcx>,
    headers: &'facts CheckedHeaders<'tcx>,
    correspondence: PreparedCorrespondence<'facts>,
}

/// Owned diagnostic facts, created only from a live checked native packet.
/// This is not deserializable and remains separate from import permission.
pub(super) struct OwnedFunction {
    keep: NativeKey,
    erase: NativeKey,
    parameter_modes: Vec<Mode>,
    return_mode: Mode,
    source: SourceIdentity,
    keep_cfg: Digest,
    erase_cfg: Digest,
    erase_rmeta: Digest,
}

impl<'tcx> PreparedFunction<'_, 'tcx> {
    pub(super) fn into_owned(self, tcx: TyCtxt<'tcx>) -> Result<OwnedFunction, String> {
        let current = self
            .headers
            .empty_for(tcx, self.owner)
            .ok_or("the native empty-header fact changed before staging consumption")?;
        if !std::ptr::eq(current, self.empty_header)
            || tcx
                .hir_maybe_body_owned_by(self.owner)
                .is_none_or(|body| !std::ptr::eq(body, self.body))
            || !original_body_available(tcx, self.owner)
            || tcx.dcx().has_errors().is_some()
        {
            return Err(
                "the original native body/header changed before staging consumption".into(),
            );
        }
        Ok(OwnedFunction {
            keep: self.correspondence.keep.key,
            erase: self.correspondence.erase.key,
            parameter_modes: self
                .modes
                .signature
                .params
                .iter()
                .map(|p| p.declared.mode)
                .collect(),
            return_mode: self.modes.signature.ret.mode,
            source: self.correspondence.source_identity,
            keep_cfg: self.correspondence.keep_cfg,
            erase_cfg: self.correspondence.erase_cfg,
            erase_rmeta: self.correspondence.erase_rmeta,
        })
    }
}

impl OwnedFunction {
    pub(super) fn keep_key(&self) -> NativeKey {
        self.keep
    }

    pub(super) fn erase_key(&self) -> NativeKey {
        self.erase
    }
    pub(super) fn parameter_modes(&self) -> &[Mode] {
        &self.parameter_modes
    }
    pub(super) fn return_mode(&self) -> Mode {
        self.return_mode
    }
    pub(super) fn source_identity(&self) -> SourceIdentity {
        self.source
    }
    pub(super) fn keep_cfg(&self) -> Digest {
        self.keep_cfg
    }
    pub(super) fn erase_cfg(&self) -> Digest {
        self.erase_cfg
    }
    pub(super) fn erase_rmeta(&self) -> Digest {
        self.erase_rmeta
    }

    pub(super) fn observation(&self) -> Value {
        json!({"state": "CheckedNativeDeclarationInputs",
            "keep_key": {"crate": self.keep.stable_crate_id, "hash": self.keep.def_path_hash.to_string()},
            "erase_key": {"crate": self.erase.stable_crate_id, "hash": self.erase.def_path_hash.to_string()},
            "parameter_modes": self.parameter_modes.iter().map(|m| format!("{m:?}")).collect::<Vec<_>>(),
            "return_mode": format!("{:?}", self.return_mode),
            "native_empty_header_checked": true,
            "source_manifest_sha256": self.source.manifest_sha256,
            "compatibility_recipe_sha256": self.source.compatibility.recipe_sha256(),
            "compatibility_patch_sha256": self.source.compatibility.patch_sha256(),
            "keep_cfg_sha256": self.keep_cfg, "erase_cfg_sha256": self.erase_cfg,
            "erase_rmeta_sha256": self.erase_rmeta,
            "declaration_authority": "not constructed by native fact preparation",
            "import_authorized": false, "body_verified": false, "ownership_checked": false})
    }
}

pub(super) enum PreparationError {
    Refused(String),
    ModeRejected(super::UserError),
    ModeUnknown(super::Refusal),
}

impl From<String> for PreparationError {
    fn from(value: String) -> Self {
        Self::Refused(value)
    }
}

fn spec_signature(mode: Mode, params: impl IntoIterator<Item = (Mode, bool)>, ret: Mode) -> bool {
    mode == Mode::Spec
        && ret == Mode::Spec
        && params
            .into_iter()
            .all(|(mode, mutable)| mode == Mode::Spec && !mutable)
}

fn native_key(tcx: TyCtxt<'_>, owner: LocalDefId) -> NativeKey {
    let (high, low) = tcx.def_path_hash(owner.to_def_id()).0.split();
    NativeKey {
        stable_crate_id: tcx.stable_crate_id(LOCAL_CRATE).as_u64(),
        def_path_hash: (u128::from(high.as_u64()) << 64) | u128::from(low.as_u64()),
    }
}

fn actual_identifier(tcx: TyCtxt<'_>, owner: LocalDefId) -> Result<ObservedAnchor, String> {
    let span = tcx
        .def_ident_span(owner.to_def_id())
        .ok_or("no native identifier span")?;
    if span.is_dummy() {
        return Err("a dummy identifier has no source binding".into());
    }
    let file = tcx.sess.source_map().lookup_source_file(span.lo());
    if !file.contains(span.hi()) {
        return Err("a cross-file identifier is not represented".into());
    }
    let FileName::Real(name) = &file.name else {
        return Err("a virtual identifier source is not represented".into());
    };
    let path = name
        .local_path()
        .ok_or("the native identifier has no local source path")?;
    Ok(ObservedAnchor {
        local_path: path
            .to_str()
            .ok_or("the native source path is not UTF-8")?
            .into(),
        compiler_source_hash: file.src_hash.to_string(),
        original_file_len: file.unnormalized_source_len,
        bytes: (
            file.original_relative_byte_pos(span.lo()).to_u32(),
            file.original_relative_byte_pos(span.hi()).to_u32(),
        ),
    })
}

pub(super) fn prepare_function<'facts, 'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    index: &DeclarationModes<'tcx>,
    headers: &'facts CheckedHeaders<'tcx>,
    correspondence: PreparedCorrespondence<'facts>,
) -> Result<PreparedFunction<'facts, 'tcx>, PreparationError> {
    let refuse = |reason: &str| PreparationError::Refused(reason.into());
    if !index.belongs_to(tcx)
        || tcx.dcx().has_errors().is_some()
        || !original_body_available(tcx, owner)
        || native_key(tcx, owner) != correspondence.keep.key
        || !tcx.visibility(owner).is_public()
    {
        return Err(refuse(
            "the public native Keep owner/body is not established",
        ));
    }
    let parent_kind = tcx.def_kind(tcx.local_parent(owner));
    let Observation::Observed(DeclarationShape::Function { origin, inputs, .. }) =
        &correspondence.keep.shape
    else {
        return Err(refuse("the candidate has no supported function shape"));
    };
    let origin_matches = matches!(
        (origin, parent_kind),
        (FunctionOrigin::Free, DefKind::Mod)
            | (
                FunctionOrigin::Inherent { .. },
                DefKind::Impl { of_trait: false }
            )
    );
    if !matches!(tcx.def_kind(owner), DefKind::Fn | DefKind::AssocFn)
        || !origin_matches
        || tcx.trait_impl_of_assoc(owner.to_def_id()).is_some()
    {
        return Err(refuse(
            "the native function origin differs from the candidate",
        ));
    }
    let Observation::Observed(anchor) = &correspondence.keep.source else {
        return Err(refuse("the candidate source is Unknown"));
    };
    if correspondence
        .sources
        .anchor(&actual_identifier(tcx, owner)?)?
        != anchor.identifier
    {
        return Err(refuse(
            "the native Keep identifier differs from its bound candidate",
        ));
    }
    types::check(tcx, owner, correspondence.keep, correspondence.dependencies)?;
    let modes = match index.check(owner) {
        ModeCheck::Clean(modes) => modes,
        ModeCheck::Error(error) => return Err(PreparationError::ModeRejected(error)),
        ModeCheck::Unknown(reason) => return Err(PreparationError::ModeUnknown(reason)),
    };
    let signature = &modes.signature;
    if signature.def_id != owner.to_def_id()
        || signature.body_owner != owner
        || signature.params.len() != inputs.len()
        || !spec_signature(
            signature.mode,
            signature
                .params
                .iter()
                .map(|p| (p.declared.mode, p.mutable_reference)),
            signature.ret.mode,
        )
    {
        return Err(refuse(
            "the checked native signature is not the corresponding all-Spec declaration",
        ));
    }
    let empty_header = headers
        .empty_for(tcx, owner)
        .ok_or_else(|| refuse("no sealed empty-header fact for this original native owner"))?;
    let body = tcx
        .hir_maybe_body_owned_by(owner)
        .ok_or_else(|| refuse("the native original body is unavailable"))?;
    if tcx.dcx().has_errors().is_some() || !original_body_available(tcx, owner) {
        return Err(refuse(
            "native declaration checking produced errors or changed the body view",
        ));
    }
    Ok(PreparedFunction {
        owner,
        body,
        modes,
        empty_header,
        headers,
        correspondence,
    })
}

#[cfg(test)]
#[path = "declaration_factory/tests.rs"]
mod tests;
