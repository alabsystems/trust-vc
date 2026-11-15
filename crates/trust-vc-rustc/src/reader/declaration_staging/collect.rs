//! Native selections and direct owned declaration inventories.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use rustc_hir::def::DefKind;
use rustc_hir::def_id::{CrateNum, DefId, DefIndex, LOCAL_CRATE};
use rustc_middle::ty::TyCtxt;

use crate::declaration_alignment::source_bindings::{Metadata, MetadataInput, PinnedFile};
use crate::declaration_alignment::{CommonInputs, Digest, View};

use super::super::declaration_native;
use super::inputs::Inputs;
use super::invocation::Invocation;

pub(super) struct SelectedTarget {
    pub(super) metadata: Metadata,
    pub(super) native_crate: CrateNum,
    pub(super) stable_crate_id: u64,
    pub(super) svh: u128,
    pub(super) file: PinnedFile,
}

pub(super) fn selections(
    tcx: TyCtxt<'_>,
    inputs: &Inputs,
    fresh: Option<&PinnedFile>,
) -> Result<(Metadata, Option<SelectedTarget>), String> {
    selections_from(tcx, &inputs.common_files, fresh)
}

pub(super) fn client_selections(
    tcx: TyCtxt<'_>,
    common: &std::collections::BTreeMap<PathBuf, PinnedFile>,
    fresh: &PinnedFile,
) -> Result<(Metadata, Option<SelectedTarget>), String> {
    selections_from(tcx, common, Some(fresh))
}

fn selections_from(
    tcx: TyCtxt<'_>,
    files: &std::collections::BTreeMap<PathBuf, PinnedFile>,
    fresh: Option<&PinnedFile>,
) -> Result<(Metadata, Option<SelectedTarget>), String> {
    let mut common = Vec::new();
    let mut seen = BTreeSet::new();
    let mut target = None;
    for krate in tcx.crates(()) {
        let source = tcx.used_crate_source(*krate);
        let native_path = source
            .rmeta
            .as_ref()
            .or(source.rlib.as_ref())
            .or(source.dylib.as_ref())
            .ok_or("native dependency has no represented selected metadata")?;
        let path = native_path.canonicalize().map_err(|e| e.to_string())?;
        let id = tcx.stable_crate_id(*krate).as_u64();
        let svh = tcx.crate_hash(*krate).as_u128();
        if let Some(fresh) = fresh.filter(|fresh| fresh.path == path) {
            if target.is_some() {
                return Err("the fresh Erase artifact has multiple native identities".into());
            }
            fresh.read()?;
            target = Some(SelectedTarget {
                metadata: Metadata::load_native_selections([(
                    MetadataInput {
                        stable_crate_id: id,
                        svh,
                        file: PinnedFile {
                            path: native_path.clone(),
                            sha256: fresh.sha256,
                        },
                    },
                    path.clone(),
                )])?,
                native_crate: *krate,
                stable_crate_id: id,
                svh,
                file: fresh.clone(),
            });
        } else {
            let file = files.get(&path).ok_or_else(|| {
                format!(
                    "native dependency is outside the checked byte cohort: {}",
                    path.display()
                )
            })?;
            if !seen.insert(path.clone()) {
                return Err("duplicate native metadata selection".into());
            }
            // Preserve this actual CStore spelling only after its canonical
            // target matched the approved inventory. The byte binder also
            // rechecks that exact target, so a retargeted alias cannot replace
            // the approved artifact between inventory lookup and binding.
            common.push((
                MetadataInput {
                    stable_crate_id: id,
                    svh,
                    file: PinnedFile {
                        path: native_path.clone(),
                        sha256: file.sha256,
                    },
                },
                path,
            ));
        }
    }
    if seen != files.keys().cloned().collect() || target.is_some() != fresh.is_some() {
        return Err("the native common/target inventory differs from the staging recipe".into());
    }
    Ok((Metadata::load_native_selections(common)?, target))
}

pub(super) fn common(inputs: &Inputs, metadata: &Metadata) -> CommonInputs {
    CommonInputs {
        compiler_sha256: inputs.compiler_driver.sha256,
        source: inputs.sources.identity(),
        builtin_artifacts: [&inputs.builtin]
            .into_iter()
            .chain(&inputs.macros)
            .map(|file| file.sha256)
            .collect(),
        dependency_artifacts: metadata.digests(),
    }
}

pub(super) fn view(
    tcx: TyCtxt<'_>,
    library: CrateNum,
    inputs: &Inputs,
    metadata: &Metadata,
    invocation: &Invocation,
    selected: Option<Digest>,
) -> Result<View, String> {
    let definitions = if library == LOCAL_CRATE {
        tcx.hir_crate_items(())
            .owners()
            .map(|owner| owner.def_id.to_def_id())
            .collect::<Vec<_>>()
    } else {
        (0..tcx.num_extern_def_ids(library))
            .map(|index| DefId {
                krate: library,
                index: DefIndex::from_usize(index),
            })
            .collect()
    };
    let declarations = definitions
        .into_iter()
        .filter(|def| {
            matches!(
                tcx.def_kind(*def),
                DefKind::Fn | DefKind::AssocFn | DefKind::Struct | DefKind::Enum | DefKind::Union
            ) && tcx.visibility(*def).is_public()
        })
        .map(|def| declaration_native::capture(tcx, def, library, &inputs.sources, metadata))
        .collect();
    Ok(View {
        common: common(inputs, metadata),
        cfg_sha256: invocation.cfg_digest()?,
        stable_crate_id: tcx.stable_crate_id(library).as_u64(),
        selected_rmeta_sha256: selected,
        declarations,
    })
}

pub(super) fn target_path(root: &Path) -> PathBuf {
    root.join("erase").join("libvstd.rmeta")
}
