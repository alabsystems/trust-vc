//! Rematch actual foreign identities in the new client compiler context.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

extern crate rustc_data_structures;

use rustc_data_structures::fingerprint::Fingerprint;
use rustc_hir::def_id::{CrateNum, DefId, DefPathHash};

use super::*;

/// These IDs belong only to the actual client GCTx. They are never saved in
/// the owned producer packet or reconstructed from Keep-session DefIds.
pub(super) struct ClientFrame<'library, 'tcx> {
    tcx: TyCtxt<'tcx>,
    target: CrateNum,
    images: client_images::ObservedImages<'library, 'tcx>,
    owner: &'library standalone_client::StandaloneImported<'library>,
    argv: Vec<String>,
}

impl<'library, 'tcx> ClientFrame<'library, 'tcx> {
    pub(super) fn capture(
        tcx: TyCtxt<'tcx>,
        argv: &[String],
        owner: &'library standalone_client::StandaloneImported<'library>,
    ) -> Result<Self, String> {
        diagnostics(tcx)?;
        let images = owner.inspect(tcx, argv)?;
        images.current(tcx)?;
        let target = images.target();
        diagnostics(tcx)?;
        Ok(Self {
            tcx,
            target,
            images,
            owner,
            argv: argv.to_vec(),
        })
    }

    pub(super) fn current(&self, tcx: TyCtxt<'tcx>) -> Result<(), String> {
        if !std::ptr::eq(*self.tcx, *tcx) {
            return Err("the client declaration belongs to a different compiler context".into());
        }
        self.owner.current()?;
        self.images.current(tcx)
    }

    pub(super) fn library(&self) -> &'library StagedLibrary {
        self.owner.library()
    }
    pub(super) fn owner(&self) -> &'library standalone_client::StandaloneImported<'library> {
        self.owner
    }
    pub(super) fn common(&self) -> &Metadata {
        self.images.common()
    }

    pub(super) fn revalidate(&self, tcx: TyCtxt<'tcx>) -> Result<(), String> {
        self.current(tcx)?;
        let actual = self.owner.inspect(tcx, &self.argv)?;
        actual.current(tcx)?;
        if actual.target() != self.target {
            return Err("the current client selected a different native Erase crate".into());
        }
        self.common().revalidate()?;
        diagnostics(tcx)
    }

    /// Retained input/current-CStore identity, including after an expected
    /// compiler diagnostic. This grants no declaration or proof permission:
    /// positive uses still require the diagnostic-sensitive `revalidate`.
    pub(super) fn check_retained_inputs(&self, tcx: TyCtxt<'tcx>) -> Result<(), String> {
        if !std::ptr::eq(*self.tcx, *tcx) {
            return Err("the normal client left its original compiler context".into());
        }
        self.owner.check_retained_inputs()?;
        let library = self.library();
        let (common, target) = collect::client_selections(
            tcx,
            self.owner.common_files(),
            &library.prepared.erase.file,
        )?;
        let target = target.ok_or("the normal client lost its actual Erase crate")?;
        if target.native_crate != self.target
            || target.stable_crate_id != library.prepared.erase.view.stable_crate_id
            || target.svh != library.prepared.erase.target_svh
            || common.crate_ids() != self.common().crate_ids()
        {
            return Err("the normal client CStore selection changed".into());
        }
        for krate in tcx.crates(()) {
            if *krate == self.target {
                continue;
            }
            let source = tcx.used_crate_source(*krate);
            let path = source
                .rmeta
                .as_ref()
                .or(source.rlib.as_ref())
                .or(source.dylib.as_ref())
                .ok_or("the retained client dependency has no native file")?
                .canonicalize()
                .map_err(|e| e.to_string())?;
            let id = tcx.stable_crate_id(*krate).as_u64();
            let svh = tcx.crate_hash(*krate).as_u128();
            if common.selected(id, svh, &path)? != self.common().selected(id, svh, &path)? {
                return Err("a retained normal-client dependency changed".into());
            }
        }
        self.common().revalidate()
    }

    /// Resolve an already licensed Erase key, after establishing its crate is
    /// actually loaded. The latter avoids the native inverse-hash API's
    /// uninterned-crate failure. Display paths and local indices are not keys.
    pub(super) fn resolve(&self, key: NativeKey) -> Result<DefId, String> {
        self.current(self.tcx)?;
        if key.stable_crate_id != self.tcx.stable_crate_id(self.target).as_u64()
            || (key.def_path_hash >> 64) as u64 != key.stable_crate_id
        {
            return Err("the imported declaration key is outside the actual Erase crate".into());
        }
        let hash = DefPathHash(Fingerprint::new(
            (key.def_path_hash >> 64) as u64,
            key.def_path_hash as u64,
        ));
        let def = self
            .tcx
            .def_path_hash_to_def_id(hash)
            .ok_or("the actual client metadata has no licensed declaration key")?;
        if def.is_local()
            || def.krate != self.target
            || declaration_native::key(self.tcx, def) != key
        {
            return Err(
                "the native inverse identity is not the expected foreign declaration".into(),
            );
        }
        Ok(def)
    }

    pub(super) fn declaration(
        &self,
        key: NativeKey,
    ) -> Result<(DefId, alignment::Declaration), String> {
        let def = self.resolve(key)?;
        let library = self.library();
        let expected = library
            .prepared
            .erase
            .view
            .declarations
            .iter()
            .find(|declaration| declaration.key == key)
            .ok_or("the selected metadata declaration was not in the producer's Erase inventory")?;
        let actual = declaration_native::capture(
            self.tcx,
            def,
            self.target,
            &library.inputs.sources,
            self.common(),
        );
        if actual != *expected {
            return Err("the actual client declaration differs from the staged native signature/source facts".into());
        }
        diagnostics(self.tcx)?;
        Ok((def, actual))
    }
}
