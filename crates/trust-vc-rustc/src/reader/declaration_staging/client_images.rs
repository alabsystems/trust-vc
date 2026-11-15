//! Owned client macro images and their exact native metadata correspondence.
//!
//! This is loader provenance only. Independent Imported initialization still
//! requires the genuine old-image negative and new-image positive execution.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
extern crate rustc_session;

fn unique_native_candidates(
    tcx: TyCtxt<'_>,
    copies: &[build_origin::CopiedMacro],
) -> Result<(), String> {
    use rustc_session::search_paths::PathKind;
    // These native iterators include implicit target/host sysroot paths.
    // Directory order is insufficient when locator candidates have equal
    // filenames and SVHs, so require one canonical physical macro candidate.
    for search in [tcx.sess.target_filesearch(), tcx.sess.host_filesearch()] {
        for copy in copies {
            let filename = copy
                .file()
                .path
                .file_name()
                .and_then(|name| name.to_str())
                .ok_or("the genuine macro has no represented native filename")?;
            let prefix = filename
                .strip_suffix(".dylib")
                .ok_or("the current macro recipe requires the native Darwin dylib")?;
            let mut found = false;
            for suffix in [".dylib", ".rmeta", ".rlib"] {
                for (_, path) in search.get_library_candidates(prefix, suffix, PathKind::Dependency)
                {
                    if path.canonicalize().map_err(|e| e.to_string())? != copy.file().path {
                        return Err(
                            "the copied macro is not the unique native dependency candidate".into(),
                        );
                    }
                    found = true;
                }
            }
            if !found {
                return Err(
                    "the copied macro is not the unique native dependency candidate".into(),
                );
            }
        }
    }
    Ok(())
}

pub(super) struct ClientImages<'library> {
    library: &'library StagedLibrary,
    copies: Vec<build_origin::CopiedMacro>,
    dependency_view: build_origin::DependencyView,
    common_files: BTreeMap<std::path::PathBuf, PinnedFile>,
}

pub(super) struct ObservedImages<'images, 'tcx> {
    tcx: TyCtxt<'tcx>,
    target: rustc_hir::def_id::CrateNum,
    loaded: Vec<build_origin::LoadedMacro<'images>>,
    common: Metadata,
    dependency_view: Value,
}

impl<'library> ClientImages<'library> {
    pub(super) fn prepare(library: &'library StagedLibrary) -> Result<Self, String> {
        library.inputs.revalidate()?;
        let cohort = library
            .inputs
            .build_origin
            .as_ref()
            .ok_or("client macro isolation needs the actual fresh builtin construction")?;
        let copies = cohort.copy_client_macros(
            &library.inputs.sources,
            &library.inputs.output.join("client-macro-images"),
        )?;
        let mut common_files = library.inputs.common_files.clone();
        for copy in &copies {
            let original = copy.original().file();
            let old = common_files
                .remove(&original.path)
                .ok_or("the copied macro origin is outside the original native cohort")?;
            if old.sha256 != original.sha256
                || common_files
                    .insert(copy.file().path.clone(), copy.file().clone())
                    .is_some()
            {
                return Err(
                    "the client macro copy changes or duplicates a selected artifact".into(),
                );
            }
        }
        if copies.len() != 2 || common_files.len() != library.inputs.common_files.len() {
            return Err(
                "the client macro copy inventory differs from the genuine two images".into(),
            );
        }
        let dependency_view = cohort.dependency_view(&library.inputs.sources, &copies)?;
        Ok(Self {
            library,
            copies,
            dependency_view,
            common_files,
        })
    }

    pub(super) fn revalidate(&self) -> Result<(), String> {
        self.dependency_view.revalidate()?;
        for copy in &self.copies {
            copy.revalidate()?;
        }
        for file in self.common_files.values() {
            file.read()?;
        }
        Ok(())
    }

    pub(super) fn library(&self) -> &'library StagedLibrary {
        self.library
    }

    pub(super) fn common_files(&self) -> &BTreeMap<std::path::PathBuf, PinnedFile> {
        &self.common_files
    }

    pub(super) fn macro_files(&self) -> impl Iterator<Item = &PinnedFile> {
        self.copies.iter().map(build_origin::CopiedMacro::file)
    }

    pub(super) fn observe<'images, 'tcx>(
        &'images self,
        tcx: TyCtxt<'tcx>,
    ) -> Result<ObservedImages<'images, 'tcx>, String> {
        diagnostics(tcx)?;
        let library = self.library;
        library.inputs.revalidate()?;
        self.revalidate()?;
        unique_native_candidates(tcx, &self.copies)?;
        let (common, target) =
            collect::client_selections(tcx, self.common_files(), &library.prepared.erase.file)?;
        let target = target.ok_or("the client did not load the actual fresh Erase library")?;
        if target.stable_crate_id != library.prepared.erase.view.stable_crate_id
            || target.svh != library.prepared.erase.target_svh
            || target.file.path != library.prepared.erase.file.path
            || target.file.sha256 != library.prepared.erase.file.sha256
            || common.crate_ids() != library.prepared.common.crate_ids()
        {
            return Err(
                "the client macro images are paired with another library/dependency cohort".into(),
            );
        }
        let mut loaded = Vec::new();
        for copy in &self.copies {
            let mut matching = tcx.crates(()).iter().copied().filter(|krate| {
                tcx.used_crate_source(*krate)
                    .dylib
                    .as_ref()
                    .is_some_and(|path| {
                        path.canonicalize()
                            .is_ok_and(|actual| actual == copy.file().path)
                    })
            });
            let krate = matching
                .next()
                .ok_or("a genuine copied macro image was not selected")?;
            if matching.next().is_some() {
                return Err("a copied macro has multiple native identities".into());
            }
            let id = tcx.stable_crate_id(krate).as_u64();
            let svh = tcx.crate_hash(krate).as_u128();
            if library
                .prepared
                .common
                .selected(id, svh, &copy.original().file().path)?
                != common.selected(id, svh, &copy.file().path)?
            {
                return Err(
                    "a copied macro's native CID/SVH/bytes differ from its build origin".into(),
                );
            }
            loaded.push(copy.loaded(tcx, krate)?);
        }
        // Every other dependency keeps its exact original selected path.
        for krate in tcx
            .crates(())
            .iter()
            .copied()
            .filter(|krate| *krate != target.native_crate)
        {
            let source = tcx.used_crate_source(krate);
            let path = source
                .rmeta
                .as_ref()
                .or(source.rlib.as_ref())
                .or(source.dylib.as_ref())
                .ok_or("the native client dependency has no selected metadata")?
                .canonicalize()
                .map_err(|e| e.to_string())?;
            if self.copies.iter().any(|copy| copy.file().path == path) {
                continue;
            }
            let id = tcx.stable_crate_id(krate).as_u64();
            let svh = tcx.crate_hash(krate).as_u128();
            if common.selected(id, svh, &path)?
                != library.prepared.common.selected(id, svh, &path)?
            {
                return Err(
                    "a non-macro client dependency changed its exact native selection".into(),
                );
            }
        }
        diagnostics(tcx)?;
        let dependency_view = self.dependency_view.observation()?;
        Ok(ObservedImages {
            tcx,
            target: target.native_crate,
            loaded,
            common,
            dependency_view,
        })
    }
}

impl<'tcx> ObservedImages<'_, 'tcx> {
    /// Native IDs remain tied to their actual client GCTx. The observation
    /// alone cannot construct a declaration or select another staged packet.
    pub(super) fn current(&self, tcx: TyCtxt<'tcx>) -> Result<(), String> {
        if !std::ptr::eq(*self.tcx, *tcx) {
            return Err("the client image selection belongs to another compiler context".into());
        }
        diagnostics(tcx)
    }

    pub(super) fn target(&self) -> rustc_hir::def_id::CrateNum {
        self.target
    }
    pub(super) fn common(&self) -> &Metadata {
        &self.common
    }

    pub(super) fn observation(&self) -> Value {
        json!({"state": "ObservedClientMacroImages",
            "images": self.loaded.iter().map(build_origin::LoadedMacro::observation).collect::<Vec<_>>(),
            "dependency_view": self.dependency_view,
            "common_native_crates": self.common.crate_ids().len(),
            "Imported_context_authority": "Unknown; independent initialization not established",
            "import_authorized": false})
    }
}
