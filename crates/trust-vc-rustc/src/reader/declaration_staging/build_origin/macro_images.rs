//! Owned byte-identical images for a later isolated client macro context.
//!
//! Copying is not evidence of independent loader state. Native image lookup
//! and the actual IsVstd/Imported discriminator remain separate prerequisites.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

extern crate rustc_session;

use std::ffi::{CStr, CString};
use std::io::Write;
use std::mem::MaybeUninit;

use rustc_hir::def_id::CrateNum;
use rustc_middle::ty::TyCtxt;

use super::*;

/// Only this actual fresh build can construct a copy origin. The original
/// and destination paths stay distinct and both byte selections are checked.
pub(in crate::reader::declaration_staging) struct CopiedMacro {
    original: BuiltArtifact,
    file: PinnedFile,
    root: PathBuf,
}

/// An observation of the genuine compiler's already-loaded image, not an
/// assertion that its OnceLock was initialized in the intended context.
pub(in crate::reader::declaration_staging) struct LoadedMacro<'copy> {
    copied: &'copy CopiedMacro,
    stable_crate_id: u64,
    svh: u128,
}

impl BuiltCohort {
    pub(in crate::reader::declaration_staging) fn copy_client_macros(
        &self,
        sources: &Sources,
        output: &Path,
    ) -> Result<Vec<CopiedMacro>, String> {
        self.revalidate(sources)?;
        let output = super::super::inputs::canonical_output(output, sources.root())?;
        std::fs::create_dir(&output).map_err(|e| e.to_string())?;
        let mut copies = Vec::new();
        for name in [
            "libverus_builtin_macros.dylib",
            "libverus_state_machines_macros.dylib",
        ] {
            let original_file = self.artifact(name)?;
            let original = self.selected(sources, &original_file.path, original_file.sha256)?;
            let path = output.join(name);
            let mut created = std::fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&path)
                .map_err(|e| e.to_string())?;
            created
                .write_all(&original_file.read()?)
                .map_err(|e| e.to_string())?;
            created.sync_all().map_err(|e| e.to_string())?;
            let file = super::output_artifact(&output, name)?;
            let copy = CopiedMacro {
                original,
                file,
                root: output.clone(),
            };
            copy.revalidate()?;
            copies.push(copy);
        }
        self.revalidate(sources)?;
        Ok(copies)
    }
}

impl CopiedMacro {
    pub(in crate::reader::declaration_staging) fn file(&self) -> &PinnedFile {
        &self.file
    }
    pub(in crate::reader::declaration_staging) fn original(&self) -> &BuiltArtifact {
        &self.original
    }

    pub(in crate::reader::declaration_staging) fn revalidate(&self) -> Result<(), String> {
        self.original.file.read()?;
        let name = self
            .file
            .path
            .file_name()
            .and_then(|name| name.to_str())
            .ok_or("a copied macro has no represented filename")?;
        let actual = super::output_artifact(&self.root, name)?;
        if actual.path != self.file.path
            || actual.sha256 != self.file.sha256
            || self.file.sha256 != self.original.file.sha256
            || self.file.path == self.original.file.path
        {
            return Err(
                "the copied macro is not the distinct regular byte-identical owned image".into(),
            );
        }
        Ok(())
    }

    /// RTLD_NOLOAD makes this an observation only: this routine cannot load
    /// an image, run initializers, or replace rustc's own proc-macro boundary.
    pub(in crate::reader::declaration_staging) fn loaded<'copy>(
        &'copy self,
        tcx: TyCtxt<'_>,
        krate: CrateNum,
    ) -> Result<LoadedMacro<'copy>, String> {
        self.revalidate()?;
        if tcx.dcx().has_errors().is_some() {
            return Err("native diagnostics reject loaded macro provenance".into());
        }
        let source = tcx.used_crate_source(krate);
        let selected = source
            .dylib
            .as_ref()
            .ok_or("the native macro crate has no selected dylib")?
            .canonicalize()
            .map_err(|e| e.to_string())?;
        if selected != self.file.path {
            return Err("the native macro CStore selection is not this exact owned copy".into());
        }
        let id = tcx.stable_crate_id(krate);
        let symbol = rustc_session::generate_proc_macro_decls_symbol(id);
        let loaded = loaded_image(&self.file.path, &symbol)?;
        if loaded != self.file.path {
            return Err(
                "the native loader coalesced the copied proc macro with another image".into(),
            );
        }
        Ok(LoadedMacro {
            copied: self,
            stable_crate_id: id.as_u64(),
            svh: tcx.crate_hash(krate).as_u128(),
        })
    }
}

impl LoadedMacro<'_> {
    pub(in crate::reader::declaration_staging) fn observation(&self) -> serde_json::Value {
        serde_json::json!({"state": "ObservedDistinctLoadedMacroImage",
            "stable_crate_id": format!("{:016x}", self.stable_crate_id),
            "svh": format!("{:032x}", self.svh),
            "loaded_path": self.copied.file.path,
            "sha256": self.copied.file.sha256,
            "origin": self.copied.original.observation(),
            "independent_Imported_context": "Unknown; actual discriminator required",
            "import_authorized": false})
    }
}

fn loaded_image(path: &Path, symbol: &str) -> Result<PathBuf, String> {
    let path = path
        .to_str()
        .ok_or("the copied macro path is not represented")?;
    let path = CString::new(path).map_err(|e| e.to_string())?;
    let symbol = CString::new(symbol).map_err(|e| e.to_string())?;
    // The matching dlclose releases only this NOLOAD observation reference.
    // Rustc intentionally retains its own original loader handle forever.
    let handle = unsafe { libc::dlopen(path.as_ptr(), libc::RTLD_NOW | libc::RTLD_NOLOAD) };
    if handle.is_null() {
        return Err("the expected macro image is not already loaded".into());
    }
    let result = (|| {
        let address = unsafe { libc::dlsym(handle, symbol.as_ptr()) };
        if address.is_null() {
            return Err("the loaded image lacks its native proc-macro declarations symbol".into());
        }
        let mut info = MaybeUninit::<libc::Dl_info>::uninit();
        if unsafe { libc::dladdr(address, info.as_mut_ptr()) } == 0 {
            return Err("the actual proc-macro symbol image could not be identified".into());
        }
        let info = unsafe { info.assume_init() };
        if info.dli_fname.is_null() {
            return Err("the actual proc-macro image has no native path".into());
        }
        let filename = unsafe { CStr::from_ptr(info.dli_fname) }
            .to_str()
            .map_err(|e| e.to_string())?;
        PathBuf::from(filename)
            .canonicalize()
            .map_err(|e| e.to_string())
    })();
    if unsafe { libc::dlclose(handle) } != 0 {
        return Err("the native macro observation handle could not be released".into());
    }
    result
}
