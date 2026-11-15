// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! One request owns its parsed options and both native projections. This is
//! request data, not an import capability or a native checking result.

use super::*;
use crate::declaration_alignment::source_bindings::PinnedFile;
use crate::reader::declaration_staging::NormalClientArgs;
use sha2::{Digest as _, Sha256};
use std::path::Path;

struct EntrySource {
    operand: PathBuf,
    file: PinnedFile,
}

impl EntrySource {
    fn capture(operand: &str) -> Result<Self, String> {
        let operand = std::env::current_dir()
            .map_err(|e| e.to_string())?
            .join(operand);
        let path = operand.canonicalize().map_err(|e| e.to_string())?;
        if !std::fs::metadata(&path)
            .map_err(|e| e.to_string())?
            .is_file()
        {
            return Err("the normal invocation snapshot requires a regular source file".into());
        }
        let bytes = std::fs::read(&path).map_err(|e| e.to_string())?;
        let file = PinnedFile {
            path,
            sha256: Sha256::digest(&bytes).into(),
        };
        file.read()?;
        Ok(Self { operand, file })
    }

    fn revalidate(&self) -> Result<(), String> {
        if self.operand.canonicalize().map_err(|e| e.to_string())? != self.file.path {
            return Err("the normal invocation source path changed its actual target".into());
        }
        self.file.read()?;
        Ok(())
    }
}

pub(crate) struct NormalInvocation {
    verify: Vec<String>,
    erase: Vec<String>,
    opts: RunOptions,
    original: Option<SplitArgs>,
    source: Result<EntrySource, String>,
}

impl NormalInvocation {
    pub(crate) fn derive(program: String, split: SplitArgs) -> Result<Self, String> {
        if let Some(problem) = argument_error(&split) {
            return Err(problem);
        }
        let mut common = vec![program];
        common.extend(split.rustc.iter().cloned());
        if !split.rustc.iter().any(|a| a.starts_with("--edition")) {
            common.extend(["--edition".to_string(), "2021".to_string()]);
        }
        common.extend(verus_rustc_flags());
        let mut verify = common.clone();
        for cfg in VERIFY_RUN_CFGS {
            verify.extend(["--cfg".to_string(), cfg.to_string()]);
        }
        let mut erase = common;
        for cfg in ERASE_RUN_CFGS {
            erase.extend(["--cfg".to_string(), cfg.to_string()]);
        }
        for allow in ERASE_RUN_ALLOWS {
            erase.extend(["-A".to_string(), allow.to_string()]);
        }
        let opts = RunOptions::from_split(&split, erase.clone())?;
        // Missing/unreadable rustc inputs still receive rustc's original
        // front-end diagnostics in ordinary main. An owned binder must have
        // a real snapshot and cannot turn this missing fact into permission.
        let source = split
            .entry_file()
            .ok_or_else(|| "normal invocation has no represented source".to_string())
            .and_then(EntrySource::capture);
        Ok(Self {
            verify,
            erase,
            opts,
            original: Some(split),
            source,
        })
    }

    /// Only the existing owner-built opaque pair constructs this explicit
    /// default instance. No API accepts caller-provided paired vectors.
    pub(crate) fn closed_standalone(args: NormalClientArgs) -> Result<Self, String> {
        let split = SplitArgs::default();
        let verify = args.verify().to_vec();
        let erase = args.erase().to_vec();
        let parsed = args::split(verify.get(1..).unwrap_or(&[])).map_err(|e| e.to_string())?;
        let source = parsed
            .entry_file()
            .ok_or_else(|| "closed normal invocation has no source".to_string())
            .and_then(EntrySource::capture);
        let opts = RunOptions::from_split(&split, erase.clone())?;
        Ok(Self {
            verify,
            erase,
            opts,
            original: None,
            source,
        })
    }

    pub(crate) fn verify(&self) -> &[String] {
        &self.verify
    }
    pub(crate) fn erase(&self) -> &[String] {
        &self.erase
    }
    pub(crate) fn expects_erase(&self) -> bool {
        self.opts.erase_args.is_some()
    }
    pub(crate) fn original(&self) -> Option<&SplitArgs> {
        self.original.as_ref()
    }
    pub(super) fn options(&self) -> RunOptions {
        self.opts.clone()
    }

    pub(crate) fn source_matches(&self, expected: &PinnedFile) -> Result<(), String> {
        let source = self.source.as_ref().map_err(Clone::clone)?;
        source.revalidate()?;
        if source.file.path != expected.path || source.file.sha256 != expected.sha256 {
            return Err("the owned source is not the original normal invocation source".into());
        }
        expected.read()?;
        Ok(())
    }

    pub(crate) fn source_operand(&self) -> Result<&Path, String> {
        Ok(&self.source.as_ref().map_err(Clone::clone)?.operand)
    }

    pub(super) fn check_native_source(&self, tcx: TyCtxt<'_>) -> Result<(), String> {
        let source = self.source.as_ref().map_err(Clone::clone)?;
        source.revalidate()?;
        let actual = tcx
            .sess
            .io
            .input
            .opt_path()
            .ok_or("the normal Session has no actual source operand")?;
        let actual = std::env::current_dir()
            .map_err(|e| e.to_string())?
            .join(actual);
        if actual != source.operand {
            return Err(
                "the normal preparation Session belongs to another invocation source".into(),
            );
        }
        let file = tcx
            .sess
            .source_map()
            .lookup_source_file(tcx.hir_root_module().spans.inner_span.lo());
        let FileName::Real(name) = &file.name else {
            return Err("the normal preparation has no original physical source".into());
        };
        let path = name
            .local_path()
            .ok_or("the normal native source has no local path")?;
        let bytes = source.file.read()?;
        if path.canonicalize().map_err(|e| e.to_string())? != source.file.path
            || usize::try_from(file.unnormalized_source_len).ok() != Some(bytes.len())
            || !crate::declaration_alignment::source_bindings::compiler_hash_matches(
                &file.src_hash.to_string(),
                &bytes,
            )?
        {
            return Err(
                "the actual normal compiler source differs from its invocation snapshot".into(),
            );
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests;
