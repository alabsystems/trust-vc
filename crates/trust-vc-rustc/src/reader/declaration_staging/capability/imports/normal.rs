// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A live normal reader, not the dedicated ghost-only verification capability.
//! Only the exact owned registry's actual read constructs this value. It stays
//! borrowed through normal MIR, erase/impl comparison and solver verification.

use super::super::super::macro_context::ClientSource;
use super::*;
use crate::reader::{CrateRead, FnStatus};
use crate::shim::NormalReadBinding;

pub(crate) struct LiveNormalClientRead<'scope, 'library, 'run, 'tcx> {
    imports: &'scope ClientImports<'library, 'tcx>,
    tcx: TyCtxt<'tcx>,
    source: &'scope ClientSource,
    read: CrateRead,
    binding: NormalReadBinding<'run>,
}

impl<'library, 'tcx> ClientImports<'library, 'tcx> {
    pub(in crate::reader::declaration_staging) fn read_for_normal_verification<'scope, 'run>(
        &'scope self,
        preparation: &crate::shim::NormalReadScope<'run, '_, '_, 'tcx>,
        source: &'scope ClientSource,
    ) -> Result<LiveNormalClientRead<'scope, 'library, 'run, 'tcx>, String> {
        let tcx = preparation.tcx();
        preparation.plan().check_owner(self.frame.owner(), source)?;
        let binding = preparation.binding();
        if !binding.source_matches(source.file()) {
            return Err("the normal read source differs from its sealed preparation".into());
        }
        self.revalidate(tcx)?;
        source.file().read()?;
        let read = self.read(tcx, binding.read_options())?;
        let live = LiveNormalClientRead {
            imports: self,
            tcx,
            source,
            read,
            binding,
        };
        live.ready_for_solver(tcx)?;
        Ok(live)
    }
}

impl<'tcx> LiveNormalClientRead<'_, '_, '_, 'tcx> {
    pub(crate) fn matches_preparation(
        &self,
        tcx: TyCtxt<'tcx>,
        binding: NormalReadBinding<'_>,
    ) -> bool {
        std::ptr::eq(*self.tcx, *tcx)
            && self.binding.same_run(&binding)
            && binding.source_matches(self.source.file())
    }
    /// Diagnostic-insensitive identity checks grant no new authority. They
    /// still run on ownership/error exits, so the canonical erase child can
    /// report both proof and exec errors without reviving a poisoned reader.
    pub(crate) fn check_retained_inputs(&self, tcx: TyCtxt<'tcx>) -> Result<(), String> {
        if !std::ptr::eq(*self.tcx, *tcx) {
            return Err("the normal read belongs to another compiler context".into());
        }
        self.binding.revalidate_source()?;
        self.source.file().read()?;
        self.imports.frame.check_retained_inputs(tcx)?;
        self.imports
            .library
            .prepared
            .erase
            .target_metadata
            .revalidate()
    }

    pub(crate) fn ready_for_solver(&self, tcx: TyCtxt<'tcx>) -> Result<(), String> {
        self.check_retained_inputs(tcx)?;
        self.imports.revalidate(tcx)?;
        if self.read.fns.is_empty()
            || self.read.fns.len() > 256
            || self.read.krate.fns.len() > 16_384
            || self.read.spans.len() > 65_536
            || self.read.krate.adts.len() > 16_384
            || self.imports.functions.len() > 16_384
        {
            return Err("the normal owned read exceeds its retained-input bound".into());
        }
        // Retain every local record and all normal rejection/deferred states.
        // Their language/ownership policy is decided by VerifyRun::decide,
        // never by weakening LiveClientRead::ready's ghost-only predicate.
        for record in &self.read.fns {
            if let FnStatus::Read(id) = &record.status {
                if self.read.fn_defs.get(id) != Some(&record.def_id)
                    || *id
                        != FnId(hash(declaration_native::key(
                            tcx,
                            record.def_id.to_def_id(),
                        )))
                    || !super::super::super::super::declaration_modes::original_body_available(
                        tcx,
                        record.def_id,
                    )
                {
                    return Err("the original local normal body/identity changed".into());
                }
            }
        }
        let mut installed = std::collections::HashSet::new();
        for declaration in &self.read.krate.fns {
            if declaration.role != FnRole::Imported {
                continue;
            }
            let function = self
                .imports
                .functions
                .values()
                .find(|f| f.id == declaration.id)
                .ok_or("an imported normal declaration has no owned native origin")?;
            if function.definition.is_local()
                || !installed.insert(declaration.id)
                || *declaration != function.declaration(declaration.span)
            {
                return Err(
                    "an imported signature acquired clauses, body or instance authority".into(),
                );
            }
        }
        if installed.len() != self.imports.functions.len() {
            return Err("the complete normal import inventory changed".into());
        }
        diagnostics(tcx)
    }

    pub(crate) fn with_read<R>(&self, action: impl FnOnce(TyCtxt<'tcx>, &CrateRead) -> R) -> R {
        action(self.tcx, &self.read)
    }

    pub(in crate::reader::declaration_staging) fn imported_count(&self) -> usize {
        self.imports.functions.len()
    }

    pub(in crate::reader::declaration_staging) fn imported_spec_definition_count(&self) -> usize {
        self.read.spec_definitions.len()
    }

    pub(in crate::reader::declaration_staging) fn native_ownership_roots(&self) -> usize {
        self.read.native_ownership.len()
    }
}
