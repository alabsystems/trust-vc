// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Actual fresh outputs and native identities used by the helper checker.

use std::collections::HashSet;
use std::sync::Arc;

use rustc_hir::def::DefKind;
use rustc_hir::def_id::{CrateNum, DefId};
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;

use super::*;
use crate::declaration_alignment::source_bindings::SourceIdentity;

struct Selection {
    stable_crate_id: u64,
    svh: u128,
    artifact: build_origin::BuiltArtifact,
}

pub(super) struct OwnedCohort {
    source: SourceIdentity,
    intrinsic: NativeKey,
    selections: Vec<Selection>,
}

impl OwnedCohort {
    pub(super) fn revalidate(&self, inputs: &Inputs, metadata: &Metadata) -> Result<(), String> {
        inputs.revalidate()?;
        metadata.revalidate()?;
        if inputs.sources.identity() != self.source {
            return Err("the nominal helper source cohort changed".into());
        }
        let fresh = inputs
            .build_origin
            .as_ref()
            .ok_or("nominal helpers require an actual fresh builtin construction")?;
        for selection in &self.selections {
            let file = selection.artifact.file();
            file.read()?;
            if metadata.selected(selection.stable_crate_id, selection.svh, &file.path)?
                != file.sha256
            {
                return Err("a helper builtin/macro native selection changed".into());
            }
            fresh.selected(&inputs.sources, &file.path, file.sha256)?;
        }
        Ok(())
    }
}

pub(in crate::reader::declaration_staging) struct Cohort<'scope, 'tcx> {
    tcx: TyCtxt<'tcx>,
    inputs: &'scope Inputs,
    metadata: &'scope Metadata,
    intrinsic: DefId,
    macro_crates: HashSet<CrateNum>,
    owned: Arc<OwnedCohort>,
    #[cfg(test)]
    transaction_probe: Option<transaction::Probe>,
}

/// A successfully completed helper transaction in its still-live Keep
/// context. The owned helper map alone cannot recreate this borrowed scope.
pub(in crate::reader::declaration_staging) struct ClosedScope<'scope, 'tcx> {
    tcx: TyCtxt<'tcx>,
    inputs: &'scope Inputs,
    metadata: &'scope Metadata,
    intrinsic: DefId,
    owned: Arc<OwnedCohort>,
    owners: Vec<NativeKey>,
}

impl<'tcx> ClosedScope<'_, 'tcx> {
    pub(in crate::reader::declaration_staging) fn current(
        &self,
        tcx: TyCtxt<'tcx>,
        inputs: &Inputs,
        metadata: &Metadata,
        helpers: &BTreeMap<NativeKey, OwnedHelpers>,
    ) -> Result<(), String> {
        diagnostics(tcx)?;
        if !std::ptr::eq(*tcx, *self.tcx)
            || !std::ptr::eq(inputs, self.inputs)
            || !std::ptr::eq(metadata, self.metadata)
            || std::env::var("VSTD_KIND").as_deref() != Ok("IsVstd")
            || declaration_native::key(tcx, self.intrinsic) != self.owned.intrinsic
            || tcx.get_diagnostic_item(Symbol::intern("verus::verus_builtin::get_variant_field"))
                != Some(self.intrinsic)
            || !helpers.keys().copied().eq(self.owners.iter().copied())
            || helpers.iter().any(|(key, helper)| {
                *key != helper.owner || !Arc::ptr_eq(&helper.cohort, &self.owned)
            })
        {
            return Err(
                "the closed helper scope, native context or exact helper map changed".into(),
            );
        }
        Ok(())
    }

    /// Full physical validation brackets a source read. Intermediate views
    /// remain borrowed from this exact context and cannot become import facts.
    pub(in crate::reader::declaration_staging) fn revalidate(
        &self,
        tcx: TyCtxt<'tcx>,
        inputs: &Inputs,
        metadata: &Metadata,
        helpers: &BTreeMap<NativeKey, OwnedHelpers>,
    ) -> Result<(), String> {
        self.current(tcx, inputs, metadata, helpers)?;
        self.owned.revalidate(inputs, metadata)?;
        self.current(tcx, inputs, metadata, helpers)
    }
}

impl<'scope, 'tcx> Cohort<'scope, 'tcx> {
    pub(in crate::reader::declaration_staging) fn capture(
        tcx: TyCtxt<'tcx>,
        inputs: &'scope Inputs,
        metadata: &'scope Metadata,
        work: &mut Work,
    ) -> Result<Self, Failure> {
        let fresh = inputs.build_origin.as_ref().ok_or_else(|| {
            Failure::Unknown("nominal helpers require an actual fresh builtin construction".into())
        })?;
        inputs.revalidate()?;
        metadata.revalidate()?;
        let session = tcx.sess;
        if session.trust_verification_enabled()
            || session.trust_ir_lower_enabled()
            || session.opts.unstable_opts.trust_targo_test_monitor
            || session.opts.unstable_opts.trust_certified_test_monitors
            || session.opts.incremental.is_some()
            || std::env::var("VSTD_KIND").as_deref() != Ok("IsVstd")
            || ["verus_keep_ghost", "verus_keep_ghost_body"]
                .into_iter()
                .any(|name| !session.config.contains(&(Symbol::intern(name), None)))
        {
            return Err(Failure::Unknown(
                "helper capture needs the original unverified Keep Session".into(),
            ));
        }
        let intrinsic = tcx
            .get_diagnostic_item(Symbol::intern("verus::verus_builtin::get_variant_field"))
            .ok_or_else(|| Failure::Unknown("the actual field intrinsic is absent".into()))?;
        if intrinsic.is_local() || tcx.def_kind(intrinsic) != DefKind::Fn {
            return Err(Failure::Unknown(
                "the field intrinsic is not the genuine foreign function".into(),
            ));
        }
        work.charge(tcx, tcx.crates(()).len())?;
        let mut selections = Vec::new();
        let mut macro_crates = HashSet::new();
        let mut selected_files = HashSet::new();
        let mut builtin = false;
        for krate in tcx.crates(()).iter().copied() {
            let source = tcx.used_crate_source(krate);
            let path = source
                .rmeta
                .as_ref()
                .or(source.rlib.as_ref())
                .or(source.dylib.as_ref())
                .ok_or_else(|| {
                    Failure::Unknown("a native helper dependency has no selected path".into())
                })?
                .canonicalize()
                .map_err(|error| Failure::Unknown(error.to_string()))?;
            let expected = if path == inputs.builtin.path {
                Some(&inputs.builtin)
            } else {
                inputs.macros.iter().find(|file| file.path == path)
            };
            let Some(file) = expected else {
                continue;
            };
            if !selected_files.insert(path.clone()) {
                return Err(Failure::Unknown(
                    "a helper artifact has multiple native selections".into(),
                ));
            }
            let stable_crate_id = tcx.stable_crate_id(krate).as_u64();
            let svh = tcx.crate_hash(krate).as_u128();
            if metadata.selected(stable_crate_id, svh, &path)? != file.sha256 {
                return Err(Failure::Unknown(
                    "a helper artifact differs from its native metadata".into(),
                ));
            }
            let artifact = fresh.selected(&inputs.sources, &path, file.sha256)?;
            if path == inputs.builtin.path {
                if krate != intrinsic.krate {
                    return Err(Failure::Unknown(
                        "the field intrinsic is from another selected crate".into(),
                    ));
                }
                builtin = true;
            } else {
                macro_crates.insert(krate);
            }
            selections.push(Selection {
                stable_crate_id,
                svh,
                artifact,
            });
        }
        if !builtin
            || inputs.macros.len() != 2
            || macro_crates.len() != inputs.macros.len()
            || selections.len() != inputs.macros.len() + 1
        {
            return Err(Failure::Unknown(
                "the native helper cohort omits a fresh builtin/macro output".into(),
            ));
        }
        let result = Self {
            tcx,
            inputs,
            metadata,
            intrinsic,
            macro_crates,
            owned: Arc::new(OwnedCohort {
                source: inputs.sources.identity(),
                intrinsic: declaration_native::key(tcx, intrinsic),
                selections,
            }),
            #[cfg(test)]
            transaction_probe: None,
        };
        result.current(tcx, inputs, metadata)?;
        Ok(result)
    }

    pub(super) fn current(
        &self,
        tcx: TyCtxt<'tcx>,
        inputs: &Inputs,
        metadata: &Metadata,
    ) -> Result<(), String> {
        diagnostics(tcx)?;
        if !std::ptr::eq(*tcx, *self.tcx)
            || !std::ptr::eq(inputs, self.inputs)
            || !std::ptr::eq(metadata, self.metadata)
            || std::env::var("VSTD_KIND").as_deref() != Ok("IsVstd")
            || declaration_native::key(tcx, self.intrinsic) != self.owned.intrinsic
            || tcx.get_diagnostic_item(Symbol::intern("verus::verus_builtin::get_variant_field"))
                != Some(self.intrinsic)
        {
            return Err("the helper context or actual intrinsic changed".into());
        }
        // Full physical validation brackets the complete Keep transaction.
        // Intermediate results have the distinct PendingHelpers type and
        // cannot become owned facts until finish consumes this exact scope.
        Ok(())
    }

    pub(in crate::reader::declaration_staging) fn finish(
        self,
        pending: BTreeMap<NativeKey, PendingHelpers>,
    ) -> Result<BTreeMap<NativeKey, OwnedHelpers>, String> {
        #[cfg(test)]
        let mut scope = self;
        #[cfg(test)]
        if let Some(probe) = scope.transaction_probe.take() {
            return probe.finish(scope, pending);
        }
        #[cfg(test)]
        let self_scope = scope;
        #[cfg(not(test))]
        let self_scope = self;
        self_scope.current(self_scope.tcx, self_scope.inputs, self_scope.metadata)?;
        for (key, helper) in &pending {
            if *key != helper.owner || !Arc::ptr_eq(&helper.cohort, &self_scope.owned) {
                return Err(
                    "pending helpers belong to another native construction or owner".into(),
                );
            }
        }
        self_scope
            .owned
            .revalidate(self_scope.inputs, self_scope.metadata)?;
        diagnostics(self_scope.tcx)?;
        Ok(pending
            .into_iter()
            .map(|(key, helper)| {
                (
                    key,
                    OwnedHelpers {
                        owner: helper.owner,
                        local_declarations: helper.local_declarations,
                        helpers: helper.helpers,
                        cohort: helper.cohort,
                    },
                )
            })
            .collect())
    }

    /// Retain live context identity only after the unchanged transaction
    /// finalizer succeeds. A prior owned map or matching NativeKeys cannot
    /// construct this scope or rebind it to another compiler context.
    pub(in crate::reader::declaration_staging) fn finish_with_scope(
        self,
        pending: BTreeMap<NativeKey, PendingHelpers>,
    ) -> Result<(BTreeMap<NativeKey, OwnedHelpers>, ClosedScope<'scope, 'tcx>), String> {
        let closed = ClosedScope {
            tcx: self.tcx,
            inputs: self.inputs,
            metadata: self.metadata,
            intrinsic: self.intrinsic,
            owned: Arc::clone(&self.owned),
            owners: pending.keys().copied().collect(),
        };
        let helpers = self.finish(pending)?;
        closed.current(closed.tcx, closed.inputs, closed.metadata, &helpers)?;
        Ok((helpers, closed))
    }

    #[cfg(test)]
    pub(in crate::reader::declaration_staging) fn with_transaction_probe(
        mut self,
        probe: Option<transaction::Probe>,
    ) -> Self {
        self.transaction_probe = probe;
        self
    }

    pub(super) fn intrinsic(&self) -> DefId {
        self.intrinsic
    }
    pub(super) fn owns_macro(&self, definition: DefId) -> bool {
        !definition.is_local() && self.macro_crates.contains(&definition.krate)
    }
    pub(super) fn owned(&self) -> Arc<OwnedCohort> {
        Arc::clone(&self.owned)
    }
}

#[cfg(test)]
mod tests;
#[cfg(test)]
pub(in crate::reader::declaration_staging) mod transaction;
