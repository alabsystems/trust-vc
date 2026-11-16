//! Owned producer handoff. Diagnostic JSON is never its constructor.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

mod client;
pub(super) mod facts;
mod imports;
mod lower;

pub(in crate::reader) use imports::ClientImports;
pub(crate) use imports::LiveNormalClientRead;
pub(super) use imports::PendingVerification;

/// The actual completed producer's native facts and byte/build ownership.
/// Possession alone does not authorize any declaration or function body.
/// The finalizer must establish every per-declaration prerequisite and the
/// consumer must rematch the actual client compiler's CStore selections.
pub(crate) struct StagedLibrary {
    pub(super) inputs: Inputs,
    pub(super) prepared: keep::KeepInputs,
}

impl StagedLibrary {
    pub(super) fn new(inputs: Inputs, prepared: keep::KeepInputs) -> Result<Self, String> {
        inputs.revalidate()?;
        prepared.common.revalidate()?;
        prepared.erase.revalidate_artifacts()?;
        if prepared.erase.view.stable_crate_id != prepared.keep_view.stable_crate_id
            || prepared.erase.view.selected_rmeta_sha256 != Some(prepared.erase.file.sha256)
            || prepared.erase.view.common != prepared.keep_view.common
        {
            return Err(
                "owned Keep/Erase handoff no longer belongs to the same native library".into(),
            );
        }
        for function in &prepared.functions {
            let facts = &function.native;
            if let Some(requirement) = facts.source_header() {
                if !prepared
                    .source_families
                    .values()
                    .any(|family| family.covers(requirement))
                {
                    return Err(
                        "a source header signature lacks its exact complete owned semantic family"
                            .into(),
                    );
                }
            }
            if facts.keep_key() != function.policy.owner()
                || facts.source_identity() != inputs.sources.identity()
                || facts.keep_cfg() != prepared.keep_view.cfg_sha256
                || facts.erase_cfg() != prepared.erase.view.cfg_sha256
                || facts.erase_rmeta() != prepared.erase.file.sha256
                || !prepared.candidates.matches.iter().any(|candidate| {
                    candidate.keep == facts.keep_key() && candidate.erase == facts.erase_key()
                })
                || prepared
                    .erase
                    .roundtrip_unknown
                    .contains_key(&facts.erase_key())
            {
                return Err(
                    "owned function packet does not belong to this exact staged batch".into(),
                );
            }
        }
        // Pending dependency inputs cannot be substituted for the separate
        // signature-only import facts or the separate checked definitions.
        // Both retain their exact source and native counterpart bindings.
        let spec_pairs = spec_graph::Pairs::compare(
            &prepared.spec_view,
            &prepared.erase.spec_view,
            &prepared.erase.spec_roundtrip_unknown,
            spec_graph::nominal_pairs(&prepared.keep_view, &prepared.candidates),
        )?;
        if spec_pairs != prepared.spec_pairs {
            return Err("the retained Spec companion views changed correspondence".into());
        }
        spec_graph::revalidate_all(&inputs, &prepared.spec_pairs, prepared.spec_inputs.values())?;
        for graph in prepared.spec_definitions.values() {
            graph.revalidate(&inputs, &prepared.spec_pairs)?;
        }
        for (root, family) in &prepared.source_families {
            family.revalidate(&inputs, &prepared.spec_pairs)?;
            family.validate_functions(&prepared.functions)?;
            if *root != family.root()
                || prepared
                    .functions
                    .iter()
                    .filter_map(|packet| packet.native.source_header())
                    .filter(|requirement| family.covers(requirement))
                    .count()
                    != 2
            {
                return Err(
                    "the atomic source family lost a required native header/function".into(),
                );
            }
        }
        Ok(Self { inputs, prepared })
    }

    /// A report remains an observation even when all currently checked
    /// prerequisites are retained in the same owner process.
    pub(crate) fn write_observation(&self) -> Result<(), String> {
        self.inputs.revalidate()?;
        self.prepared.common.revalidate()?;
        self.prepared.erase.revalidate_artifacts()?;
        super::write_observation(&self.inputs, &self.prepared.report)
    }
}
