//! Original local field-language admission for an abstract declaration packet.
//!
//! This checks types and resolves declaration modes, but exports no fields,
//! constructors or representation axioms. Builtin meanings, external mappings
//! and source identities remain conditional on the actual staging producer's
//! source/build/selected-artifact binding. JSON never creates these facts.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use serde_json::{json, Value};

use crate::declaration_alignment::NativeKey;

use super::declaration_policy::CheckedPolicy;
use super::declaration_wf::{self, CheckedWf};

mod attributes;
mod native;
mod proxy;
#[cfg(test)]
mod tests;

/// An authored, checked external type specification. Only the proxy's original
/// local definition and the exact foreign target are retained, not its fields.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ExternalMapping {
    pub(super) proxy: NativeKey,
    pub(super) target: NativeKey,
    pub(super) target_svh: u128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct OwnedFields {
    owner: NativeKey,
    local_declarations: Vec<NativeKey>,
    mappings: Vec<ExternalMapping>,
}

impl OwnedFields {
    pub(super) fn owner(&self) -> NativeKey {
        self.owner
    }
    pub(super) fn local_declarations(&self) -> &[NativeKey] {
        &self.local_declarations
    }
    pub(super) fn external_mappings(&self) -> &[ExternalMapping] {
        &self.mappings
    }
}

pub(super) struct CheckedFields<'facts, 'policy, 'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: DefId,
    wf: &'facts CheckedWf<'policy, 'tcx>,
    proxies: Vec<DefId>,
    facts: Result<OwnedFields, String>,
}

impl<'tcx> CheckedFields<'_, '_, 'tcx> {
    pub(super) fn for_owner(&self, tcx: TyCtxt<'tcx>, owner: DefId) -> Option<&OwnedFields> {
        if owner != self.owner
            || !std::ptr::eq(*tcx, *self.tcx)
            || self.wf.for_owner(tcx, owner).is_none()
            || tcx.dcx().has_errors().is_some()
            || self
                .proxies
                .iter()
                .any(|proxy| !declaration_wf::original(tcx, *proxy))
        {
            return None;
        }
        self.facts.as_ref().ok()
    }

    pub(super) fn owned_for(&self, tcx: TyCtxt<'tcx>, owner: DefId) -> Option<OwnedFields> {
        self.for_owner(tcx, owner).cloned()
    }

    pub(super) fn observation(&self) -> Value {
        let Some(facts) = self.for_owner(self.tcx, self.owner) else {
            return json!({"state": "Unknown", "reason": self.facts.as_ref().err()
                .map(String::as_str).unwrap_or("native field context is no longer established"),
                "import_authorized": false});
        };
        json!({"state": "CheckedConditionalNativeFieldLanguage",
            "owner": key_json(facts.owner),
            "local_declarations": facts.local_declarations.iter().copied().map(key_json).collect::<Vec<_>>(),
            "required_external_mappings": facts.mappings.iter().map(|mapping| json!({
                "proxy": key_json(mapping.proxy), "target": key_json(mapping.target),
                "target_svh": format!("{:032x}", mapping.target_svh),
            })).collect::<Vec<_>>(),
            "field_types_and_declaration_modes_checked": true,
            "source_builtin_and_mapping_build_binding": "separate producer obligation",
            "field_access_or_constructor_authority": false,
            "private_representation_exported": false, "import_authorized": false})
    }
}

fn key_json(key: NativeKey) -> Value {
    json!({"stable_crate_id": format!("{:016x}", key.stable_crate_id),
        "def_path_hash": format!("{:032x}", key.def_path_hash)})
}

fn key(tcx: TyCtxt<'_>, owner: DefId) -> NativeKey {
    let (high, low) = tcx.def_path_hash(owner).0.split();
    NativeKey {
        stable_crate_id: tcx.stable_crate_id(owner.krate).as_u64(),
        def_path_hash: (u128::from(high.as_u64()) << 64) | u128::from(low.as_u64()),
    }
}

pub(super) fn check<'facts, 'policy, 'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: DefId,
    policy: &CheckedPolicy<'tcx>,
    wf: &'facts CheckedWf<'policy, 'tcx>,
) -> CheckedFields<'facts, 'policy, 'tcx> {
    let mut proxies = Vec::new();
    let facts = (|| {
        let policy = policy
            .for_owner(tcx, owner)
            .ok_or("no native policy for field admission")?;
        if policy.nominal().is_none() {
            return Err("field admission requires a nominal owner".into());
        }
        let owners = wf
            .local_owners(tcx, owner)
            .ok_or("no same-context native positivity/base-case fact")?;
        if owners.is_empty() || !owners.contains(&owner) {
            return Err("native WF inventory omits its owner".into());
        }
        let captured = native::check(tcx, owner, wf)?;
        proxies = captured.proxies;
        if tcx.dcx().has_errors().is_some()
            || proxies
                .iter()
                .any(|proxy| !declaration_wf::original(tcx, *proxy))
        {
            return Err("field admission emitted diagnostics or changed a mapping owner".into());
        }
        Ok(OwnedFields {
            owner: key(tcx, owner),
            local_declarations: owners.iter().map(|owner| key(tcx, *owner)).collect(),
            mappings: captured.mappings,
        })
    })();
    CheckedFields {
        tcx,
        owner,
        wf,
        proxies,
        facts,
    }
}
