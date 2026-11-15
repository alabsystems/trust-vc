//! Validate local datatype positivity and base cases without exporting fields.
//!
//! The field types come from original local source, never foreign private
//! metadata. Builtin meanings are conditional on the exact native definitions
//! recorded below: the staging owner must authenticate those selections before
//! consuming these facts. No observation file can construct a sealed value.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_hir::def_id::DefId;
use rustc_hir::{self as hir, OwnerNode};
use rustc_middle::ty::TyCtxt;
use serde_json::{json, Value};

use crate::declaration_alignment::NativeKey;

use super::declaration_policy::CheckedPolicy;

mod graph;
mod native;
#[cfg(test)]
mod tests;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum BuiltinRole {
    SpecFunction,
    MathematicalInteger,
    NaturalNumber,
    OwnedBox,
}

/// Actual native identity whose language meaning this check used. A diagnostic
/// item by itself is not build authentication. The producer must match both the
/// key and SVH to its authenticated selected compiler/builtin artifact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct BuiltinRequirement {
    pub(super) role: BuiltinRole,
    pub(super) definition: NativeKey,
    pub(super) crate_svh: u128,
}

/// No representation or axioms escape. All listed local declarations passed
/// both checks; their source identities and the builtin selections still need
/// the actual staging producer's source/build binding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct OwnedWf {
    owner: NativeKey,
    local_declarations: Vec<NativeKey>,
    builtins: Vec<BuiltinRequirement>,
}

impl OwnedWf {
    pub(super) fn owner(&self) -> NativeKey {
        self.owner
    }
    pub(super) fn local_declarations(&self) -> &[NativeKey] {
        &self.local_declarations
    }
    pub(super) fn builtin_requirements(&self) -> &[BuiltinRequirement] {
        &self.builtins
    }
}

pub(super) struct CheckedWf<'policy, 'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: DefId,
    policy: &'policy CheckedPolicy<'tcx>,
    checked_owners: Vec<DefId>,
    facts: Result<OwnedWf, String>,
}

impl<'tcx> CheckedWf<'_, 'tcx> {
    pub(super) fn for_owner(&self, tcx: TyCtxt<'tcx>, owner: DefId) -> Option<&OwnedWf> {
        if owner != self.owner
            || !std::ptr::eq(*tcx, *self.tcx)
            || self.policy.for_owner(tcx, owner).is_none()
            || tcx.dcx().has_errors().is_some()
            || self
                .checked_owners
                .iter()
                .any(|owner| !original(tcx, *owner))
        {
            return None;
        }
        self.facts.as_ref().ok()
    }

    pub(super) fn owned_for(&self, tcx: TyCtxt<'tcx>, owner: DefId) -> Option<OwnedWf> {
        self.for_owner(tcx, owner).cloned()
    }

    /// The live original local owners covered by this check. These IDs are
    /// available only with the matching compiler context; they are never part
    /// of the owned metadata handoff.
    pub(super) fn local_owners(&self, tcx: TyCtxt<'tcx>, owner: DefId) -> Option<&[DefId]> {
        self.for_owner(tcx, owner)?;
        Some(&self.checked_owners)
    }

    pub(super) fn observation(&self) -> Value {
        let Some(facts) = self.for_owner(self.tcx, self.owner) else {
            return json!({"state": "Unknown", "reason": self.facts.as_ref().err()
                .map(String::as_str).unwrap_or("original native owners are no longer established"),
                "import_authorized": false});
        };
        json!({"state": "CheckedConditionalNativeNominalWf",
            "owner": key_json(facts.owner),
            "local_declarations": facts.local_declarations.iter().copied().map(key_json).collect::<Vec<_>>(),
            "required_builtin_selections": facts.builtins.iter().map(|builtin| json!({
                "role": format!("{:?}", builtin.role), "definition": key_json(builtin.definition),
                "crate_svh": format!("{:032x}", builtin.crate_svh),
            })).collect::<Vec<_>>(),
            "positivity_and_base_cases_checked": true,
            "builtin_and_source_build_authentication": "separate producer obligation",
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

pub(super) fn original(tcx: TyCtxt<'_>, owner: DefId) -> bool {
    let Some(local) = owner.as_local() else {
        return false;
    };
    let Some(raw) = tcx.lower_to_hir(local).as_owner() else {
        return false;
    };
    matches!((raw.node(), tcx.hir_node_by_def_id(local)),
        (OwnerNode::Item(a), hir::Node::Item(b)) if std::ptr::eq(a, b))
}

pub(super) fn check<'policy, 'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: DefId,
    policy: &'policy CheckedPolicy<'tcx>,
) -> CheckedWf<'policy, 'tcx> {
    let mut checked_owners = Vec::new();
    let facts = (|| {
        let policy = policy
            .for_owner(tcx, owner)
            .ok_or("no sealed policy for this native owner")?;
        if policy.nominal().is_none() {
            return Err("well-foundedness needs a nominal declaration".into());
        }
        let captured = native::capture(tcx, owner)?;
        graph::validate(&captured.graph).map_err(|failure| failure.to_string())?;
        checked_owners = captured.owners;
        if tcx.dcx().has_errors().is_some()
            || checked_owners.iter().any(|owner| !original(tcx, *owner))
        {
            return Err(
                "native datatype checking emitted errors or changed an original owner".into(),
            );
        }
        Ok(OwnedWf {
            owner: key(tcx, owner),
            local_declarations: checked_owners
                .iter()
                .map(|owner| key(tcx, *owner))
                .collect(),
            builtins: captured.builtins,
        })
    })();
    CheckedWf {
        tcx,
        owner,
        policy,
        checked_owners,
        facts,
    }
}

/// A checked local closure in the actual importing reader. This fact borrows
/// that exact Cx, so it cannot become an owned foreign policy or survive its
/// client context. It supplies only positivity and base cases, never fields,
/// construction, field-language admission or ownership permission.
pub(super) struct ClientWf<'context, 'tcx> {
    cx: &'context super::Cx<'tcx>,
    owner: DefId,
    owners: Vec<DefId>,
    imported: Vec<DefId>,
}

/// A language judgement is attributed to an actual original local owner.
/// Unavailable native facts, changed context and bounded-work refusals cannot
/// be classified as source language errors by inspecting an error string.
#[derive(Debug)]
pub(super) enum ClientError {
    Unknown(String),
    NonPositiveDatatype {
        owner: DefId,
        target: DefId,
    },
    NonPositiveParameter {
        owner: DefId,
        parameter: u32,
    },
    /// The caller selects the first primary in native Verus dependency-SCC
    /// order, never the order this root's closure happened to be captured.
    NoBase {
        owners: Vec<DefId>,
    },
}

impl From<String> for ClientError {
    fn from(reason: String) -> Self {
        Self::Unknown(reason)
    }
}

impl From<&str> for ClientError {
    fn from(reason: &str) -> Self {
        Self::Unknown(reason.into())
    }
}

fn client_error(failure: graph::Failure, owners: &[DefId]) -> ClientError {
    use graph::Failure;
    match failure {
        Failure::Unknown(reason) => ClientError::Unknown(reason),
        Failure::NonPositiveDatatype { owner, target } => {
            match owners.get(owner).copied().zip(owners.get(target).copied()) {
                Some((owner, target)) => ClientError::NonPositiveDatatype { owner, target },
                None => ClientError::Unknown(
                    "the recursive failure has no original local owners".into(),
                ),
            }
        }
        Failure::NonPositiveParameter { owner, parameter } => match owners.get(owner).copied() {
            Some(owner) => ClientError::NonPositiveParameter { owner, parameter },
            None => {
                ClientError::Unknown("the parameter failure has no original local owner".into())
            }
        },
        Failure::NoBase { owners: indices } => {
            match indices
                .iter()
                .map(|index| owners.get(*index).copied())
                .collect::<Option<Vec<_>>>()
            {
                Some(owners) if !owners.is_empty() => ClientError::NoBase { owners },
                _ => ClientError::Unknown(
                    "the base-case failure has no complete original local inventory".into(),
                ),
            }
        }
    }
}

impl<'tcx> ClientWf<'_, 'tcx> {
    pub(super) fn local_owners(&self, cx: &super::Cx<'tcx>, owner: DefId) -> Option<&[DefId]> {
        if !std::ptr::eq(self.cx, cx)
            || owner != self.owner
            || cx.tcx.dcx().has_errors().is_some()
            || self.owners.iter().any(|owner| !original(cx.tcx, *owner))
            || self
                .imported
                .iter()
                .any(|definition| cx.imported_nominal_policy(*definition).is_none())
        {
            return None;
        }
        Some(&self.owners)
    }
}

/// Validate original local field types using only the current registry's
/// sealed foreign summaries. Conditional builtin meanings introduced by those
/// local fields must already be covered by authenticated current selections.
pub(super) fn check_client<'context, 'tcx>(
    cx: &'context super::Cx<'tcx>,
    owner: DefId,
) -> Result<ClientWf<'context, 'tcx>, ClientError> {
    let captured = native::capture_client(cx, owner)?;
    if cx.tcx.dcx().has_errors().is_some()
        || captured
            .owners
            .iter()
            .any(|owner| !original(cx.tcx, *owner))
        || captured
            .imported
            .iter()
            .any(|definition| cx.imported_nominal_policy(*definition).is_none())
    {
        return Err(ClientError::Unknown(
            "local wrapper checking lost its original native context".into(),
        ));
    }
    if captured
        .builtins
        .iter()
        .any(|requirement| !cx.imported_wf_requirement(requirement))
    {
        return Err(ClientError::Unknown(
            "a local wrapper needs an authenticated current builtin meaning".into(),
        ));
    }
    graph::validate(&captured.graph).map_err(|failure| client_error(failure, &captured.owners))?;
    let checked = ClientWf {
        cx,
        owner,
        owners: captured.owners,
        imported: captured.imported,
    };
    checked
        .local_owners(cx, owner)
        .ok_or("local wrapper checking lost its original owner or client context")?;
    Ok(checked)
}
