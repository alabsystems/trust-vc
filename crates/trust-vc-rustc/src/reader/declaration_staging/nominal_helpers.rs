//! Original Keep helper-language facts for a nominal declaration closure.
//!
//! Native source, expansion and representation facts stay conditional on the
//! actual staging cohort. Neither observations nor this interface fact prove
//! a helper body, confer ownership, or expose a foreign representation.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashSet;
use std::sync::Arc;

use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::TyCtxt;

use super::*;
use crate::reader::modes::{self, ModeCheck};

mod cohort;
mod context;
mod helper;
mod inline;
mod inventory;
mod origin;
mod types;

#[cfg(test)]
pub(super) use cohort::transaction::Probe as TransactionProbe;
pub(super) use cohort::{ClosedScope, Cohort};

/// The same counter pays for cohort, owner, expansion, type and body inventory.
pub(super) struct Work {
    remaining: usize,
}

impl Work {
    pub(super) fn new() -> Self {
        Self { remaining: 262_144 }
    }

    fn charge(&mut self, tcx: TyCtxt<'_>, amount: usize) -> Result<(), Failure> {
        diagnostics(tcx).map_err(Failure::Unknown)?;
        self.remaining = self
            .remaining
            .checked_sub(amount)
            .ok_or_else(|| Failure::Unknown("nominal helper work bound was exhausted".into()))?;
        Ok(())
    }
}

#[derive(Debug)]
pub(super) enum Failure {
    Unknown(String),
    UnknownWithContext { reason: String, context: Value },
    Modes(super::super::UserError),
}

impl From<String> for Failure {
    fn from(reason: String) -> Self {
        Self::Unknown(reason)
    }
}

impl Failure {
    pub(super) fn observation(&self) -> Value {
        match self {
            Self::Unknown(reason) => json!({"state": "Unknown", "reason": reason}),
            Self::UnknownWithContext { reason, context } => json!({"state": "Unknown",
                "reason": reason, "origin_refusal_context": context}),
            Self::Modes(error) => json!({"state": "NativeHelperModeError",
                "message": error.message, "span_debug": format!("{:?}", error.span)}),
        }
    }
}

/// Only this module's completed native capture can create this fourth fact.
pub(super) struct OwnedHelpers {
    owner: NativeKey,
    local_declarations: Vec<NativeKey>,
    helpers: Vec<NativeKey>,
    cohort: Arc<cohort::OwnedCohort>,
}

/// Native language results awaiting the whole Keep transaction's final
/// physical-input and native-cohort validation. This is not an owned fact.
pub(super) struct PendingHelpers {
    owner: NativeKey,
    local_declarations: Vec<NativeKey>,
    helpers: Vec<NativeKey>,
    cohort: Arc<cohort::OwnedCohort>,
}

fn observation(owner: NativeKey, local_declarations: usize, helpers: usize) -> Value {
    json!({"state": "CheckedOriginalNominalHelperClosure",
        "owner": format!("{:032x}", owner.def_path_hash),
        "local_declarations": local_declarations, "helpers": helpers,
        "representation_exported": false, "verified_functions": null,
        "ownership_authorized": false, "import_authorized": false})
}

impl PendingHelpers {
    fn observation(&self) -> Value {
        observation(
            self.owner,
            self.local_declarations.len(),
            self.helpers.len(),
        )
    }
}

impl OwnedHelpers {
    pub(super) fn owner(&self) -> NativeKey {
        self.owner
    }
    pub(super) fn local_declarations(&self) -> &[NativeKey] {
        &self.local_declarations
    }

    pub(super) fn revalidate(&self, inputs: &Inputs, metadata: &Metadata) -> Result<(), String> {
        self.cohort.revalidate(inputs, metadata)
    }

    pub(super) fn observation(&self) -> Value {
        observation(
            self.owner,
            self.local_declarations.len(),
            self.helpers.len(),
        )
    }
}

/// A Keep packet comes from one actual native construction. Check that every
/// fact retains that same Arc, then validate it once for this finalizer
/// operation. Later consumers must perform their own validation.
pub(super) fn revalidate_all<'a>(
    inputs: &Inputs,
    metadata: &Metadata,
    helpers: impl IntoIterator<Item = &'a OwnedHelpers>,
) -> Result<(), String> {
    let mut checked: Option<&Arc<cohort::OwnedCohort>> = None;
    for helper in helpers {
        if let Some(cohort) = checked {
            if !Arc::ptr_eq(cohort, &helper.cohort) {
                return Err("a Keep helper packet mixes native construction scopes".into());
            }
        } else {
            checked = Some(&helper.cohort);
        }
    }
    if let Some(cohort) = checked {
        cohort.revalidate(inputs, metadata)?;
    }
    Ok(())
}

/// The borrowed prerequisites cannot be replaced by an owned observation.
pub(super) struct CheckedHelpers<'check, 'facts, 'policy, 'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: DefId,
    policy: &'check declaration_policy::CheckedPolicy<'tcx>,
    wf: &'check declaration_wf::CheckedWf<'policy, 'tcx>,
    fields: &'check declaration_fields::CheckedFields<'facts, 'policy, 'tcx>,
    modes: &'check declaration_modes::DeclarationModes<'tcx>,
    cohort: &'check Cohort<'check, 'tcx>,
    inputs: &'check Inputs,
    metadata: &'check Metadata,
    originals: Vec<LocalDefId>,
    result: Result<PendingHelpers, Failure>,
}

impl CheckedHelpers<'_, '_, '_, '_> {
    fn current(&self) -> bool {
        self.modes.belongs_to(self.tcx)
            && self.policy.for_owner(self.tcx, self.owner).is_some()
            && self.wf.for_owner(self.tcx, self.owner).is_some()
            && self.fields.for_owner(self.tcx, self.owner).is_some()
            && self
                .originals
                .iter()
                .all(|owner| inventory::original(self.tcx, *owner))
            && self
                .cohort
                .current(self.tcx, self.inputs, self.metadata)
                .is_ok()
    }

    pub(super) fn observation(&self) -> Value {
        if !self.current() {
            return Failure::Unknown(
                "the native helper prerequisites are no longer current".into(),
            )
            .observation();
        }
        match &self.result {
            Ok(fact) => fact.observation(),
            Err(failure) => failure.observation(),
        }
    }

    pub(super) fn into_pending(self) -> Result<PendingHelpers, Failure> {
        if !self.current() {
            return Err(Failure::Unknown(
                "the native helper prerequisites changed".into(),
            ));
        }
        self.result
    }
}

pub(super) struct Required<'check, 'facts, 'policy, 'tcx> {
    pub(super) policy: &'check declaration_policy::CheckedPolicy<'tcx>,
    pub(super) wf: &'check declaration_wf::CheckedWf<'policy, 'tcx>,
    pub(super) fields: &'check declaration_fields::CheckedFields<'facts, 'policy, 'tcx>,
    pub(super) cohort: &'check Cohort<'check, 'tcx>,
    pub(super) modes: &'check declaration_modes::DeclarationModes<'tcx>,
    pub(super) inputs: &'check Inputs,
    pub(super) metadata: &'check Metadata,
}

pub(super) fn check<'check, 'facts, 'policy, 'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: DefId,
    required: Required<'check, 'facts, 'policy, 'tcx>,
    work: &mut Work,
) -> CheckedHelpers<'check, 'facts, 'policy, 'tcx> {
    let Required {
        policy,
        wf,
        fields,
        cohort,
        modes,
        inputs,
        metadata,
    } = required;
    let mut originals = Vec::new();
    let result = (|| {
        if !modes.belongs_to(tcx) {
            return Err(Failure::Unknown(
                "the nominal helper modes belong to another compiler context".into(),
            ));
        }
        cohort.current(tcx, inputs, metadata)?;
        let policy = policy
            .for_owner(tcx, owner)
            .filter(|policy| policy.nominal().is_some())
            .ok_or_else(|| Failure::Unknown("no same-context nominal policy".into()))?;
        let wf_fact = wf
            .for_owner(tcx, owner)
            .ok_or_else(|| Failure::Unknown("no same-context nominal WF fact".into()))?;
        let fields = fields
            .for_owner(tcx, owner)
            .ok_or_else(|| Failure::Unknown("no same-context nominal field fact".into()))?;
        let owners = wf
            .local_owners(tcx, owner)
            .ok_or_else(|| Failure::Unknown("no original nominal owner closure".into()))?;
        work.charge(tcx, owners.len())?;
        if owners.is_empty()
            || owners.len() > 256
            || !owners.contains(&owner)
            || policy.owner() != wf_fact.owner()
            || fields.owner() != wf_fact.owner()
            || fields.local_declarations() != wf_fact.local_declarations()
        {
            return Err(Failure::Unknown(
                "nominal helper prerequisites have different inventories".into(),
            ));
        }
        let allowed = owners.iter().copied().collect::<HashSet<_>>();
        if allowed.len() != owners.len() {
            return Err(Failure::Unknown(
                "the original nominal inventory repeats an owner".into(),
            ));
        }
        let inventory = inventory::capture(tcx, owners, cohort, inputs, work)?;
        originals = inventory.originals;
        let mut helpers = Vec::new();
        for helper in inventory.helpers {
            let inline = inline::capture(tcx, helper.owner, work)?;
            let context =
                context::Context::new(modes, &allowed, cohort.intrinsic(), helper.owner, &inline);
            match modes::check_with_context(&context, helper.owner) {
                ModeCheck::Clean(checked)
                    if checked.signature.def_id == helper.owner.to_def_id()
                        && checked.signature.body_owner == helper.owner => {}
                ModeCheck::Error(error) => return Err(Failure::Modes(error)),
                ModeCheck::Unknown(refusal) => return Err(Failure::Unknown(refusal.detail)),
                _ => {
                    return Err(Failure::Unknown(
                        "the helper mode receipt changed owner".into(),
                    ))
                }
            }
            diagnostics(tcx)?;
            helpers.push(declaration_native::key(tcx, helper.owner.to_def_id()));
        }
        Ok(PendingHelpers {
            owner: policy.owner(),
            local_declarations: wf_fact.local_declarations().to_vec(),
            helpers,
            cohort: cohort.owned(),
        })
    })();
    CheckedHelpers {
        tcx,
        owner,
        policy,
        wf,
        fields,
        modes,
        cohort,
        inputs,
        metadata,
        originals,
        result,
    }
}
