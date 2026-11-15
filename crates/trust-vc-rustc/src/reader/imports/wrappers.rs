//! Find local datatype closures that depend on a sealed imported carrier.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{HashMap, HashSet, VecDeque};

use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty;

use super::super::{declaration_wf, Cx};

pub(in crate::reader) struct Checks<'context, 'tcx> {
    cx: &'context Cx<'tcx>,
    affected: HashSet<LocalDefId>,
    entries: Vec<(
        LocalDefId,
        Result<declaration_wf::ClientWf<'context, 'tcx>, declaration_wf::ClientError>,
    )>,
}

impl<'context, 'tcx> Checks<'context, 'tcx> {
    pub(in crate::reader) fn belongs_to(&self, cx: &Cx<'tcx>) -> bool {
        std::ptr::eq(self.cx, cx)
    }
    pub(in crate::reader) fn capture(
        cx: &'context Cx<'tcx>,
        owners: &[LocalDefId],
        pending_policy: &HashSet<LocalDefId>,
    ) -> Self {
        let affected = match affected(cx, owners, pending_policy) {
            Ok(affected) => affected,
            Err(reason) => {
                return Self {
                    cx,
                    affected: owners.iter().copied().collect(),
                    entries: owners
                        .iter()
                        .map(|owner| {
                            (
                                *owner,
                                Err(declaration_wf::ClientError::Unknown(reason.clone())),
                            )
                        })
                        .collect(),
                }
            }
        };
        let mut entries: Vec<(
            LocalDefId,
            Result<declaration_wf::ClientWf<'context, 'tcx>, declaration_wf::ClientError>,
        )> = Vec::new();
        for owner in owners.iter().filter(|owner| affected.contains(owner)) {
            if entries.iter().any(|(root, checked)| {
                checked.as_ref().is_ok_and(|fact| {
                    fact.local_owners(cx, root.to_def_id())
                        .is_some_and(|covered| covered.contains(&owner.to_def_id()))
                })
            }) {
                continue;
            }
            entries.push((*owner, declaration_wf::check_client(cx, owner.to_def_id())));
        }
        Self {
            cx,
            affected,
            entries,
        }
    }

    pub(in crate::reader) fn affected(&self, owner: LocalDefId) -> bool {
        self.affected.contains(&owner)
    }

    pub(in crate::reader) fn unknown(&self, owner: LocalDefId) -> Option<String> {
        if self.affected(owner) && !declaration_wf::original(self.cx.tcx, owner.to_def_id()) {
            return Some("the wrapper lost its original local declaration".into());
        }
        self.entries
            .iter()
            .find_map(|(root, checked)| match checked {
                Err(declaration_wf::ClientError::Unknown(reason)) if *root == owner => {
                    Some(reason.clone())
                }
                Ok(fact)
                    if *root == owner && fact.local_owners(self.cx, root.to_def_id()).is_none() =>
                {
                    Some("the wrapper lost its current whole-closure fact".into())
                }
                _ => None,
            })
    }

    /// This is only permission to consume native recursion directives while
    /// lowering. A successful whole-closure fact is required for admission;
    /// a typed semantic failure instead rejects the crate before verification.
    pub(in crate::reader) fn checked_policy(&self, owner: LocalDefId) -> bool {
        self.entries.iter().any(|(root, checked)| match checked {
            Ok(fact) => fact
                .local_owners(self.cx, root.to_def_id())
                .is_some_and(|owners| owners.contains(&owner.to_def_id())),
            Err(declaration_wf::ClientError::Unknown(_)) => false,
            Err(_) => *root == owner,
        })
    }

    pub(in crate::reader) fn diagnostics(
        &self,
    ) -> Result<
        (
            Vec<(LocalDefId, super::super::UserError)>,
            HashSet<LocalDefId>,
        ),
        String,
    > {
        use super::super::{Phase, UserError};
        use declaration_wf::ClientError;
        if self.cx.tcx.dcx().has_errors().is_some() {
            return Err("native diagnostics invalidate wrapper language judgments".into());
        }
        let mut errors = Vec::new();
        let mut no_base = HashSet::new();
        let mut reported = HashSet::new();
        for (root, checked) in &self.entries {
            if !declaration_wf::original(self.cx.tcx, root.to_def_id()) {
                return Err("wrapper diagnostics lost their original local declaration".into());
            }
            let (owner, message) = match checked {
                Err(ClientError::NonPositiveDatatype { owner, target }) => (
                    *owner,
                    format!(
                        "Type {} recursively uses type {} in a non-positive position",
                        self.cx.friendly_path(*owner),
                        self.cx.friendly_path(*target)
                    ),
                ),
                Err(ClientError::NonPositiveParameter { owner, parameter }) => {
                    let parameter = self
                        .cx
                        .tcx
                        .generics_of(*owner)
                        .own_params
                        .iter()
                        .find(|candidate| candidate.index == *parameter)
                        .ok_or("the typed non-positive parameter lost its actual native binder")?;
                    (*owner, format!("Type parameter {} of {} must be declared #[verifier::reject_recursive_types] to be used in a non-positive position",
                        parameter.name, self.cx.friendly_path(*owner)))
                }
                Err(ClientError::NoBase { owners }) => {
                    no_base.extend(
                        owners
                            .iter()
                            .map(|owner| owner.as_local())
                            .collect::<Option<Vec<_>>>()
                            .ok_or("the typed base-case failure has a nonlocal owner")?,
                    );
                    continue;
                }
                _ => continue,
            };
            let owner = owner
                .as_local()
                .ok_or("the typed positivity failure has a nonlocal owner")?;
            if reported.insert((owner, message.clone())) {
                errors.push((
                    owner,
                    UserError::new(
                        Phase::WellFormed,
                        self.cx
                            .tcx
                            .hir_span_with_body(self.cx.tcx.local_def_id_to_hir_id(owner)),
                        message,
                    ),
                ));
            }
        }
        Ok((errors, no_base))
    }
}

const MAX_WORK: usize = 262_144;
const MAX_LOCAL_DECLARATIONS: usize = 4_096;

fn charge(work: &mut usize) -> Result<(), String> {
    *work = work
        .checked_sub(1)
        .ok_or("imported wrapper discovery exceeds its work bound")?;
    Ok(())
}

/// Follow original local field types only. In particular A { b: B<A> }
/// is affected when B<T> { set: Set<T> } uses an import, even though A's
/// own syntactic type arguments do not contain that imported declaration.
pub(in crate::reader) fn affected(
    cx: &Cx<'_>,
    owners: &[LocalDefId],
    pending_policy: &HashSet<LocalDefId>,
) -> Result<HashSet<LocalDefId>, String> {
    if cx.imports.is_none() && pending_policy.is_empty() {
        return Ok(HashSet::new());
    }
    if owners.len() > MAX_LOCAL_DECLARATIONS {
        return Err("imported wrapper discovery exceeds its local declaration bound".into());
    }
    let mut work = MAX_WORK;
    let index = owners
        .iter()
        .enumerate()
        .map(|(index, owner)| (owner.to_def_id(), index))
        .collect::<HashMap<_, _>>();
    if index.len() != owners.len() {
        return Err("the local datatype inventory is duplicated".into());
    }
    let mut predecessors = vec![Vec::new(); owners.len()];
    let mut imported = vec![false; owners.len()];
    for (owner_index, owner) in owners.iter().copied().enumerate() {
        imported[owner_index] = pending_policy.contains(&owner);
        if !declaration_wf::original(cx.tcx, owner.to_def_id()) {
            return Err("wrapper discovery requires original local datatype declarations".into());
        }
        let adt = cx.tcx.adt_def(owner);
        for field in adt.all_fields() {
            charge(&mut work)?;
            let field_type = cx
                .tcx
                .type_of(field.did)
                .instantiate_identity()
                .skip_normalization();
            for argument in field_type.walk() {
                charge(&mut work)?;
                let Some(value) = argument.as_type() else {
                    continue;
                };
                if let ty::Adt(adt, _) = value.kind() {
                    if cx.imported_nominal_policy(adt.did()).is_some() {
                        imported[owner_index] = true;
                    } else if let Some(target) = index.get(&adt.did()) {
                        predecessors[*target].push(owner_index);
                    }
                }
            }
        }
    }
    let mut pending = imported
        .iter()
        .enumerate()
        .filter_map(|(index, imported)| imported.then_some(index))
        .collect::<VecDeque<_>>();
    while let Some(target) = pending.pop_front() {
        for predecessor in &predecessors[target] {
            charge(&mut work)?;
            if !imported[*predecessor] {
                imported[*predecessor] = true;
                pending.push_back(*predecessor);
            }
        }
    }
    Ok(owners
        .iter()
        .zip(imported)
        .filter_map(|(owner, imported)| imported.then_some(*owner))
        .collect())
}
