// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Complete original native impl/member inventory and enum-field coverage.

use std::collections::HashSet;

use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::{self as hir, OwnerNode};
use rustc_middle::ty::{self, TyCtxt};

use super::*;

pub(super) struct Inventory {
    pub(super) originals: Vec<LocalDefId>,
    pub(super) helpers: Vec<helper::Helper>,
}

pub(super) fn original(tcx: TyCtxt<'_>, owner: LocalDefId) -> bool {
    let Some(raw) = tcx.lower_to_hir(owner).as_owner() else {
        return false;
    };
    let same = match (raw.node(), tcx.hir_node_by_def_id(owner)) {
        (OwnerNode::Item(a), hir::Node::Item(b)) => std::ptr::eq(a, b),
        (OwnerNode::ImplItem(a), hir::Node::ImplItem(b)) => std::ptr::eq(a, b),
        _ => false,
    };
    let root = tcx.local_def_id_to_hir_id(owner);
    same && std::ptr::eq(raw.attrs.get(root.local_id), tcx.hir_attrs(root))
        && (!matches!(tcx.def_kind(owner), DefKind::Fn | DefKind::AssocFn)
            || declaration_modes::original_body_available(tcx, owner))
}

/// Native slot identity is a component fact, never a helper permission token.
pub(super) fn field_slots(
    tcx: TyCtxt<'_>,
    owner: DefId,
    work: &mut Work,
) -> Result<HashSet<helper::Slot>, Failure> {
    if owner.as_local().is_none_or(|local| !original(tcx, local))
        || !matches!(tcx.def_kind(owner), DefKind::Struct | DefKind::Enum)
    {
        return Err(Failure::Unknown(
            "helper slots require an original local nominal".into(),
        ));
    }
    let adt = tcx.adt_def(owner);
    work.charge(tcx, adt.variants().len())?;
    if adt.variants().len() > 1024 {
        return Err(Failure::Unknown(
            "helper nominal variant count exceeds its bound".into(),
        ));
    }
    let mut slots = HashSet::new();
    if adt.is_enum() {
        for (variant, definition) in adt.variants().iter().enumerate() {
            work.charge(tcx, definition.fields.len())?;
            for field in 0..definition.fields.len() {
                if slots.len() >= 4096 {
                    return Err(Failure::Unknown(
                        "helper field closure exceeds its bound".into(),
                    ));
                }
                slots.insert(helper::Slot {
                    nominal: declaration_native::key(tcx, owner),
                    variant: variant as u32,
                    field: field as u32,
                });
            }
        }
    }
    Ok(slots)
}

pub(super) fn complete(
    expected: &HashSet<helper::Slot>,
    covered: &HashSet<helper::Slot>,
) -> Result<(), Failure> {
    if expected != covered {
        return Err(Failure::Unknown(
            "the original helper inventory does not cover every enum field".into(),
        ));
    }
    Ok(())
}

struct Capture<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    cohort: &'a Cohort<'a, 'tcx>,
    inputs: &'a Inputs,
    work: &'a mut Work,
    originals: Vec<LocalDefId>,
    seen: HashSet<LocalDefId>,
    expected: HashSet<helper::Slot>,
    covered: HashSet<helper::Slot>,
    helpers: Vec<helper::Helper>,
}

impl<'tcx> Capture<'_, 'tcx> {
    fn retain(&mut self, owner: DefId) -> Result<LocalDefId, Failure> {
        self.work.charge(self.tcx, 1)?;
        let local = owner
            .as_local()
            .ok_or_else(|| Failure::Unknown("helper inventory contains a foreign owner".into()))?;
        if !self.seen.insert(local) || !original(self.tcx, local) {
            return Err(Failure::Unknown(
                "helper inventory repeats or projects an original owner".into(),
            ));
        }
        self.originals.push(local);
        Ok(local)
    }

    fn nominal(&mut self, owner: DefId) -> Result<(), Failure> {
        self.retain(owner)?;
        if !matches!(self.tcx.def_kind(owner), DefKind::Struct | DefKind::Enum) {
            return Err(Failure::Unknown(
                "helper coverage needs an original struct or enum".into(),
            ));
        }
        let slots = field_slots(self.tcx, owner, self.work)?;
        self.work.charge(self.tcx, slots.len())?;
        if self.expected.len().saturating_add(slots.len()) > 4096 {
            return Err(Failure::Unknown(
                "helper field closure exceeds its bound".into(),
            ));
        }
        self.expected.extend(slots);
        let source = origin::nominal(self.tcx, owner, self.cohort, self.inputs, self.work)?;
        let implementations = self.tcx.inherent_impls(owner);
        self.work.charge(self.tcx, implementations.len())?;
        if implementations.len() > 4096 {
            return Err(Failure::Unknown(
                "inherent helper impl inventory exceeds its bound".into(),
            ));
        }
        for implementation in implementations {
            self.implementation(owner, *implementation, &source)?;
        }
        Ok(())
    }

    fn implementation(
        &mut self,
        nominal: DefId,
        implementation: DefId,
        source: &origin::Nominal<'_, 'tcx>,
    ) -> Result<(), Failure> {
        let local = self.retain(implementation)?;
        let raw = self
            .tcx
            .lower_to_hir(local)
            .as_owner()
            .ok_or_else(|| Failure::Unknown("the inherent impl has no original HIR".into()))?;
        let OwnerNode::Item(item) = raw.node() else {
            return Err(Failure::Unknown(
                "the original inherent impl is not an item".into(),
            ));
        };
        let hir::ItemKind::Impl(implementation_hir) = &item.kind else {
            return Err(Failure::Unknown(
                "the native inherent owner is not an impl".into(),
            ));
        };
        if implementation_hir.of_trait.is_some()
            || !matches!(
                self.tcx.def_kind(implementation),
                DefKind::Impl { of_trait: false }
            )
        {
            return Err(Failure::Unknown(
                "the helper owner is not an inherent implementation".into(),
            ));
        }
        let native = self.tcx.generics_of(implementation);
        self.work.charge(self.tcx, native.own_params.len())?;
        if native.own_params.len() > 256 {
            return Err(Failure::Unknown(
                "the inherent impl binder exceeds its native bound".into(),
            ));
        }
        let self_type = self
            .tcx
            .try_normalize_erasing_regions(
                ty::TypingEnv::non_body_analysis(self.tcx, implementation),
                self.tcx.type_of(implementation).instantiate_identity(),
            )
            .map_err(|_| {
                Failure::Unknown("the actual inherent Self type cannot be normalized".into())
            })?;
        if !matches!(self_type.kind(), ty::Adt(adt, _) if adt.did() == nominal) {
            return Err(Failure::Unknown(
                "an inherent impl belongs to another native nominal".into(),
            ));
        }
        let association = origin::implementation(
            self.tcx,
            implementation,
            item,
            source,
            self.cohort,
            self.inputs,
            self.work,
        )?;
        let members = self.members(implementation, implementation_hir.items)?;
        let synthetic = matches!(&association, origin::Association::Synthesis { .. });
        if synthetic {
            types::implementation(self.tcx, nominal, implementation, self.work)?;
        }
        for member in members {
            origin::member(
                self.tcx,
                member.to_def_id(),
                &association,
                self.cohort,
                self.inputs,
                self.work,
            )?;
            if synthetic {
                if self.tcx.def_kind(member) != DefKind::AssocFn {
                    return Err(Failure::Unknown(
                        "a synthetic impl contains an unsupported member".into(),
                    ));
                }
                types::member(
                    self.tcx,
                    nominal,
                    implementation,
                    member.to_def_id(),
                    self.work,
                )?;
                let helper = helper::capture(self.tcx, nominal, member, self.cohort, self.work)?;
                if !self.expected.contains(&helper.slot) {
                    return Err(Failure::Unknown(
                        "a helper does not cover an actual enum field".into(),
                    ));
                }
                self.covered.insert(helper.slot);
                self.helpers.push(helper);
            }
        }
        diagnostics(self.tcx)?;
        Ok(())
    }

    fn members(
        &mut self,
        implementation: DefId,
        raw: &[hir::ImplItemId],
    ) -> Result<Vec<LocalDefId>, Failure> {
        self.work.charge(self.tcx, raw.len())?;
        if raw.len() > 4096 {
            return Err(Failure::Unknown(
                "the original associated inventory exceeds its bound".into(),
            ));
        }
        let expected = raw
            .iter()
            .map(|item| item.owner_id.def_id)
            .collect::<HashSet<_>>();
        if expected.len() != raw.len() {
            return Err(Failure::Unknown(
                "original associated owners are duplicated".into(),
            ));
        }
        let mut actual = HashSet::new();
        let mut members = Vec::new();
        for item in self
            .tcx
            .associated_items(implementation)
            .in_definition_order()
        {
            self.work.charge(self.tcx, 1)?;
            if members.len() >= 4096 || self.tcx.impl_of_assoc(item.def_id) != Some(implementation)
            {
                return Err(Failure::Unknown(
                    "the native associated inventory has another container".into(),
                ));
            }
            let local = self.retain(item.def_id)?;
            if !actual.insert(local) {
                return Err(Failure::Unknown(
                    "the native associated inventory repeats an owner".into(),
                ));
            }
            members.push(local);
        }
        if actual != expected {
            return Err(Failure::Unknown(
                "the original and current associated inventories differ".into(),
            ));
        }
        Ok(members)
    }
}

pub(super) fn capture<'tcx>(
    tcx: TyCtxt<'tcx>,
    owners: &[DefId],
    cohort: &Cohort<'_, 'tcx>,
    inputs: &Inputs,
    work: &mut Work,
) -> Result<Inventory, Failure> {
    let mut capture = Capture {
        tcx,
        cohort,
        inputs,
        work,
        originals: Vec::new(),
        seen: HashSet::new(),
        expected: HashSet::new(),
        covered: HashSet::new(),
        helpers: Vec::new(),
    };
    for owner in owners {
        capture.nominal(*owner)?;
    }
    capture
        .work
        .charge(tcx, capture.expected.len() + capture.covered.len())?;
    complete(&capture.expected, &capture.covered)?;
    Ok(Inventory {
        originals: capture.originals,
        helpers: capture.helpers,
    })
}
