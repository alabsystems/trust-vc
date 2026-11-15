// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! One exact original inline occurrence, consumed only for helper mode checking.

use rustc_attr_ir::{AttrArgs, Attribute};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::TyCtxt;
use rustc_span::AttrId;

use super::*;
use crate::reader::attrs::{self, ItemAttrs};

pub(super) struct Checked<'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    original: &'tcx [Attribute],
    index: usize,
    id: AttrId,
}

impl<'tcx> Checked<'tcx> {
    fn current(&self, tcx: TyCtxt<'tcx>, owner: LocalDefId) -> bool {
        std::ptr::eq(*self.tcx, *tcx)
            && owner == self.owner
            && tcx.dcx().has_errors().is_none()
            && inventory::original(tcx, owner)
            && std::ptr::eq(
                self.original,
                tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner)),
            )
    }

    pub(super) fn permits(
        &self,
        tcx: TyCtxt<'tcx>,
        owner: LocalDefId,
        attribute: &Attribute,
    ) -> bool {
        self.current(tcx, owner)
            && self.original.get(self.index).is_some_and(|actual| {
                std::ptr::eq(actual, attribute)
                    && matches!(attribute, Attribute::Unparsed(item) if item.id.attr_id == self.id)
            })
    }

    pub(super) fn mode_attrs(&self, tcx: TyCtxt<'tcx>, owner: LocalDefId) -> Option<ItemAttrs> {
        if !self.current(tcx, owner) {
            return None;
        }
        let remaining = self
            .original
            .iter()
            .enumerate()
            .filter(|(index, attribute)| {
                *index != self.index || !self.permits(tcx, owner, attribute)
            })
            .map(|(_, attribute)| attribute.clone())
            .collect::<Vec<_>>();
        Some(attrs::item_attrs(&remaining))
    }
}

pub(super) fn capture<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    work: &mut Work,
) -> Result<Checked<'tcx>, Failure> {
    if tcx.def_kind(owner) != DefKind::AssocFn || !inventory::original(tcx, owner) {
        return Err(Failure::Unknown(
            "inline helper attributes need an original associated function".into(),
        ));
    }
    let original = tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner));
    work.charge(tcx, original.len())?;
    attrs::verus_parse(original).map_err(|problem| {
        Failure::Unknown(format!(
            "the original helper attribute language is unavailable: {problem:?}"
        ))
    })?;
    let mut occurrence = None;
    for (index, attribute) in original.iter().enumerate() {
        let Attribute::Unparsed(item) = attribute else {
            continue;
        };
        if item
            .path
            .segments
            .iter()
            .map(|name| name.as_str())
            .eq(["verifier", "inline"])
        {
            if !matches!(item.args, AttrArgs::Empty) || occurrence.is_some() {
                return Err(Failure::Unknown(
                    "the getter inline occurrence is not its unique canonical attribute".into(),
                ));
            }
            occurrence = Some((index, item.id.attr_id));
        }
    }
    let (index, id) = occurrence.ok_or_else(|| {
        Failure::Unknown("the original getter has no canonical inline attribute".into())
    })?;
    let checked = Checked {
        tcx,
        owner,
        original,
        index,
        id,
    };
    let attributes = checked.mode_attrs(tcx, owner).ok_or_else(|| {
        Failure::Unknown("the helper inline occurrence is no longer current".into())
    })?;
    if !attributes.verus_macro
        || attributes.mode != Some(trust_vc_vcir::Mode::Spec)
        || attributes.external
        || attributes.external_body
        || attributes.reveal_fn
        || !attributes.unsupported.is_empty()
    {
        return Err(Failure::Unknown(
            "the native getter attributes are not a supported Spec body".into(),
        ));
    }
    Ok(checked)
}
