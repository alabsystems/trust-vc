// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Current original enum source, derived before inspecting any impl spans.
//!
//! Only complete source-prefix attributes contribute endpoints. Attached
//! overlapping spans have no such authority and must fit the result already
//! established by the original item and its own prefix syntax.

use rustc_ast::AttrStyle;
use rustc_attr_ir::{Attribute, AttributeKind};
use rustc_hir::{def_id::LocalDefId, OwnerNode};

use super::*;

mod lexical;
#[cfg(test)]
mod tests;

const ATTRIBUTES: usize = 32;
const PREFIX_BYTES: usize = 65_536;

pub(super) struct CheckedEnumExtent<'sources, 'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    item: &'tcx hir::Item<'tcx>,
    attributes: &'tcx [Attribute],
    sources: &'sources Sources,
    header: AuthoredSpan,
    extent: AuthoredSpan,
}

fn slot_matches(attributes: &[Attribute], slot: usize, actual: &Attribute) -> bool {
    attributes
        .get(slot)
        .is_some_and(|current| std::ptr::eq(current, actual))
}

impl<'tcx> CheckedEnumExtent<'_, 'tcx> {
    fn current(&self, tcx: TyCtxt<'tcx>, sources: &Sources) -> bool {
        if diagnostics(tcx).is_err()
            || !std::ptr::eq(*tcx, *self.tcx)
            || !std::ptr::eq(sources, self.sources)
        {
            return false;
        }
        let Some(raw) = tcx.lower_to_hir(self.owner).as_owner() else {
            return false;
        };
        let OwnerNode::Item(item) = raw.node() else {
            return false;
        };
        let root = tcx.local_def_id_to_hir_id(self.owner);
        std::ptr::eq(item, self.item)
            && matches!(tcx.hir_node_by_def_id(self.owner), hir::Node::Item(current)
                if std::ptr::eq(item, current))
            && root.owner.def_id == self.owner
            && root.local_id.as_u32() == 0
            && std::ptr::eq(raw.attrs.get(root.local_id), self.attributes)
            && std::ptr::eq(self.attributes, tcx.hir_attrs(root))
    }

    pub(super) fn matches(
        &self,
        tcx: TyCtxt<'tcx>,
        inputs: &Inputs,
        header: &AuthoredSpan,
        item: &AuthoredSpan,
    ) -> bool {
        self.current(tcx, &inputs.sources) && self.matches_anchors(header, item)
    }

    fn matches_anchors(&self, header: &AuthoredSpan, item: &AuthoredSpan) -> bool {
        same_file(&self.extent, header)
            && item == &self.extent
            && header.bytes == (self.extent.bytes.0, self.header.bytes.1)
    }

    pub(super) fn envelope(&self, tcx: TyCtxt<'tcx>, inputs: &Inputs) -> Option<&AuthoredSpan> {
        self.current(tcx, &inputs.sources).then_some(&self.extent)
    }
}

pub(super) fn capture<'sources, 'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: DefId,
    inputs: &'sources Inputs,
    header: &AuthoredSpan,
    identifier: &AuthoredSpan,
    work: &mut Work,
) -> Result<CheckedEnumExtent<'sources, 'tcx>, Failure> {
    capture_sources(tcx, owner, &inputs.sources, header, identifier, work)
}

fn capture_sources<'sources, 'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: DefId,
    sources: &'sources Sources,
    header: &AuthoredSpan,
    identifier: &AuthoredSpan,
    work: &mut Work,
) -> Result<CheckedEnumExtent<'sources, 'tcx>, Failure> {
    work.charge(tcx, 1)?;
    let local = owner.as_local().ok_or_else(|| {
        Failure::Unknown("an enum source extent needs an original local owner".into())
    })?;
    if tcx.def_kind(owner) != DefKind::Enum || !inventory::original(tcx, local) {
        return Err(Failure::Unknown(
            "the enum source owner is not current original HIR".into(),
        ));
    }
    let raw = tcx
        .lower_to_hir(local)
        .as_owner()
        .ok_or_else(|| Failure::Unknown("the enum source owner has no original HIR".into()))?;
    let OwnerNode::Item(item) = raw.node() else {
        return Err(Failure::Unknown(
            "the enum source owner is not an original item".into(),
        ));
    };
    if item.owner_id.def_id != local || !matches!(&item.kind, hir::ItemKind::Enum(..)) {
        return Err(Failure::Unknown(
            "the original item is not this native enum".into(),
        ));
    }
    let root = tcx.local_def_id_to_hir_id(local);
    let attributes = raw.attrs.get(root.local_id);
    let current = tcx.hir_attrs(root);
    if root.owner.def_id != local
        || root.local_id.as_u32() != 0
        || !std::ptr::eq(attributes, current)
        || attributes.len() > ATTRIBUTES
    {
        return Err(Failure::Unknown(
            "the enum root attribute inventory is unavailable or exceeds its bound".into(),
        ));
    }
    work.charge(tcx, attributes.len())?;
    let item_source = anchor_sources(tcx, item.span, sources)?;
    let actual_header = anchor_sources(tcx, tcx.def_span(owner), sources)?;
    let actual_identifier = anchor_sources(
        tcx,
        tcx.def_ident_span(owner).ok_or_else(|| {
            Failure::Unknown("the original enum identifier is unavailable".into())
        })?,
        sources,
    )?;
    if &actual_header != header
        || &actual_identifier != identifier
        || !contains(&item_source, header)
        || !contains(header, identifier)
    {
        return Err(Failure::Unknown(
            "the original enum header/item/identifier source differs".into(),
        ));
    }
    let mut prefix = Vec::new();
    let mut attached = Vec::new();
    for (slot, attribute) in attributes.iter().enumerate() {
        work.charge(tcx, 1)?;
        if !slot_matches(current, slot, attribute) {
            return Err(Failure::Unknown(
                "an enum attribute is not this original root slot".into(),
            ));
        }
        let (style, span, kind) = match attribute {
            Attribute::Tool(item) | Attribute::DeriveHelper(item) => {
                (item.style, item.span, lexical::Kind::Attribute)
            }
            Attribute::Parsed(AttributeKind::DocComment { style, span, .. }) => {
                (*style, *span, lexical::Kind::Document)
            }
            _ => {
                return Err(Failure::Unknown(
                    "an enum attribute has no represented complete source span".into(),
                ))
            }
        };
        if style != AttrStyle::Outer {
            return Err(Failure::Unknown(
                "an enum inner attribute has no source-prefix license".into(),
            ));
        }
        let span = anchor_sources(tcx, span, sources)?;
        if !same_file(&span, &item_source) {
            return Err(Failure::Unknown(
                "an enum attribute belongs to another source identity".into(),
            ));
        }
        if span.bytes.1 <= item_source.bytes.0 {
            prefix.push((span, kind));
        } else {
            // Interior/overlapping attached spans never choose an endpoint.
            attached.push(span);
        }
    }
    prefix.sort_by_key(|(span, _)| span.bytes);
    let mut extent = item_source.clone();
    if let Some((first, _)) = prefix.first() {
        let bytes = item_source
            .bytes
            .0
            .checked_sub(first.bytes.0)
            .ok_or_else(|| {
                Failure::Unknown("the enum source prefix has invalid coordinates".into())
            })? as usize;
        if bytes > PREFIX_BYTES {
            return Err(Failure::Unknown(
                "the enum source prefix exceeds its byte bound".into(),
            ));
        }
        // Pay before scanning this bounded prefix. Full-file source authentication
        // above is separate. Each original prefix byte can contribute
        // at most one token; delimiter work is bounded by the same scan.
        work.charge(
            tcx,
            bytes
                .checked_mul(2)
                .ok_or_else(|| Failure::Unknown("the enum source prefix work overflows".into()))?,
        )?;
        let mut source = item_source.clone();
        source.bytes = (first.bytes.0, item_source.bytes.0);
        let text = sources.text_for(&source, PREFIX_BYTES)?;
        let parts = prefix
            .iter()
            .map(|(span, kind)| lexical::Part {
                start: (span.bytes.0 - source.bytes.0) as usize,
                end: (span.bytes.1 - source.bytes.0) as usize,
                kind: *kind,
            })
            .collect::<Vec<_>>();
        lexical::partition(text, &parts).map_err(|reason| Failure::Unknown(reason.into()))?;
        extent.bytes.0 = first.bytes.0;
    }
    if attached.iter().any(|span| !contains(&extent, span)) {
        return Err(Failure::Unknown(
            "an attached enum span is outside its independently checked source extent".into(),
        ));
    }
    sources.validate_anchor(&extent)?;
    let checked = CheckedEnumExtent {
        tcx,
        owner: local,
        item,
        attributes,
        sources,
        header: header.clone(),
        extent,
    };
    if !checked.current(tcx, sources) {
        return Err(Failure::Unknown(
            "the original enum extent was revoked during capture".into(),
        ));
    }
    Ok(checked)
}
