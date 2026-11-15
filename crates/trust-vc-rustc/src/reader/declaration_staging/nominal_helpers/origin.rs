// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Typed native invocation and original-byte association under the pinned recipe.
//!
//! A range relation alone grants nothing. The inventory separately requires
//! actual Self/binders, complete native membership and the closed helper schema.

use std::collections::HashSet;

use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::DefId;
use rustc_hir::{self as hir};
use rustc_middle::ty::TyCtxt;
use rustc_span::hygiene::ExpnKind;
use rustc_span::{ExpnId, FileName, Pos, Span};

use super::*;
use crate::declaration_alignment::source_bindings::Sources;
use crate::declaration_alignment::{observation::ObservedAnchor, AuthoredSpan};

mod enum_extent;
mod refusal_context;

pub(super) struct Event {
    id: ExpnId,
    call_site: AuthoredSpan,
}

pub(super) struct Nominal<'sources, 'tcx> {
    definition: DefId,
    envelope: AuthoredSpan,
    identifier: AuthoredSpan,
    events: Vec<Event>,
    enum_source: Option<enum_extent::CheckedEnumExtent<'sources, 'tcx>>,
}

pub(super) enum Association {
    Authored {
        envelope: AuthoredSpan,
    },
    Synthesis {
        envelope: AuthoredSpan,
        event: Event,
    },
}

fn same_file(a: &AuthoredSpan, b: &AuthoredSpan) -> bool {
    a.relative_file == b.relative_file
        && a.file_sha256 == b.file_sha256
        && a.original_file_len == b.original_file_len
}

pub(super) fn contains(outer: &AuthoredSpan, inner: &AuthoredSpan) -> bool {
    same_file(outer, inner) && outer.bytes.0 <= inner.bytes.0 && inner.bytes.1 <= outer.bytes.1
}

fn disjoint(a: &AuthoredSpan, b: &AuthoredSpan) -> bool {
    // Attribution callers bind both anchors to the same approved source graph.
    // Distinct files have separate coordinate spaces; inconsistent metadata
    // for one relative file never establishes disjointness.
    if a.relative_file != b.relative_file {
        return true;
    }
    same_file(a, b) && (a.bytes.1 <= b.bytes.0 || b.bytes.1 <= a.bytes.0)
}

/// A source-association component, never a synthesis or import certificate.
pub(super) fn authored(
    envelope: &AuthoredSpan,
    nominal: &AuthoredSpan,
    identifier: &AuthoredSpan,
) -> bool {
    disjoint(envelope, nominal) && contains(envelope, identifier)
}

pub(super) fn anchor(
    tcx: TyCtxt<'_>,
    span: Span,
    inputs: &Inputs,
) -> Result<AuthoredSpan, Failure> {
    anchor_sources(tcx, span, &inputs.sources)
}

fn anchor_sources(tcx: TyCtxt<'_>, span: Span, sources: &Sources) -> Result<AuthoredSpan, Failure> {
    if span.is_dummy() {
        return Err(Failure::Unknown("helper source span is dummy".into()));
    }
    let file = tcx.sess.source_map().lookup_source_file(span.lo());
    if !file.contains(span.hi()) {
        return Err(Failure::Unknown("helper source span crosses files".into()));
    }
    let FileName::Real(name) = &file.name else {
        return Err(Failure::Unknown("helper source file is not real".into()));
    };
    let path = name
        .local_path()
        .and_then(|path| path.to_str())
        .ok_or_else(|| Failure::Unknown("helper source has no represented local path".into()))?;
    Ok(sources.anchor(&ObservedAnchor {
        local_path: path.into(),
        compiler_source_hash: file.src_hash.to_string(),
        original_file_len: file.unnormalized_source_len,
        bytes: (
            file.original_relative_byte_pos(span.lo()).to_u32(),
            file.original_relative_byte_pos(span.hi()).to_u32(),
        ),
    })?)
}

fn events(
    tcx: TyCtxt<'_>,
    owner: DefId,
    cohort: &Cohort<'_, '_>,
    inputs: &Inputs,
    work: &mut Work,
) -> Result<Vec<Event>, Failure> {
    let mut pending = vec![tcx.expn_that_defined(owner)];
    let mut seen = HashSet::new();
    let mut result = Vec::new();
    while let Some(id) = pending.pop() {
        if id == ExpnId::root() || !seen.insert(id) {
            continue;
        }
        work.charge(tcx, 3)?;
        if seen.len() > 128 {
            return Err(Failure::Unknown(
                "helper expansion graph exceeds its bound".into(),
            ));
        }
        let data = id.expn_data();
        if matches!(data.kind, ExpnKind::Macro(..))
            && data
                .macro_def_id
                .is_some_and(|definition| cohort.owns_macro(definition))
        {
            result.push(Event {
                id,
                call_site: anchor(tcx, data.call_site, inputs)?,
            });
        }
        // Inert attributes and outer user macros do not acquire permission,
        // nor do they impose a requirement that every wrapper have a DefId.
        pending.extend([data.parent, data.call_site.ctxt().outer_expn()]);
    }
    Ok(result)
}

pub(super) fn nominal<'sources, 'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: DefId,
    cohort: &Cohort<'_, '_>,
    inputs: &'sources Inputs,
    work: &mut Work,
) -> Result<Nominal<'sources, 'tcx>, Failure> {
    let envelope = anchor(tcx, tcx.def_span(owner), inputs)?;
    let identifier = anchor(
        tcx,
        tcx.def_ident_span(owner)
            .ok_or_else(|| Failure::Unknown("the nominal has no actual identifier span".into()))?,
        inputs,
    )?;
    if !contains(&envelope, &identifier) {
        return Err(Failure::Unknown(
            "the nominal identifier is outside its original envelope".into(),
        ));
    }
    // Establish original source extent before querying any inherent impl.
    // The declaration header remains a distinct identity component.
    let enum_source = if tcx.def_kind(owner) == DefKind::Enum {
        Some(enum_extent::capture(
            tcx,
            owner,
            inputs,
            &envelope,
            &identifier,
            work,
        )?)
    } else {
        None
    };
    let events = if tcx.def_kind(owner) == DefKind::Enum {
        events(tcx, owner, cohort, inputs, work)?
    } else {
        Vec::new()
    };
    if tcx.def_kind(owner) == DefKind::Enum && events.is_empty() {
        return Err(Failure::Unknown(
            "no genuine source-bound macro invocation defines this enum".into(),
        ));
    }
    Ok(Nominal {
        definition: owner,
        envelope,
        identifier,
        events,
        enum_source,
    })
}

pub(super) fn implementation<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: DefId,
    original: &hir::Item<'tcx>,
    nominal: &Nominal<'_, 'tcx>,
    cohort: &Cohort<'_, 'tcx>,
    inputs: &Inputs,
    work: &mut Work,
) -> Result<Association, Failure> {
    if original.owner_id.def_id.to_def_id() != owner {
        return Err(Failure::Unknown(
            "the original impl item belongs to another native owner".into(),
        ));
    }
    let hir::ItemKind::Impl(implementation) = &original.kind else {
        return Err(Failure::Unknown(
            "the original implementation is not an impl item".into(),
        ));
    };
    let hir::TyKind::Path(hir::QPath::Resolved(None, path)) = &implementation.self_ty.kind else {
        return Err(Failure::Unknown(
            "the original impl Self path is not represented".into(),
        ));
    };
    work.charge(tcx, path.segments.len() + 2)?;
    let terminal = path.segments.last().ok_or_else(|| {
        Failure::Unknown("the original Self path has no terminal identifier".into())
    })?;
    let identifier = anchor(tcx, terminal.ident.span, inputs)?;
    let declaration = anchor(tcx, tcx.def_span(owner), inputs)?;
    // The native definition span describes the impl header. Only the retained
    // original item span includes the members whose source is checked below.
    let envelope = anchor(tcx, original.span, inputs)?;
    if !contains(&envelope, &declaration) {
        return Err(Failure::Unknown(
            "the impl declaration is outside its original item source".into(),
        ));
    }
    if authored(&declaration, &nominal.envelope, &identifier)
        && authored(&envelope, &nominal.envelope, &identifier)
    {
        return Ok(Association::Authored { envelope });
    }
    if !matches!(path.res, Res::Def(DefKind::Enum, actual) if actual == nominal.definition)
        || identifier != nominal.identifier
        || !nominal
            .enum_source
            .as_ref()
            .is_some_and(|extent| extent.matches(tcx, inputs, &declaration, &envelope))
    {
        return Err(Failure::UnknownWithContext {
            reason: "impl source cannot be attributed to authored code or enum synthesis".into(),
            context: refusal_context::capture(
                tcx,
                refusal_context::Site {
                    owner,
                    original,
                    self_type: implementation.self_ty,
                    resolution: path.res,
                    self_identifier: terminal.ident.span,
                    nominal,
                    identifier: &identifier,
                    declaration: &declaration,
                    envelope: &envelope,
                },
                cohort,
            ),
        });
    }
    let actual = events(tcx, owner, cohort, inputs, work)?;
    work.charge(
        tcx,
        nominal
            .events
            .len()
            .checked_mul(actual.len())
            .ok_or_else(|| {
                Failure::Unknown("helper event intersection exceeds its bound".into())
            })?,
    )?;
    let common = nominal
        .events
        .iter()
        .filter(|expected| {
            actual
                .iter()
                .any(|event| event.id == expected.id && event.call_site == expected.call_site)
        })
        .collect::<Vec<_>>();
    let [event] = common.as_slice() else {
        return Err(Failure::Unknown(
            "enum and synthetic impl have no unique genuine invocation".into(),
        ));
    };
    let extent = nominal
        .enum_source
        .as_ref()
        .ok_or_else(|| Failure::Unknown("the enum has no checked original source extent".into()))?;
    let envelope = extent
        .envelope(tcx, inputs)
        .ok_or_else(|| Failure::Unknown("the enum source extent is no longer current".into()))?
        .clone();
    Ok(Association::Synthesis {
        envelope,
        event: Event {
            id: event.id,
            call_site: event.call_site.clone(),
        },
    })
}

pub(super) fn member(
    tcx: TyCtxt<'_>,
    owner: DefId,
    association: &Association,
    cohort: &Cohort<'_, '_>,
    inputs: &Inputs,
    work: &mut Work,
) -> Result<(), Failure> {
    work.charge(tcx, 1)?;
    let span = anchor(tcx, tcx.def_span(owner), inputs)?;
    let (Association::Authored { envelope } | Association::Synthesis { envelope, .. }) =
        association;
    if !contains(envelope, &span) {
        return Err(Failure::Unknown(
            "an associated member is outside its original impl source".into(),
        ));
    }
    if let Association::Synthesis { event, .. } = association {
        if !events(tcx, owner, cohort, inputs, work)?
            .iter()
            .any(|actual| actual.id == event.id && actual.call_site == event.call_site)
        {
            return Err(Failure::Unknown(
                "a synthetic member has another native macro invocation".into(),
            ));
        }
    }
    Ok(())
}
