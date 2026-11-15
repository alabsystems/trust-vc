// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Bounded observations at an already-decided source-attribution refusal.
//!
//! This recorder never receives the qualification work counter. Its output is
//! attached only to Unknown; missing observations cannot authorize a helper.

use std::io::{self, Write};

use rustc_hir::OwnerNode;
use rustc_span::hygiene::MacroKind;

use super::*;

mod attributes;

const WORK: usize = 4096;
const TEXT_BYTES: usize = 32_768;
const JSON_BYTES: usize = 65_536;
const EXPANSIONS: usize = 128;
const EVENTS: usize = 32;

pub(super) struct Site<'a, 'sources, 'hir> {
    pub(super) owner: DefId,
    pub(super) original: &'a hir::Item<'hir>,
    pub(super) self_type: &'a hir::Ty<'hir>,
    pub(super) resolution: Res,
    pub(super) self_identifier: Span,
    pub(super) nominal: &'a Nominal<'sources, 'hir>,
    pub(super) identifier: &'a AuthoredSpan,
    pub(super) declaration: &'a AuthoredSpan,
    pub(super) envelope: &'a AuthoredSpan,
}

struct Budget {
    work: usize,
    bytes: usize,
    refused: bool,
}

impl Budget {
    fn new() -> Self {
        Self {
            work: WORK,
            bytes: TEXT_BYTES,
            refused: false,
        }
    }

    fn charge(&mut self, work: usize, bytes: usize) -> Result<(), &'static str> {
        if self.refused {
            return Err("origin observation budget was already refused");
        }
        let (Some(work), Some(bytes)) =
            (self.work.checked_sub(work), self.bytes.checked_sub(bytes))
        else {
            self.refused = true;
            return Err("origin observation exceeded its separate work or byte bound");
        };
        self.work = work;
        self.bytes = bytes;
        Ok(())
    }
}

fn unknown(reason: &str) -> Value {
    json!({"state": "Unknown", "reason": reason})
}

fn key(tcx: TyCtxt<'_>, owner: DefId) -> Value {
    let key = declaration_native::key(tcx, owner);
    json!({"stable_crate_id": format!("{:016x}", key.stable_crate_id),
        "def_path_hash": format!("{:032x}", key.def_path_hash)})
}

fn kind(kind: DefKind) -> &'static str {
    match kind {
        DefKind::Struct => "Struct",
        DefKind::Enum => "Enum",
        DefKind::Impl { of_trait: false } => "InherentImplementation",
        DefKind::Impl { of_trait: true } => "TraitImplementation",
        _ => "Other",
    }
}

fn expansion(id: ExpnId) -> Value {
    json!({"crate_number": id.krate.as_u32(), "local_expansion_index": id.local_id.as_u32(),
        "identity_scope": "this compiler session only"})
}

fn bound_anchor(anchor: &AuthoredSpan, budget: &mut Budget) -> Result<Value, &'static str> {
    budget.charge(1, anchor.relative_file.len())?;
    Ok(
        json!({"state": "AlreadySourceBoundAnchor", "relative_file": anchor.relative_file,
        "file_sha256": anchor.file_sha256.iter().map(|byte| format!("{byte:02x}"))
            .collect::<String>(),
        "original_file_len": anchor.original_file_len,
        "original_lo": anchor.bytes.0, "original_hi": anchor.bytes.1}),
    )
}

// Native coordinates are observations, not another source-binding operation.
fn coordinates(tcx: TyCtxt<'_>, span: Span, budget: &mut Budget) -> Result<Value, &'static str> {
    budget.charge(1, 0)?;
    if span.is_dummy() {
        return Ok(unknown("the native span is dummy"));
    }
    let file = tcx.sess.source_map().lookup_source_file(span.lo());
    if !file.contains(span.hi()) {
        return Ok(unknown("the native span crosses source files"));
    }
    let FileName::Real(name) = &file.name else {
        return Ok(unknown("the native span has no real source file"));
    };
    let Some(path) = name.local_path().and_then(|path| path.to_str()) else {
        return Ok(unknown("the native span has no UTF-8 local source path"));
    };
    budget.charge(1, path.len())?;
    let lo = file.original_relative_byte_pos(span.lo()).to_u32();
    let hi = file.original_relative_byte_pos(span.hi()).to_u32();
    if lo > hi || hi > file.unnormalized_source_len {
        return Ok(unknown("the native span exceeds its original source file"));
    }
    let hash = file.src_hash.to_string();
    budget.charge(1, hash.len())?;
    Ok(
        json!({"state": "ObservedCompilerSourceCoordinates", "local_path": path,
        "compiler_source_hash": hash, "original_file_len": file.unnormalized_source_len,
        "original_lo": lo, "original_hi": hi,
        "normalized_lo": file.relative_position(span.lo()).to_u32(),
        "normalized_hi": file.relative_position(span.hi()).to_u32(),
        "outer_expansion": expansion(span.ctxt().outer_expn()),
        "source_binding_authority": false}),
    )
}

fn span(tcx: TyCtxt<'_>, span: Span, budget: &mut Budget) -> Result<Value, &'static str> {
    let native = coordinates(tcx, span, budget)?;
    let mut callsite = span;
    let mut seen = HashSet::new();
    while callsite.ctxt().outer_expn() != ExpnId::root() {
        budget.charge(1, 0)?;
        let id = callsite.ctxt().outer_expn();
        if seen.len() >= EXPANSIONS || !seen.insert(id) {
            return Err("origin observation callsite ancestry exceeds its bound or repeats");
        }
        callsite = id.expn_data().call_site;
    }
    Ok(json!({"native": native, "source_callsite": coordinates(tcx, callsite, budget)?}))
}

struct ObservedEvent {
    id: ExpnId,
    call_site: Span,
    row: Value,
}

// This traverses the same parent/callsite graph as attribution, but also for
// structs, whose attribution path deliberately does not collect enum events.
// The separate observation cannot populate or change Nominal::events.
fn event_inventory(
    tcx: TyCtxt<'_>,
    owner: DefId,
    cohort: &Cohort<'_, '_>,
    budget: &mut Budget,
) -> Result<Vec<ObservedEvent>, &'static str> {
    budget.charge(1, 0)?;
    let mut pending = vec![tcx.expn_that_defined(owner)];
    let mut seen = HashSet::new();
    let mut result = Vec::new();
    while let Some(id) = pending.pop() {
        if id == ExpnId::root() || !seen.insert(id) {
            continue;
        }
        budget.charge(3, 0)?;
        if seen.len() > EXPANSIONS {
            return Err("origin observation expansion graph exceeds its bound");
        }
        if diagnostics(tcx).is_err() {
            return Err("native diagnostics revoke the origin observation");
        }
        let data = id.expn_data();
        if let ExpnKind::Macro(macro_kind, _) = data.kind {
            if let Some(definition) = data.macro_def_id {
                if cohort.owns_macro(definition) {
                    if result.len() >= EVENTS {
                        return Err("origin observation event inventory exceeds its bound");
                    }
                    budget.charge(2, 0)?;
                    let source = coordinates(tcx, data.call_site, budget)?;
                    let macro_kind = match macro_kind {
                        MacroKind::Bang => "Bang",
                        MacroKind::Attr => "Attribute",
                        MacroKind::Derive => "Derive",
                    };
                    result.push(ObservedEvent {
                        id,
                        call_site: data.call_site,
                        row: json!({
                            "native_expansion": expansion(id), "macro_kind": macro_kind,
                            "macro_definition": key(tcx, definition), "selected_cohort_macro": true,
                            "callsite_coordinates": source,
                            "new_source_binding_authorized": false,
                        }),
                    });
                }
            }
        }
        pending.extend([data.parent, data.call_site.ctxt().outer_expn()]);
    }
    Ok(result)
}

fn event_relation(
    tcx: TyCtxt<'_>,
    site: &Site<'_, '_, '_>,
    cohort: &Cohort<'_, '_>,
    budget: &mut Budget,
) -> Result<Value, &'static str> {
    let nominal = event_inventory(tcx, site.nominal.definition, cohort, budget)?;
    let implementation = event_inventory(tcx, site.owner, cohort, budget)?;
    let mut qualified_nominal_events = Vec::new();
    for event in &site.nominal.events {
        qualified_nominal_events.push(json!({"native_expansion": expansion(event.id),
            "already_source_bound_callsite": bound_anchor(&event.call_site, budget)?}));
    }
    let mut equalities = Vec::new();
    for (nominal_index, expected) in nominal.iter().enumerate() {
        for (impl_index, actual) in implementation.iter().enumerate() {
            budget.charge(1, 0)?;
            if expected.id == actual.id {
                equalities.push(
                    json!({"nominal_event": nominal_index, "impl_event": impl_index,
                    "native_expansion_equal": true,
                    "native_callsite_span_equal": expected.call_site == actual.call_site}),
                );
            }
        }
    }
    Ok(json!({"state": "ObservedNativeEventRelation",
        "defining_expansion_equal": tcx.expn_that_defined(site.nominal.definition)
            == tcx.expn_that_defined(site.owner),
        "nominal_defining_expansion": expansion(tcx.expn_that_defined(site.nominal.definition)),
        "impl_defining_expansion": expansion(tcx.expn_that_defined(site.owner)),
        "qualification_nominal_event_count": site.nominal.events.len(),
        "qualification_collects_nominal_events": tcx.def_kind(site.nominal.definition) == DefKind::Enum,
        "already_qualified_nominal_event_anchors": qualified_nominal_events,
        "nominal_observed_events": nominal.into_iter().map(|event| event.row).collect::<Vec<_>>(),
        "impl_observed_events": implementation.into_iter().map(|event| event.row).collect::<Vec<_>>(),
        "equal_native_event_pairs": equalities,
        "synthesis_authorized": false}))
}

fn record(
    tcx: TyCtxt<'_>,
    site: Site<'_, '_, '_>,
    cohort: &Cohort<'_, '_>,
) -> Result<Value, &'static str> {
    if diagnostics(tcx).is_err() {
        return Err("native diagnostics revoke the origin observation");
    }
    let mut budget = Budget::new();
    budget.charge(32, 0)?;
    let nominal_original = match site
        .nominal
        .definition
        .as_local()
        .and_then(|local| tcx.lower_to_hir(local).as_owner())
        .map(|owner| owner.node())
    {
        Some(OwnerNode::Item(item)) => span(tcx, item.span, &mut budget)?,
        _ => unknown("the nominal original item span is unavailable"),
    };
    let nominal = json!({"native_key": key(tcx, site.nominal.definition),
        "native_kind": kind(tcx.def_kind(site.nominal.definition)),
        "definition_span": span(tcx, tcx.def_span(site.nominal.definition), &mut budget)?,
        "identifier_span": match tcx.def_ident_span(site.nominal.definition) {
            Some(value) => span(tcx, value, &mut budget)?,
            None => unknown("the nominal native identifier span is unavailable"),
        },
        "original_item_span": nominal_original,
        "checked_envelope": bound_anchor(&site.nominal.envelope, &mut budget)?,
        "checked_identifier": bound_anchor(&site.nominal.identifier, &mut budget)?});
    let resolution = match site.resolution {
        Res::Def(def_kind, owner) => json!({"state": "ResolvedNativeDefinition",
            "native_key": key(tcx, owner), "native_kind": kind(def_kind),
            "same_nominal_definition": owner == site.nominal.definition}),
        _ => unknown("the Self path is not resolved to a native definition"),
    };
    let implementation = json!({"native_key": key(tcx, site.owner),
        "native_kind": kind(tcx.def_kind(site.owner)),
        "definition_header_span": span(tcx, tcx.def_span(site.owner), &mut budget)?,
        "original_full_item_span": span(tcx, site.original.span, &mut budget)?,
        "self_type_span": span(tcx, site.self_type.span, &mut budget)?,
        "self_identifier_span": span(tcx, site.self_identifier, &mut budget)?,
        "checked_header": bound_anchor(site.declaration, &mut budget)?,
        "checked_full_item": bound_anchor(site.envelope, &mut budget)?,
        "checked_self_identifier": bound_anchor(site.identifier, &mut budget)?,
        "self_path_resolution": resolution});
    let predicates = json!({
        "header_inside_full_item": contains(site.envelope, site.declaration),
        "authored_header": authored(site.declaration, &site.nominal.envelope, site.identifier),
        "authored_full_item": authored(site.envelope, &site.nominal.envelope, site.identifier),
        "self_resolves_to_exact_enum": matches!(site.resolution,
            Res::Def(DefKind::Enum, owner) if owner == site.nominal.definition),
        "self_identifier_equals_nominal_identifier": site.identifier == &site.nominal.identifier,
        "header_inside_nominal": contains(&site.nominal.envelope, site.declaration),
        "full_item_inside_nominal": contains(&site.nominal.envelope, site.envelope),
    });
    let attributes =
        attributes::capture(tcx, site.nominal.definition, &mut budget).unwrap_or_else(unknown);
    let relation = event_relation(tcx, &site, cohort, &mut budget).unwrap_or_else(unknown);
    if diagnostics(tcx).is_err() {
        return Err("native diagnostics revoke the origin observation");
    }
    Ok(json!({"schema": "trust-vc-nominal-origin-refusal@1",
        "state": "ObservedOriginRefusalContext", "scope": "diagnostic only", "nominal": nominal,
        "implementation": implementation, "existing_attribution_predicates": predicates,
        "nominal_root_attributes": attributes,
        "native_event_relation": relation, "observation_work_cap": WORK,
        "observation_text_byte_cap": TEXT_BYTES, "observation_json_byte_cap": JSON_BYTES,
        "observation_work_remaining": budget.work, "observation_text_bytes_remaining": budget.bytes,
        "observation_budget_refused": budget.refused,
        "qualification_work_unchanged": true, "helper_authorized": false,
        "import_authorized": false, "ownership_authorized": false}))
}

struct SizeLimit(usize);
impl Write for SizeLimit {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.0 = self
            .0
            .checked_sub(bytes.len())
            .ok_or_else(|| io::Error::other("origin observation JSON exceeds its byte bound"))?;
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

fn finish(result: Result<Value, &'static str>) -> Value {
    match result {
        Ok(value) if serde_json::to_writer(SizeLimit(JSON_BYTES), &value).is_ok() => value,
        Ok(_) => unknown("origin observation JSON exceeds its byte bound"),
        Err(reason) => unknown(reason),
    }
}

pub(super) fn capture(tcx: TyCtxt<'_>, site: Site<'_, '_, '_>, cohort: &Cohort<'_, '_>) -> Value {
    finish(record(tcx, site, cohort))
}

#[cfg(test)]
mod tests;
