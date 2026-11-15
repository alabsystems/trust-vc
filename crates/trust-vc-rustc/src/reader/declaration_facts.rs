//! Declaration observations from an expanded Keep-body crate.
//!
//! These observations are an input to a future authenticated producer, not
//! an import receipt. In particular, a completed body traversal which sees
//! no header reference is not KnownEmpty until macro/source provenance and
//! the exact Erase declaration have also been authenticated.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashSet;

use rustc_hir::def::DefKind;
use rustc_hir::def_id::{CrateNum, DefId, DefIndex, LocalDefId};
use rustc_middle::ty::TyCtxt;
use rustc_span::{ExpnId, FileName, Pos, Span};
use serde_json::{json, Value};
use trust_vc_vcir::Mode;

use super::attrs::{self, VerusAttr};
use super::modes::{self, ModeOrigin, ResolvedMode};
use crate::declaration_alignment::observation::NativeDeclarationKind;

fn unknown(reason: &str) -> Value {
    json!({"state": "Unknown", "reason": reason})
}

// Coordinates come from the real compiler SourceFile, not a parsed Debug
// string. Authentication against the pinned source manifest remains separate.
pub(super) fn source_anchor(tcx: TyCtxt<'_>, span: Span) -> Value {
    if span.is_dummy() {
        return unknown("a dummy source span has no authored anchor");
    }
    let file = tcx.sess.source_map().lookup_source_file(span.lo());
    if !file.contains(span.hi()) {
        return unknown("a cross-file source span cannot be an authored anchor");
    }
    let FileName::Real(name) = &file.name else {
        return unknown("virtual or macro-generated source has no real file anchor");
    };
    let Some(path) = name.local_path() else {
        return unknown("the compiler source file has no available local path");
    };
    let original_lo = file.original_relative_byte_pos(span.lo()).to_u32();
    let original_hi = file.original_relative_byte_pos(span.hi()).to_u32();
    if original_lo > original_hi || original_hi > file.unnormalized_source_len {
        return unknown("source coordinates are outside the original file");
    }
    json!({
        "state": "ObservedRealSourceAnchor",
        "local_path": path.display().to_string(),
        "compiler_source_hash": file.src_hash.to_string(),
        "compiler_source_file_id_debug": format!("{:?}", file.stable_id),
        "normalized_lo": file.relative_position(span.lo()).to_u32(),
        "normalized_hi": file.relative_position(span.hi()).to_u32(),
        "original_lo": original_lo, "original_hi": original_hi,
        "original_file_len": file.unnormalized_source_len,
        "imported": file.is_imported(),
        "source_manifest_authentication": unknown("the wrapper must bind these compiler file coordinates/hash to approved source bytes"),
    })
}

fn native_declaration_kind(kind: DefKind) -> NativeDeclarationKind {
    match kind {
        DefKind::Fn => NativeDeclarationKind::Function,
        DefKind::AssocFn => NativeDeclarationKind::AssociatedFunction,
        DefKind::Struct => NativeDeclarationKind::Struct,
        DefKind::Enum => NativeDeclarationKind::Enum,
        DefKind::Union => NativeDeclarationKind::Union,
        DefKind::Impl { of_trait: false } => NativeDeclarationKind::InherentImplementation,
        DefKind::Impl { of_trait: true } => NativeDeclarationKind::TraitImplementation,
        DefKind::Mod => NativeDeclarationKind::Module,
        DefKind::Trait => NativeDeclarationKind::Trait,
        _ => NativeDeclarationKind::Other,
    }
}

// Deliberately does not request the local SVH. At this pre-MIR seam, computing
// a local crate hash is not a substitute for an emitted Erase artifact.
pub(super) fn definition(tcx: TyCtxt<'_>, def: DefId) -> Value {
    let (high, low) = tcx.def_path_hash(def).0.split();
    let kind = native_declaration_kind(tcx.def_kind(def));
    json!({
        "def_path_hash": format!("{:016x}{:016x}", high.as_u64(), low.as_u64()),
        "stable_crate_id": format!("{:016x}", tcx.stable_crate_id(def.krate).as_u64()),
        "declaration_kind": kind.machine_name(),
        "kind_debug": format!("{:?}", tcx.def_kind(def)),
        "path_display_only": tcx.def_path_str(def),
        "item_name_observation": tcx.opt_item_name(def).map(|name| name.to_string()),
        "source_span_debug": format!("{:?}", tcx.def_span(def)),
        "source_callsite_debug": format!("{:?}", tcx.def_span(def).source_callsite()),
        "definition_anchor": source_anchor(tcx, tcx.def_span(def)),
        "identifier_anchor": tcx.def_ident_span(def).map(|span| source_anchor(tcx, span))
            .unwrap_or_else(|| unknown("the compiler provides no identifier span for this definition")),
        "source_callsite_anchor": source_anchor(tcx, tcx.def_span(def).source_callsite()),
    })
}

fn authored_scope_anchors(tcx: TyCtxt<'_>, def: DefId) -> Value {
    let mut scopes = Vec::new();
    let mut current = tcx.opt_parent(def);
    while let Some(scope) = current {
        if scopes.len() >= 64 {
            return unknown("authored scope ancestry exceeded its bound");
        }
        let kind = tcx.def_kind(scope);
        // Compiler crate-root spans are not authored module declarations.
        if tcx.opt_parent(scope).is_none() {
            break;
        }
        scopes.push(json!({
            "declaration_kind": native_declaration_kind(kind).machine_name(),
            "kind_debug": format!("{kind:?}"),
            "definition_anchor": source_anchor(tcx, tcx.def_span(scope)),
            "identifier_anchor": tcx.def_ident_span(scope).map(|span| source_anchor(tcx, span)),
        }));
        current = tcx.opt_parent(scope);
    }
    scopes.reverse();
    json!({"state": "ObservedAuthoredScopeCandidates", "scopes": scopes,
        "authentication": unknown("every authored file/range must be bound to approved bytes; missing/synthetic anchors remain Unknown")})
}

fn function_container(tcx: TyCtxt<'_>, def: DefId) -> Value {
    let Some(parent) = tcx.opt_parent(def) else {
        return unknown("no declaration parent");
    };
    match tcx.def_kind(parent) {
        DefKind::Mod => json!({"state": "ObservedFreeFunction", "parent": definition(tcx, parent)}),
        DefKind::Impl { of_trait: false } => json!({
            "state": "ObservedInherentDeclaration", "parent": definition(tcx, parent),
            "structural_self_type": super::declaration_types::nominal(tcx, parent),
            "applicable_concrete_impl": unknown("a generic declaration is not a selected call instance"),
        }),
        _ => unknown("trait/default/inherited or other function origin needs a separate contract correspondence"),
    }
}

fn resolved_mode(value: ResolvedMode) -> Value {
    let origin = match value.origin {
        ModeOrigin::FunctionDefault => json!({"kind": "FunctionDefault"}),
        ModeOrigin::ImplicitReturn => json!({"kind": "ImplicitReturn"}),
        ModeOrigin::Attribute(span) => {
            json!({"kind": "Attribute", "span_debug": format!("{span:?}")})
        }
    };
    json!({"mode": format!("{:?}", value.mode), "origin": origin})
}

pub(super) fn expansion_chain(tcx: TyCtxt<'_>, start: ExpnId) -> Value {
    let mut pending = vec![start];
    let mut visited = HashSet::new();
    let mut records = Vec::new();
    while let Some(id) = pending.pop() {
        if id == ExpnId::root() || !visited.insert(id) {
            continue;
        }
        if visited.len() > 128 {
            return unknown("expansion provenance exceeded its bounded traversal");
        }
        let data = id.expn_data();
        records.push(json!({
            "expansion_debug": format!("{id:?}"),
            "kind_debug": format!("{:?}", data.kind),
            "macro_definition": data.macro_def_id.map(|def| definition(tcx, def)),
            "call_site_debug": format!("{:?}", data.call_site),
            "definition_site_debug": format!("{:?}", data.def_site),
            "call_site_anchor": source_anchor(tcx, data.call_site),
            "definition_site_anchor": source_anchor(tcx, data.def_site),
            "parent_debug": format!("{:?}", data.parent),
            "call_site_expansion_debug": format!("{:?}", data.call_site.ctxt().outer_expn()),
        }));
        pending.extend([data.parent, data.call_site.ctxt().outer_expn()]);
    }
    json!({"state": "ObservedExpansionGraph", "records": records,
        "artifact_authorization": unknown("the wrapper must bind every macro definition to the authorized artifact/source cohort")})
}

/// Project declarations without reading private ADT fields, lowering bodies or
/// admitting imports. Public spelling is an inventory filter, never authority.
pub(crate) fn observe(tcx: TyCtxt<'_>) -> Value {
    let mut rows = Vec::new();
    let mut types = Vec::new();
    let mode_index = super::declaration_modes::DeclarationModes::new(tcx);
    for owner in tcx.hir_crate_items(()).owners() {
        let local = owner.def_id;
        let def = local.to_def_id();
        let kind = tcx.def_kind(def);
        if !matches!(
            kind,
            DefKind::Fn | DefKind::AssocFn | DefKind::Struct | DefKind::Enum | DefKind::Union
        ) || !tcx.visibility(def).is_public()
        {
            continue;
        }
        let hir_id = tcx.local_def_id_to_hir_id(local);
        let parsed = attrs::item_attrs(tcx.hir_attrs(hir_id));
        if !parsed.verus_macro {
            continue;
        }
        if matches!(kind, DefKind::Struct | DefKind::Enum | DefKind::Union) {
            types.push(json!({
                "definition": definition(tcx, def),
                "authored_scope_anchors": authored_scope_anchors(tcx, def),
                "structural_nominal_type": super::declaration_types::nominal(tcx, def),
                "generics_debug": format!("{:?}", tcx.generics_of(def)),
                "declaration_type_unnormalized_debug": format!("{:?}", tcx.type_of(def).instantiate_identity()),
                "item_expansion_graph": expansion_chain(tcx, tcx.expn_that_defined(def)),
                "opaque_carrier_authority": unknown("no carrier or private representation is imported"),
                "keep_erase_alignment": unknown("no Erase row is joined by this observation tool"),
                "import_authorized": false,
            }));
            continue;
        }
        // Trait specification/default/inherited-body correspondence needs its
        // own producer evidence; this slice never substitutes a trait body.
        let parent = tcx.local_parent(local);
        let trait_origin =
            tcx.def_kind(parent) == DefKind::Trait || tcx.trait_impl_of_assoc(def).is_some();
        let signature_modes = if trait_origin {
            unknown("trait declaration/implementation contract inheritance is outside this producer slice")
        } else {
            match modes::local_signature_modes(
                tcx,
                local,
                local,
                parsed.mode.unwrap_or(Mode::Exec),
                &parsed,
                tcx.def_span(def),
            ) {
                Ok(signature) => json!({
                    "state": "ResolvedLocalDeclarationModes",
                    "function": format!("{:?}", signature.mode),
                    "parameters": signature.params.iter().map(|param| json!({
                        "declared": resolved_mode(param.declared),
                        "mutable_reference": param.mutable_reference,
                        "span_debug": format!("{:?}", param.span),
                    })).collect::<Vec<_>>(),
                    "return": resolved_mode(signature.ret),
                    "body_mode_check": unknown("declaration elaboration does not check body modes"),
                }),
                Err(refusal) => unknown(&format!("{}: {}", refusal.tag, refusal.detail)),
            }
        };
        let mut attrs_unknown = Vec::new();
        for (attr, span) in attrs::verus_attrs(tcx.hir_attrs(hir_id)) {
            if !matches!(
                attr,
                VerusAttr::VerusMacro
                    | VerusAttr::Mode(_)
                    | VerusAttr::ReturnMode(_)
                    | VerusAttr::Visibility { .. }
            ) {
                attrs_unknown.push(format!("{attr:?} at {span:?}"));
            }
        }
        let original_body = !trait_origin && mode_index.has_original_body(local);
        let header = super::declaration_headers::check(tcx, local).observation();
        let body_modes = if !original_body {
            unknown("a projected/quarantined or unavailable original body cannot supply whole-body mode facts")
        } else if trait_origin || !attrs_unknown.is_empty() {
            unknown("the declaration origin/directives require another body-mode producer policy")
        } else {
            match mode_index.check(local) {
                modes::ModeCheck::Clean(checked)
                    if checked.signature.def_id == def && checked.signature.body_owner == local =>
                {
                    json!({
                        "state": "CheckedLocalBodyModes",
                        "original_definition": definition(tcx, def),
                        "body_owner": definition(tcx, local.to_def_id()),
                        "plain_local_declarations_checked": checked.local_declarations.len(),
                        "check_scope": "the shared mode walk completed for this actual local body",
                        "private_field_mode_reads": false,
                        "ownership_checked": false, "body_verified": false,
                        "header_or_import_authority": unknown("mode checking alone grants no header or import authority"),
                    })
                }
                modes::ModeCheck::Clean(_) => {
                    unknown("the completed mode walk belongs to a different body owner")
                }
                modes::ModeCheck::Error(error) => json!({
                    "state": "RejectedBodyModes", "phase_debug": format!("{:?}", error.phase),
                    "message": error.message, "span_debug": format!("{:?}", error.span),
                    "import_authorized": false,
                }),
                modes::ModeCheck::Unknown(refusal) => {
                    unknown(&format!("{}: {}", refusal.tag, refusal.detail))
                }
            }
        };
        rows.push(json!({
            "definition": definition(tcx, def),
            "authored_scope_anchors": authored_scope_anchors(tcx, def),
            "function_container": function_container(tcx, def),
            "parent": definition(tcx, parent.to_def_id()),
            "visibility_debug": format!("{:?}", tcx.visibility(def)),
            "signature_unnormalized_debug": format!("{:?}", tcx.fn_sig(def).instantiate_identity()),
            "structural_signature": super::declaration_types::signature(tcx, def),
            "generics_debug": format!("{:?}", tcx.generics_of(def)),
            "explicit_clauses_debug": format!("{:?}", tcx.explicit_clauses_of(def)),
            "signature_modes": signature_modes,
            "body_input_view": if original_body { json!({"state": "OriginalUnprojectedBody"}) }
                else { unknown("no original body-mode/header receipt is granted for this declaration") },
            "body_mode_observation": body_modes,
            "header_observation": header,
            "item_expansion_graph": expansion_chain(tcx, tcx.expn_that_defined(def)),
            "unclassified_item_directives": attrs_unknown,
            "keep_erase_alignment": unknown("no Erase row is joined by this observation tool"),
            "body_verification": unknown("no verifier or ownership pass ran on Keep bodies"),
            "import_authorized": false,
        }));
    }
    json!({
        "schema": "trust-vc.keep-declaration-observation@2",
        "authority": "declaration observations only; not an import or proof receipt",
        "rows": rows,
        "types": types,
        "local_svh": unknown("not requested before MIR; bind the separate normally compiled Erase artifact"),
        "import_authorized": false,
        "verified_functions": null,
        "body_mode_observation_scope": "per-declaration shared mode checks only; Unknown/errors retained; no native ownership, body proof or import authority",
        "body_mode_checker_reads_private_field_declarations": false,
        "private_representation_or_axioms_read": false,
    })
}

/// Inventory the actual selected foreign crate using the same structural
/// declaration codec as Keep. This reads public declarations and attributes,
/// never private ADT fields, bodies, layouts, MIR or library axioms.
///
/// Erase has no authoritative parameter/header HIR. No surviving attribute or
/// panic body is upgraded to resolved modes, KnownEmpty headers or a proof.
#[allow(deprecated)]
pub(crate) fn observe_foreign(tcx: TyCtxt<'_>, krate: CrateNum) -> Result<Value, String> {
    if krate == rustc_hir::def_id::LOCAL_CRATE {
        return Err(
            "foreign declaration observation requires an actual loaded external crate".into(),
        );
    }
    let mut rows = Vec::new();
    let mut types = Vec::new();
    let mut kinds = std::collections::BTreeMap::<String, usize>::new();
    // Exact Trust29 documents this query for enumerating all foreign defs.
    // No local def indices or name/reexport traversal stand in for metadata.
    let definitions = tcx.num_extern_def_ids(krate);
    for index in 0..definitions {
        let def = DefId {
            krate,
            index: DefIndex::from_usize(index),
        };
        let kind = tcx.def_kind(def);
        *kinds.entry(format!("{kind:?}")).or_default() += 1;
        if !matches!(
            kind,
            DefKind::Fn | DefKind::AssocFn | DefKind::Struct | DefKind::Enum | DefKind::Union
        ) || !tcx.visibility(def).is_public()
        {
            continue;
        }
        let raw_attrs = tcx.get_all_attrs(def);
        let parsed = attrs::item_attrs(raw_attrs);
        // The pinned macro adds this function marker only in Keep, while
        // Erase still retains the real public signature and Spec/closed
        // attrs (syntax.rs:873-875). Missing metadata markers cannot remove
        // declarations from this inventory or donate source authority.
        let raw_attrs_debug: Vec<_> = raw_attrs.iter().map(|attr| format!("{attr:#?}")).collect();
        if matches!(kind, DefKind::Struct | DefKind::Enum | DefKind::Union) {
            types.push(json!({
                "definition": definition(tcx, def),
                "authored_scope_anchors": authored_scope_anchors(tcx, def),
                "structural_nominal_type": super::declaration_types::nominal(tcx, def),
                "raw_item_attrs_debug": raw_attrs_debug,
                "verus_macro_marker_observed": parsed.verus_macro,
                "opaque_carrier_authority": unknown("a structural observation imports no carrier/private representation"),
                "keep_erase_alignment": unknown("source/structural candidates must be separately joined and authenticated"),
            }));
        } else {
            rows.push(json!({
                "definition": definition(tcx, def),
                "authored_scope_anchors": authored_scope_anchors(tcx, def),
                "function_container": function_container(tcx, def),
                "structural_signature": super::declaration_types::signature(tcx, def),
                "raw_item_attrs_debug": raw_attrs_debug,
                "verus_macro_marker_observed": parsed.verus_macro,
                "explicit_clauses_debug": format!("{:?}", tcx.explicit_clauses_of(def)),
                "signature_modes": unknown("Erase attributes/signatures do not establish resolved Keep parameter/return modes"),
                "header_authority": unknown("Erase removes original headers; an empty/panic body is not evidence of absent headers"),
                "keep_erase_alignment": unknown("source/structural candidates must be separately joined and authenticated"),
                "body_verification": unknown("declaration compilation did not verify original Keep bodies"),
            }));
        }
    }
    Ok(json!({
        "schema": "trust-vc.erase-declaration-observation@2",
        "stable_crate_id": format!("{:016x}", tcx.stable_crate_id(krate).as_u64()),
        "svh": tcx.crate_hash(krate).to_string(),
        "enumerated_definition_slots": definitions,
        "definition_kind_counts_observed": kinds,
        "inventory_filter": "all public Fn/AssocFn/Struct/Enum/Union declarations; no Keep-marker filter",
        "rows": rows, "types": types,
        "authority": "metadata declaration observations only; not an import or proof receipt",
        "import_authorized": false, "verified_functions": null,
        "private_representation_or_axioms_read": false,
    }))
}
