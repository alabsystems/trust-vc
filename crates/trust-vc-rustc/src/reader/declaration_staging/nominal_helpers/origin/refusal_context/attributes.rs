// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Real root-owned attribute observations, never a source-extent constructor.

use rustc_ast::{
    token::{Delimiter, DocFragmentKind},
    AttrStyle,
};
use rustc_attr_ir::{AttrArgs, Attribute, AttributeKind};

use super::*;

const ATTRIBUTES: usize = 32;
const PATH_SEGMENTS: usize = 16;
const TOP_LEVEL_TOKENS: usize = 64;

pub(super) fn copy_text(text: &str, budget: &mut Budget) -> Result<String, &'static str> {
    budget.charge(1, text.len())?;
    Ok(text.to_owned())
}

fn style(style: AttrStyle) -> &'static str {
    match style {
        AttrStyle::Outer => "Outer",
        AttrStyle::Inner => "Inner",
    }
}

fn same_attribute(original: &Attribute, current: Option<&Attribute>) -> bool {
    current.is_some_and(|current| std::ptr::eq(original, current))
}

fn argument_shape(args: &AttrArgs, budget: &mut Budget) -> Result<Value, &'static str> {
    budget.charge(1, 0)?;
    Ok(match args {
        AttrArgs::Empty => json!({"state": "ObservedArgumentShape", "kind": "Empty"}),
        AttrArgs::Eq { .. } => json!({"state": "ObservedArgumentShape", "kind": "NameValue",
            "payload_copied": false}),
        AttrArgs::Delimited(args) => {
            let mut count = 0;
            for _ in args.tokens.iter().take(TOP_LEVEL_TOKENS + 1) {
                budget.charge(1, 0)?;
                count += 1;
            }
            if count > TOP_LEVEL_TOKENS {
                json!({"state": "Unknown", "reason": "attribute top-level token count exceeds the observation bound",
                    "observed_lower_bound": count, "cap": TOP_LEVEL_TOKENS})
            } else {
                let delimiter = match args.delim {
                    Delimiter::Parenthesis => "Parenthesis",
                    Delimiter::Bracket => "Bracket",
                    Delimiter::Brace => "Brace",
                    _ => "OtherNativeDelimiter",
                };
                json!({"state": "ObservedArgumentShape", "kind": "Delimited", "delimiter": delimiter,
                    "top_level_token_count": count, "nested_tokens_traversed": false,
                    "payload_copied": false})
            }
        }
    })
}

fn row(
    tcx: TyCtxt<'_>,
    slot: usize,
    attribute: &Attribute,
    current: Option<&Attribute>,
    budget: &mut Budget,
) -> Result<Value, &'static str> {
    budget.charge(1, 0)?;
    let detail = match attribute {
        Attribute::Unparsed(item) => {
            let path = if item.path.segments.len() > PATH_SEGMENTS {
                json!({"state": "Unknown", "reason": "attribute path exceeds the observation bound",
                    "count": item.path.segments.len(), "cap": PATH_SEGMENTS})
            } else {
                let mut parts = Vec::new();
                for name in &item.path.segments {
                    let text = name.as_str();
                    parts.push(copy_text(&text, budget)?);
                }
                json!({"state": "ObservedNativeAttributePath", "segments": parts,
                    "path_is_authority": false})
            };
            json!({"kind": "Unparsed", "style": style(item.style),
                "native_attr_id": item.id.attr_id.as_u32(),
                "native_attr_id_scope": "this compiler session only; not pointer ownership",
                "native_span": span(tcx, item.span, budget)?,
                "native_path_span": span(tcx, item.path.span, budget)?,
                "path_observation": path, "argument_observation": argument_shape(&item.args, budget)?})
        }
        Attribute::Parsed(AttributeKind::DocComment {
            style: attr_style,
            kind,
            span: source,
            comment,
        }) => {
            let kind = match kind {
                DocFragmentKind::Sugared(_) => "SugaredDocComment",
                DocFragmentKind::Raw(_) => "RawDocAttribute",
            };
            budget.charge(1, 0)?;
            json!({"kind": "ParsedDocComment", "doc_kind": kind, "style": style(*attr_style),
                "native_attr_id": null, "native_attr_id_state": "not retained for this native kind",
                "native_span": span(tcx, *source, budget)?,
                "comment_utf8_bytes": comment.as_str().len(), "comment_copied": false})
        }
        Attribute::Parsed(_) => json!({"kind": "OtherParsed",
            "style": unknown("this native parsed kind has no general style accessor"),
            "native_attr_id": null,
            "native_span": unknown("this native parsed kind has no general span accessor"),
            "source_extent_evidence": "Unknown"}),
    };
    Ok(
        json!({"slot": slot, "original_reference_matches_current_slot": same_attribute(attribute, current),
        "detail": detail, "source_extent_authorized": false}),
    )
}

pub(super) fn capture(
    tcx: TyCtxt<'_>,
    owner: DefId,
    budget: &mut Budget,
) -> Result<Value, &'static str> {
    budget.charge(4, 0)?;
    if diagnostics(tcx).is_err() {
        return Err("native diagnostics revoke root attribute observation");
    }
    let local = owner
        .as_local()
        .ok_or("root attributes require a local original owner")?;
    let raw = tcx
        .lower_to_hir(local)
        .as_owner()
        .ok_or("the original root attribute owner is unavailable")?;
    let OwnerNode::Item(item) = raw.node() else {
        return Err("the original root attribute owner is not an item");
    };
    let hir_id = tcx.local_def_id_to_hir_id(local);
    let original = raw.attrs.get(hir_id.local_id);
    let current = tcx.hir_attrs(hir_id);
    let original_item_pointer_matches = match tcx.hir_node_by_def_id(local) {
        hir::Node::Item(current) => std::ptr::eq(item, current),
        _ => false,
    };
    let mut rows = Vec::new();
    let inventory = if original.len() > ATTRIBUTES {
        unknown("original root attribute count exceeds the observation bound")
    } else {
        for (slot, attribute) in original.iter().enumerate() {
            rows.push(row(tcx, slot, attribute, current.get(slot), budget)?);
        }
        json!({"state": "ObservedRootAttributeSlots", "slots": rows})
    };
    if diagnostics(tcx).is_err() {
        return Err("native diagnostics revoke root attribute observation");
    }
    Ok(
        json!({"state": "ObservedOriginalRootAttributes", "owner": key(tcx, owner),
        "original_item_owner": key(tcx, item.owner_id.def_id.to_def_id()),
        "root_hir_owner": key(tcx, hir_id.owner.def_id.to_def_id()),
        "root_hir_local_index": hir_id.local_id.as_u32(),
        "original_item_pointer_matches_current": original_item_pointer_matches,
        "original_root_slice_pointer_matches_hir_attrs": std::ptr::eq(original, current),
        "original_root_attribute_count": original.len(), "current_root_attribute_count": current.len(),
        "attribute_cap": ATTRIBUTES, "path_segment_cap": PATH_SEGMENTS,
        "top_level_token_cap": TOP_LEVEL_TOKENS, "inventory": inventory,
        "source_extent_authorized": false, "helper_authorized": false,
        "import_authorized": false}),
    )
}

#[cfg(test)]
mod tests;
