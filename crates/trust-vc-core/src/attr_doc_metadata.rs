// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Durable doc-attr metadata transport for attr-based Verus-gap features.
//!
//! Emits and parses item-level `#[doc = "trust_vc:..."]` metadata for
//! `#[decreases]`, `#[broadcast]`, `#[trigger]`, `#[auto_trigger]`, and
//! `#[all_triggers]`.
//!
//! Part of #2569 (`#1558` doc-attr bridge).

use std::collections::BTreeMap;

const DECREASES_ENTRY_PREFIX: &str = "trust_vc:decreases:entry=";
const DECREASES_WHEN_PREFIX: &str = "trust_vc:decreases:when=";
const DECREASES_VIA_PREFIX: &str = "trust_vc:decreases:via=";
const BROADCAST_DOC_MARKER: &str = "trust_vc:broadcast";
const BROADCAST_GROUP_PREFIX: &str = "trust_vc:broadcast:group=";
const TRIGGER_DOC_PREFIX: &str = "trust_vc:trigger:";
const TRIGGER_GROUP_KEY: &str = "group=";
const TRIGGER_PATTERN_KEY: &str = "pattern=";
const TRIGGER_MODE_PREFIX: &str = "trust_vc:trigger:mode=";

/// Durable `#[decreases(...)]` metadata recovered from item doc attrs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DecreasesDocMetadata {
    pub(crate) entry: String,
    pub(crate) when: Option<String>,
    pub(crate) via: Option<String>,
}

/// Durable `#[broadcast]` metadata recovered from item doc attrs.
#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct BroadcastDocMetadata {
    pub(crate) is_broadcast: bool,
    pub(crate) group_name: Option<String>,
}

/// One indexed trigger entry recovered from item doc attrs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TriggerDocEntry {
    pub(crate) index: usize,
    pub(crate) group: usize,
    pub(crate) pattern: String,
}

/// Durable trigger inference mode recovered from item doc attrs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TriggerModeDoc {
    Conservative,
    Aggressive,
}

impl TriggerModeDoc {
    fn as_doc_value(self) -> &'static str {
        match self {
            Self::Conservative => "conservative",
            Self::Aggressive => "aggressive",
        }
    }
}

/// Durable trigger metadata recovered from item doc attrs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TriggerDocMetadata {
    pub(crate) triggers: Vec<TriggerDocEntry>,
    pub(crate) mode: Option<TriggerModeDoc>,
}

#[derive(Default)]
struct PartialTriggerDocEntry {
    group: Option<usize>,
    pattern: Option<String>,
}

pub(crate) fn decreases_entry_doc_attr(entry: &str) -> String {
    format!("{DECREASES_ENTRY_PREFIX}{entry}")
}

pub(crate) fn decreases_when_doc_attr(condition: &str) -> String {
    format!("{DECREASES_WHEN_PREFIX}{condition}")
}

pub(crate) fn decreases_via_doc_attr(path: &str) -> String {
    format!("{DECREASES_VIA_PREFIX}{path}")
}

pub(crate) fn broadcast_marker_doc_attr() -> &'static str {
    BROADCAST_DOC_MARKER
}

pub(crate) fn broadcast_group_doc_attr(group_name: &str) -> String {
    format!("{BROADCAST_GROUP_PREFIX}{group_name}")
}

pub(crate) fn trigger_group_doc_attr(index: usize, group: usize) -> String {
    format!("{TRIGGER_DOC_PREFIX}{index}:{TRIGGER_GROUP_KEY}{group}")
}

pub(crate) fn trigger_pattern_doc_attr(index: usize, pattern: &str) -> String {
    format!("{TRIGGER_DOC_PREFIX}{index}:{TRIGGER_PATTERN_KEY}{pattern}")
}

pub(crate) fn trigger_mode_doc_attr(mode: TriggerModeDoc) -> String {
    format!("{TRIGGER_MODE_PREFIX}{}", mode.as_doc_value())
}

pub(crate) fn extract_decreases_doc_metadata(
    attrs: &[syn::Attribute],
) -> crate::error::TrustVcResult<Option<DecreasesDocMetadata>> {
    let mut entry = None;
    let mut when = None;
    let mut via = None;

    for attr in attrs {
        let Some(value) = doc_value(attr) else {
            continue;
        };

        if let Some(raw_entry) = value.strip_prefix(DECREASES_ENTRY_PREFIX) {
            set_once("decreases entry", &mut entry, raw_entry.to_string())?;
        } else if let Some(raw_when) = value.strip_prefix(DECREASES_WHEN_PREFIX) {
            set_once("decreases when", &mut when, raw_when.to_string())?;
        } else if let Some(raw_via) = value.strip_prefix(DECREASES_VIA_PREFIX) {
            set_once("decreases via", &mut via, raw_via.to_string())?;
        }
    }

    match entry {
        Some(entry) => Ok(Some(DecreasesDocMetadata { entry, when, via })),
        None if when.is_some() || via.is_some() => Err(crate::error::TrustVcError::from(
            "malformed decreases doc metadata: when/via marker without entry marker".to_string(),
        )),
        None => Ok(None),
    }
}

#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn extract_broadcast_doc_metadata(
    attrs: &[syn::Attribute],
) -> crate::error::TrustVcResult<Option<BroadcastDocMetadata>> {
    let mut is_broadcast = false;
    let mut group_name = None;

    for attr in attrs {
        let Some(value) = doc_value(attr) else {
            continue;
        };

        if value == BROADCAST_DOC_MARKER {
            is_broadcast = true;
        } else if let Some(raw_group) = value.strip_prefix(BROADCAST_GROUP_PREFIX) {
            set_once("broadcast group", &mut group_name, raw_group.to_string())?;
        }
    }

    if is_broadcast {
        Ok(Some(BroadcastDocMetadata {
            is_broadcast: true,
            group_name,
        }))
    } else if group_name.is_some() {
        Err(crate::error::TrustVcError::from(
            "malformed broadcast doc metadata: group marker without trust_vc:broadcast marker"
                .to_string(),
        ))
    } else {
        Ok(None)
    }
}

pub(crate) fn extract_trigger_doc_metadata(
    attrs: &[syn::Attribute],
) -> crate::error::TrustVcResult<Option<TriggerDocMetadata>> {
    let mut mode = None;
    let mut triggers: BTreeMap<usize, PartialTriggerDocEntry> = BTreeMap::new();

    for attr in attrs {
        let Some(value) = doc_value(attr) else {
            continue;
        };

        if let Some(raw_mode) = value.strip_prefix(TRIGGER_MODE_PREFIX) {
            let parsed_mode = match raw_mode {
                "conservative" => TriggerModeDoc::Conservative,
                "aggressive" => TriggerModeDoc::Aggressive,
                _ => {
                    return Err(crate::error::TrustVcError::from(format!(
                        "malformed trigger doc metadata: unknown mode `{raw_mode}`"
                    )));
                }
            };
            set_once("trigger mode", &mut mode, parsed_mode)?;
            continue;
        }

        let Some(raw_trigger) = value.strip_prefix(TRIGGER_DOC_PREFIX) else {
            continue;
        };
        let Some((index_part, field_part)) = raw_trigger.split_once(':') else {
            return Err(crate::error::TrustVcError::from(format!(
                "malformed trigger doc metadata: missing indexed field in `{value}`"
            )));
        };

        let index = parse_usize(index_part, "trigger index", &value)?;
        let entry = triggers.entry(index).or_default();

        if let Some(raw_group) = field_part.strip_prefix(TRIGGER_GROUP_KEY) {
            let group = parse_usize(raw_group, "trigger group", &value)?;
            set_once("trigger group", &mut entry.group, group)?;
        } else if let Some(pattern) = field_part.strip_prefix(TRIGGER_PATTERN_KEY) {
            set_once("trigger pattern", &mut entry.pattern, pattern.to_string())?;
        } else {
            return Err(crate::error::TrustVcError::from(format!(
                "malformed trigger doc metadata: unknown indexed field `{field_part}`"
            )));
        }
    }

    if triggers.is_empty() && mode.is_none() {
        return Ok(None);
    }

    let triggers = triggers
        .into_iter()
        .map(|(index, entry)| {
            let group = entry.group.ok_or_else(|| {
                crate::error::TrustVcError::from(format!(
                    "malformed trigger doc metadata: trigger {index} missing group"
                ))
            })?;
            let pattern = entry.pattern.ok_or_else(|| {
                crate::error::TrustVcError::from(format!(
                    "malformed trigger doc metadata: trigger {index} missing pattern"
                ))
            })?;
            Ok(TriggerDocEntry {
                index,
                group,
                pattern,
            })
        })
        .collect::<crate::error::TrustVcResult<Vec<_>>>()?;

    Ok(Some(TriggerDocMetadata { triggers, mode }))
}

pub(crate) fn next_trigger_doc_index(
    attrs: &[syn::Attribute],
) -> crate::error::TrustVcResult<usize> {
    let Some(metadata) = extract_trigger_doc_metadata(attrs)? else {
        return Ok(0);
    };
    Ok(metadata
        .triggers
        .last()
        .map_or(0, |entry| entry.index.saturating_add(1)))
}

fn set_once<T>(
    field_name: &str,
    slot: &mut Option<T>,
    value: T,
) -> crate::error::TrustVcResult<()> {
    if slot.is_some() {
        return Err(crate::error::TrustVcError::from(format!(
            "malformed doc metadata: duplicate {field_name} marker"
        )));
    }
    *slot = Some(value);
    Ok(())
}

fn parse_usize(
    raw: &str,
    field_name: &str,
    full_value: &str,
) -> crate::error::TrustVcResult<usize> {
    raw.parse::<usize>().map_err(|_| {
        crate::error::TrustVcError::from(format!(
            "malformed trigger doc metadata: invalid {field_name} `{raw}` in `{full_value}`"
        ))
    })
}

fn doc_value(attr: &syn::Attribute) -> Option<String> {
    if !attr.path().is_ident("doc") {
        return None;
    }
    if let syn::Meta::NameValue(nv) = &attr.meta {
        if let syn::Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Str(s),
            ..
        }) = &nv.value
        {
            return Some(s.value());
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_attrs(code: &str) -> Vec<syn::Attribute> {
        let item: syn::ItemFn = syn::parse_str(code).expect("parse test function");
        item.attrs
    }

    #[test]
    fn test_extract_decreases_entry_only() {
        let attrs = parse_attrs(
            r#"
            #[doc = "trust_vc:decreases:entry=n"]
            fn foo() {}
            "#,
        );

        let metadata = extract_decreases_doc_metadata(&attrs)
            .expect("decreases metadata should parse")
            .expect("decreases metadata should exist");

        assert_eq!(metadata.entry, "n");
        assert_eq!(metadata.when, None);
        assert_eq!(metadata.via, None);
    }

    #[test]
    fn test_extract_decreases_with_when_and_via() {
        let attrs = parse_attrs(
            r#"
            #[doc = "trust_vc:decreases:entry=(m, n)"]
            #[doc = "trust_vc:decreases:when=n > 0"]
            #[doc = "trust_vc:decreases:via=prove_countdown"]
            fn foo() {}
            "#,
        );

        let metadata = extract_decreases_doc_metadata(&attrs)
            .expect("decreases metadata should parse")
            .expect("decreases metadata should exist");

        assert_eq!(metadata.entry, "(m, n)");
        assert_eq!(metadata.when.as_deref(), Some("n > 0"));
        assert_eq!(metadata.via.as_deref(), Some("prove_countdown"));
    }

    #[test]
    fn test_extract_trigger_mode_without_entries() {
        let attrs = parse_attrs(
            r#"
            #[doc = "trust_vc:trigger:mode=conservative"]
            fn foo() {}
            "#,
        );

        let metadata = extract_trigger_doc_metadata(&attrs)
            .expect("trigger metadata should parse")
            .expect("trigger metadata should exist");

        assert!(metadata.triggers.is_empty());
        assert_eq!(metadata.mode, Some(TriggerModeDoc::Conservative));
    }

    #[test]
    fn test_extract_trigger_indexed_entries_out_of_order() {
        let attrs = parse_attrs(
            r#"
            #[doc = "trust_vc:trigger:1:pattern=g(x)"]
            #[doc = "trust_vc:trigger:0:group=0"]
            #[doc = "trust_vc:trigger:1:group=2"]
            #[doc = "trust_vc:trigger:0:pattern=f(x)"]
            fn foo() {}
            "#,
        );

        let metadata = extract_trigger_doc_metadata(&attrs)
            .expect("trigger metadata should parse")
            .expect("trigger metadata should exist");

        assert_eq!(
            metadata.triggers,
            vec![
                TriggerDocEntry {
                    index: 0,
                    group: 0,
                    pattern: "f(x)".to_string(),
                },
                TriggerDocEntry {
                    index: 1,
                    group: 2,
                    pattern: "g(x)".to_string(),
                },
            ]
        );
        assert_eq!(metadata.mode, None);
    }

    #[test]
    fn test_extract_trigger_missing_pattern_fails() {
        let attrs = parse_attrs(
            r#"
            #[doc = "trust_vc:trigger:0:group=0"]
            fn foo() {}
            "#,
        );

        let message = extract_trigger_doc_metadata(&attrs)
            .expect_err("trigger without pattern should fail")
            .to_string();
        assert!(message.contains("missing pattern"), "got: {message}");
    }

    #[test]
    fn test_extract_broadcast_with_and_without_group() {
        let plain_attrs = parse_attrs(
            r#"
            #[doc = "trust_vc:broadcast"]
            fn foo() {}
            "#,
        );
        let plain_metadata = extract_broadcast_doc_metadata(&plain_attrs)
            .expect("broadcast metadata should parse")
            .expect("broadcast metadata should exist");
        assert!(plain_metadata.is_broadcast);
        assert_eq!(plain_metadata.group_name, None);

        let grouped_attrs = parse_attrs(
            r#"
            #[doc = "trust_vc:broadcast"]
            #[doc = "trust_vc:broadcast:group=arith"]
            fn foo() {}
            "#,
        );
        let grouped_metadata = extract_broadcast_doc_metadata(&grouped_attrs)
            .expect("grouped broadcast metadata should parse")
            .expect("grouped broadcast metadata should exist");
        assert!(grouped_metadata.is_broadcast);
        assert_eq!(grouped_metadata.group_name.as_deref(), Some("arith"));
    }

    #[test]
    fn test_unrelated_doc_comments_ignored() {
        let attrs = parse_attrs(
            r#"
            /// User-facing docs stay ignored.
            #[allow(dead_code)]
            fn foo() {}
            "#,
        );

        assert!(extract_decreases_doc_metadata(&attrs)
            .expect("decreases parse should succeed")
            .is_none());
        assert!(extract_broadcast_doc_metadata(&attrs)
            .expect("broadcast parse should succeed")
            .is_none());
        assert!(extract_trigger_doc_metadata(&attrs)
            .expect("trigger parse should succeed")
            .is_none());
    }
}
