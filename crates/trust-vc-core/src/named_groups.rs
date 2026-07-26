//! Manifest-backed named reveal/broadcast group support.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::error::TrustVcError;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::OnceLock;

#[doc(hidden)]
pub struct NamedRevealGroupDef {
    pub name: &'static str,
    pub members: &'static [&'static str],
}

#[doc(hidden)]
pub struct BroadcastFnGroupDef {
    pub function: &'static str,
    pub group: &'static str,
}

inventory::collect!(NamedRevealGroupDef);
inventory::collect!(BroadcastFnGroupDef);

struct NamedGroupManifest {
    reveal_groups: HashMap<&'static str, &'static [&'static str]>,
    broadcast_groups_by_fn: HashMap<&'static str, &'static str>,
}

static NAMED_GROUP_MANIFEST: OnceLock<Result<NamedGroupManifest, String>> = OnceLock::new();

fn manifest() -> &'static Result<NamedGroupManifest, String> {
    NAMED_GROUP_MANIFEST.get_or_init(build_manifest)
}

fn build_manifest() -> Result<NamedGroupManifest, String> {
    let mut reveal_entries: BTreeMap<&'static str, Vec<&'static [&'static str]>> = BTreeMap::new();
    for entry in inventory::iter::<NamedRevealGroupDef> {
        reveal_entries
            .entry(entry.name)
            .or_default()
            .push(entry.members);
    }

    if let Some((&name, _)) = reveal_entries.iter().find(|(_, defs)| defs.len() > 1) {
        return Err(format!("duplicate named reveal group `{name}`"));
    }

    let reveal_groups = reveal_entries
        .into_iter()
        .filter_map(|(name, mut defs)| defs.pop().map(|members| (name, members)))
        .collect();

    let mut broadcast_entries: BTreeMap<&'static str, BTreeSet<&'static str>> = BTreeMap::new();
    for entry in inventory::iter::<BroadcastFnGroupDef> {
        broadcast_entries
            .entry(entry.function)
            .or_default()
            .insert(entry.group);
    }

    if let Some((&function, groups)) = broadcast_entries
        .iter()
        .find(|(_, groups)| groups.len() > 1)
    {
        let groups = groups.iter().copied().collect::<Vec<_>>().join(", ");
        return Err(format!(
            "function `{function}` has conflicting broadcast_group registrations: {groups}"
        ));
    }

    let broadcast_groups_by_fn = broadcast_entries
        .into_iter()
        .filter_map(|(function, groups)| groups.into_iter().next().map(|group| (function, group)))
        .collect();

    Ok(NamedGroupManifest {
        reveal_groups,
        broadcast_groups_by_fn,
    })
}

fn manifest_error(detail: String) -> TrustVcError {
    TrustVcError::Internal {
        context: "named group manifest",
        detail,
    }
}

#[doc(hidden)]
pub fn push_reveal_or_group(name: &str) {
    if !crate::verify_macro::is_in_proof_mode() {
        return;
    }

    match manifest() {
        Ok(manifest) => {
            if let Some(members) = manifest.reveal_groups.get(name) {
                for member in *members {
                    crate::verify_macro::push_reveal(member);
                }
                return;
            }
        }
        Err(detail) => {
            crate::verification_bridge::register_collection_error(manifest_error(detail.clone()));
            return;
        }
    }

    crate::verify_macro::push_reveal(name);
}

#[doc(hidden)]
pub fn register_broadcast_use_or_group(name: &str) {
    if !crate::verify_macro::is_in_proof_mode() {
        return;
    }

    match manifest() {
        Ok(manifest) => {
            if let Some(members) = manifest.reveal_groups.get(name) {
                crate::broadcast_state::register_broadcast_use(name.to_string());
                for member in *members {
                    if let Some(group) = manifest.broadcast_groups_by_fn.get(member) {
                        crate::broadcast_state::register_broadcast_use((*group).to_string());
                    }
                }
                return;
            }
        }
        Err(detail) => {
            crate::verification_bridge::register_collection_error(manifest_error(detail.clone()));
            return;
        }
    }

    crate::broadcast_state::register_broadcast_use(name.to_string());
}
