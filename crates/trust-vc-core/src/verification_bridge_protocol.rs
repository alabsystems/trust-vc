//! Protocol type definitions and assembly for the verification bridge.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

#[cfg(feature = "ty")]
use crate::error::TrustVcResult;

#[cfg(feature = "ty")]
use super::{
    borrowed_collection_error, collection_error, PROTOCOL_ACTIONS, PROTOCOL_INVARIANTS,
    PROTOCOL_LIVENESS, PROTOCOL_STATE_VARS,
};

#[doc(hidden)]
#[derive(Debug, Clone)]
#[cfg_attr(not(feature = "ty"), allow(dead_code))]
pub(crate) struct ProtocolStateVarDef {
    pub(crate) protocol_name: String,
    pub(crate) field_name: String,
    pub(crate) rust_type: String,
    /// The variable's value in the protocol's initial state.
    pub(crate) initial: ProtocolInitial,
}

/// Where a protocol state variable starts.
#[doc(hidden)]
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(not(feature = "ty"), allow(dead_code))]
pub(crate) enum ProtocolInitial {
    /// Registered by name (`register_protocol_state_var`): its type's zero,
    /// `0` or `false`.
    Zero,
    /// A `#[protocol]` field: its value in the struct's `Default::default()`,
    /// from each of two calls (`None` for a type the lane does not model).
    Default([Option<super::ProtocolValue>; 2]),
    /// A field of a `#[protocol]` struct that does not implement `Default`.
    NoDefault,
}

#[doc(hidden)]
#[derive(Debug, Clone)]
#[cfg_attr(not(feature = "ty"), allow(dead_code))]
pub(crate) struct ProtocolActionDef {
    pub(crate) protocol_name: String,
    pub(crate) name: String,
    pub(crate) body: String,
}

#[doc(hidden)]
#[derive(Debug, Clone)]
#[cfg_attr(not(feature = "ty"), allow(dead_code))]
pub(crate) struct ProtocolInvariantDef {
    pub(crate) protocol_name: String,
    pub(crate) name: String,
    pub(crate) expr: String,
}

#[doc(hidden)]
#[derive(Debug, Clone)]
#[cfg_attr(not(feature = "ty"), allow(dead_code))]
pub(crate) struct ProtocolLivenessDef {
    pub(crate) protocol_name: String,
    pub(crate) name: String,
    pub(crate) expr: String,
    pub(crate) fairness: String,
}

/// Assemble protocol components into ProtocolObligations.
///
/// Groups state variables by protocol name, then combines with
/// registered actions and invariants. Translates to TY spec text
/// via `protocol::translate`.
#[cfg(feature = "ty")]
pub(super) fn assemble_protocol_components(
    obligations: &mut Vec<crate::protocol::ProtocolObligation>,
) -> TrustVcResult<()> {
    use std::collections::BTreeSet;

    let state_vars = PROTOCOL_STATE_VARS.with(|v| {
        v.try_borrow()
            .map(|vars| vars.clone())
            .map_err(|_| borrowed_collection_error("protocol state variables"))
    })?;
    let actions = PROTOCOL_ACTIONS.with(|v| {
        v.try_borrow()
            .map(|actions| actions.clone())
            .map_err(|_| borrowed_collection_error("protocol actions"))
    })?;
    let invariants = PROTOCOL_INVARIANTS.with(|v| {
        v.try_borrow()
            .map(|invariants| invariants.clone())
            .map_err(|_| borrowed_collection_error("protocol invariants"))
    })?;
    let liveness = PROTOCOL_LIVENESS.with(|v| {
        v.try_borrow()
            .map(|liveness| liveness.clone())
            .map_err(|_| borrowed_collection_error("protocol liveness properties"))
    })?;

    let protocol_names = state_vars
        .iter()
        .map(|v| v.protocol_name.clone())
        .collect::<BTreeSet<_>>();

    for proto_name in actions
        .iter()
        .map(|a| &a.protocol_name)
        .chain(invariants.iter().map(|i| &i.protocol_name))
        .chain(liveness.iter().map(|l| &l.protocol_name))
    {
        if !protocol_names.contains(proto_name) {
            return Err(collection_error(format!(
                "protocol '{proto_name}' has registered actions, invariants, or liveness \
                 properties but no registered state variables"
            )));
        }
    }

    if let Some(prop) = liveness
        .iter()
        .find(|prop| !prop.fairness.trim().is_empty())
    {
        return Err(collection_error(format!(
            "protocol liveness fairness is not supported yet: '{}::{}' requested '{}'",
            prop.protocol_name, prop.name, prop.fairness
        )));
    }

    if protocol_names.is_empty() {
        return Ok(());
    }

    for proto_name in &protocol_names {
        let vars: Vec<_> = state_vars
            .iter()
            .filter(|v| &v.protocol_name == proto_name)
            .collect();
        let proto_actions: Vec<_> = actions
            .iter()
            .filter(|a| a.protocol_name == *proto_name)
            .cloned()
            .collect();
        let proto_invariants: Vec<_> = invariants
            .iter()
            .filter(|i| i.protocol_name == *proto_name)
            .cloned()
            .collect();
        let proto_liveness: Vec<_> = liveness
            .iter()
            .filter(|l| l.protocol_name == *proto_name)
            .cloned()
            .collect();

        let translated = crate::protocol::translate::translate_protocol(
            proto_name,
            &vars,
            &proto_actions,
            &proto_invariants,
            &proto_liveness,
        )?;

        obligations.push(crate::protocol::ProtocolObligation {
            name: proto_name.clone(),
            spec: translated.spec,
            config: translated.config,
            shape: Some(translated.shape),
        });
    }

    Ok(())
}
