//! Registry mutation helpers for the verification bridge.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[doc(hidden)]
pub fn register_proof(name: &str, obligations: Vec<ProofObligation>) {
    REGISTERED_PROOFS.with(|proofs| {
        proofs.borrow_mut().push(ProofRegistration {
            name: name.to_string(),
            obligations,
        });
    });
}

pub(crate) fn register_collection_error(err: TrustVcError) {
    COLLECTION_ERROR.with(|slot| {
        if let Ok(mut slot) = slot.try_borrow_mut() {
            if slot.is_none() {
                *slot = Some(err);
            }
        }
    });
}

#[doc(hidden)]
pub fn clear_registrations() {
    // Graceful skip on borrow conflict: panicking during cleanup aborts later clears.
    REGISTERED_PROOFS.with(|proofs| {
        if let Ok(mut guard) = proofs.try_borrow_mut() {
            guard.clear();
        }
    });
    #[cfg(feature = "ty")]
    PROTOCOL_OBLIGATIONS.with(|proto| {
        if let Ok(mut guard) = proto.try_borrow_mut() {
            guard.clear();
        }
    });
    PROTOCOL_STATE_VARS.with(|v| {
        if let Ok(mut guard) = v.try_borrow_mut() {
            guard.clear();
        }
    });
    PROTOCOL_ACTIONS.with(|v| {
        if let Ok(mut guard) = v.try_borrow_mut() {
            guard.clear();
        }
    });
    PROTOCOL_INVARIANTS.with(|v| {
        if let Ok(mut guard) = v.try_borrow_mut() {
            guard.clear();
        }
    });
    PROTOCOL_LIVENESS.with(|v| {
        if let Ok(mut guard) = v.try_borrow_mut() {
            guard.clear();
        }
    });
    COLLECTION_ERROR.with(|slot| {
        if let Ok(mut guard) = slot.try_borrow_mut() {
            let _ = guard.take();
        }
    });
    crate::trait_registry::clear_registered_traits();
}

#[cfg(feature = "ty")]
#[doc(hidden)]
pub fn register_protocol(obligation: ProtocolObligation) {
    PROTOCOL_OBLIGATIONS.with(|proto| {
        proto.borrow_mut().push(obligation);
    });
}

#[doc(hidden)]
pub fn register_protocol_state_var(protocol_name: &str, field_name: &str, rust_type: &str) {
    PROTOCOL_STATE_VARS.with(|vars| {
        vars.borrow_mut().push(ProtocolStateVarDef {
            protocol_name: protocol_name.to_string(),
            field_name: field_name.to_string(),
            rust_type: rust_type.to_string(),
        });
    });
}

#[doc(hidden)]
pub fn register_protocol_action(protocol_name: &str, name: &str, body: &str) {
    PROTOCOL_ACTIONS.with(|actions| {
        actions.borrow_mut().push(ProtocolActionDef {
            protocol_name: protocol_name.to_string(),
            name: name.to_string(),
            body: body.to_string(),
        });
    });
}

#[doc(hidden)]
pub fn register_protocol_invariant(protocol_name: &str, name: &str, expr: &str) {
    PROTOCOL_INVARIANTS.with(|invs| {
        invs.borrow_mut().push(ProtocolInvariantDef {
            protocol_name: protocol_name.to_string(),
            name: name.to_string(),
            expr: expr.to_string(),
        });
    });
}

#[doc(hidden)]
pub fn register_protocol_liveness(protocol_name: &str, name: &str, expr: &str, fairness: &str) {
    PROTOCOL_LIVENESS.with(|props| {
        props.borrow_mut().push(ProtocolLivenessDef {
            protocol_name: protocol_name.to_string(),
            name: name.to_string(),
            expr: expr.to_string(),
            fairness: fairness.to_string(),
        });
    });
}
