//! Unit tests for verification_bridge.rs.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from the monolithic `verification_bridge_tests.rs` as part of #2714.

use super::*;

fn with_registered_proofs_borrowed<F: FnOnce()>(f: F) {
    REGISTERED_PROOFS.with(|proofs| {
        let _borrow = proofs.borrow_mut();
        f();
    });
}

fn with_protocol_state_vars_borrowed<F: FnOnce()>(f: F) {
    PROTOCOL_STATE_VARS.with(|v| {
        let _borrow = v.borrow_mut();
        f();
    });
}

fn with_protocol_actions_borrowed<F: FnOnce()>(f: F) {
    PROTOCOL_ACTIONS.with(|v| {
        let _borrow = v.borrow_mut();
        f();
    });
}

fn with_protocol_invariants_borrowed<F: FnOnce()>(f: F) {
    PROTOCOL_INVARIANTS.with(|v| {
        let _borrow = v.borrow_mut();
        f();
    });
}

fn with_protocol_liveness_borrowed<F: FnOnce()>(f: F) {
    PROTOCOL_LIVENESS.with(|v| {
        let _borrow = v.borrow_mut();
        f();
    });
}

fn with_cleared_registrations<T>(f: impl FnOnce() -> T) -> T {
    clear_registrations();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    clear_registrations();
    match result {
        Ok(result) => result,
        Err(payload) => std::panic::resume_unwind(payload),
    }
}

#[cfg(feature = "ty")]
fn with_protocol_obligations_borrowed<F: FnOnce()>(f: F) {
    PROTOCOL_OBLIGATIONS.with(|v| {
        let _borrow = v.borrow_mut();
        f();
    });
}

fn register_protocol_components() {
    register_protocol_state_var("TestProto", "counter", "u64");
    register_protocol_action("TestProto", "increment", "counter' = counter + 1");
    register_protocol_invariant("TestProto", "counter_positive", "counter >= 0");
    register_protocol_liveness("TestProto", "progress", "counter > old_counter", "weak");
}

#[cfg(feature = "ty")]
fn test_protocol_obligation(name: &str) -> ProtocolObligation {
    ProtocolObligation {
        name: name.to_string(),
        spec: format!("---- MODULE {name} ----\n===="),
        config: String::new(),
    }
}

#[track_caller]
fn assert_protocol_component_counts(
    expected_state_vars: usize,
    expected_actions: usize,
    expected_invariants: usize,
    expected_liveness: usize,
) {
    let state_vars = PROTOCOL_STATE_VARS.with(|v| v.borrow().len());
    let actions = PROTOCOL_ACTIONS.with(|v| v.borrow().len());
    let invariants = PROTOCOL_INVARIANTS.with(|v| v.borrow().len());
    let liveness = PROTOCOL_LIVENESS.with(|v| v.borrow().len());
    assert_eq!(
        (state_vars, actions, invariants, liveness),
        (
            expected_state_vars,
            expected_actions,
            expected_invariants,
            expected_liveness,
        )
    );
}

#[path = "verification_bridge_pipeline_tests.rs"]
mod pipeline_tests;

#[path = "verification_bridge_collection_tests.rs"]
mod collection_tests;

#[path = "verification_bridge_protocol_tests.rs"]
mod protocol_tests;
