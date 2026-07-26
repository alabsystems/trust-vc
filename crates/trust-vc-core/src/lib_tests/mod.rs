// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for trust-vc-core lib.rs expansion helpers.
//!
//! Split from a single flat `lib_tests.rs` file for code-quality (#2633).

use super::*;
use crate::proof_expand::has_decreases_metadata;
use quote::quote;

fn clear_expand_proof_registries() {
    crate::mode::clear_compile_time_mode_registry();
    // NOTE: do NOT clear the contract registry here — it is a global static
    // (OnceLock<Mutex<HashMap>>), not thread-local. Clearing it from parallel
    // tests races with contract_registry::tests, wiping their registered
    // contracts mid-assertion. Only 1 of 15 callers registers a contract, and
    // register() overwrites by name, so clearing is unnecessary.
}

mod attributes;
mod decreases_expand;
mod mode_validation;
mod proof_expand;
mod protocol_expand;
mod trait_expand;
