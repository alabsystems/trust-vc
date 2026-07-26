//! Unit tests for verify_macro module — split by domain.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from monolithic `verify_macro_tests.rs` (2005 lines, 89 tests)
//! per #2145 Tier 1c. Each submodule stays under 500 lines.

mod assert_by_scope;
mod borrow_conflict;
mod broadcast_interleaving;
mod broadcast_quantifier_behavior;
mod broadcast_registration;
mod cleanup_coverage;
mod context_lifecycle;
mod measure_inference;
mod measure_inference_helpers;
mod source_extraction;
mod thread_local_state;
mod verification_workflow;
