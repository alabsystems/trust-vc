//! Termination proof runtime support.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Extracted from verify_macro.rs as part of #1740 (god module splitting).
//! Split into submodules as part of #2010:
//! - `measure_types`: Parsing, validation, and type inference helpers
//! - `measure_collect`: Measure collection and obligation construction
//! - `proof_entry`: Proof-entry verification plumbing
//!
//! Accesses VERIFICATION_CONTEXT via the `with_context` accessor in verify_macro.rs.

mod measure_collect;
pub(crate) mod measure_types;
mod proof_entry;

// Public API: runtime functions called by macro expansions
pub use measure_collect::{collect_decreases_measure, collect_loop_decreases_measure};
pub use proof_entry::{collect_decrease_obligation, verify_decreases, verify_proof_impl};

// Crate-internal API: used by marker_extraction
pub(crate) use measure_types::is_valid_measure_component;

// Crate-internal API: the shared loop-decrease obligation builder + its
// file-path binding/error types, consumed by the file-extraction funnel
// (`vc_extraction::body_extract`) so the file and runtime paths share ONE
// obligation-construction core. Part of the file-path `loop_decreases!` wiring.
pub(crate) use measure_collect::{build_loop_decreases_obligations, LoopDecreaseBinding};

// Test-only re-exports: used by verify_macro_tests.rs
#[cfg(test)]
pub(crate) use measure_types::{infer_measure_type, measure_type_bit_width, sanitize_measure_name};
