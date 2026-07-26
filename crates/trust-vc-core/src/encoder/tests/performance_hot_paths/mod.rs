//! Additional hot-path scaling proofs for pre-solver encoder work.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `performance_proof_audit.rs` already covers the main verification loop plus
//! ground-pool registration/convergence. This module keeps the remaining
//! pre-solver hot-path scaling checks split out so the parent file stays under
//! the line-limit policy.
//!
//! Original monolith (524 lines, 7 tests) split for maintainability (#2145).

use super::*;

/// Maximum allowed ratio between T(4N) and T(N).
/// Linear = ~4x, quadratic = ~16x. We use 12x as the threshold.
pub(super) const QUADRATIC_THRESHOLD: f64 = 12.0;

/// Minimum timing to avoid division by near-zero durations.
pub(super) const MIN_MEASURABLE_US: u128 = 100;

mod cross_product_scaling;
mod ground_flush_and_rename;
mod trigger_and_axiom;
