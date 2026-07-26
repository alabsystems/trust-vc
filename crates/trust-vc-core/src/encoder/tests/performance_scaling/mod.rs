//! Performance scaling proofs — assert O(n) where claimed, detect O(n²) regressions.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Original monolith (680 lines, 10 tests) split for maintainability (#2145).
//! Re: #2160

use super::*;

/// Maximum allowed ratio between T(4N) and T(N).
/// Linear = ~4x, quadratic = ~16x. We use 12x as the threshold.
/// This detects quadratic blowup while tolerating measurement noise.
pub(super) const QUADRATIC_THRESHOLD: f64 = 12.0;

/// Minimum timing to avoid division by near-zero durations.
/// If T(N) < this, skip the ratio check (too fast to measure reliably).
pub(super) const MIN_MEASURABLE_US: u128 = 100;

mod component;
mod pipeline;
