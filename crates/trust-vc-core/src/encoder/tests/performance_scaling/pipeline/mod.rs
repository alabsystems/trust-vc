//! Pipeline scaling tests: assertion count, variable count, assumption count,
//! collection push chain, and replace_vars_with_pre string rewriting.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from performance_scaling/mod.rs (#2145).

mod collection_stress;
mod context_scaling;
mod rewrite_scaling;
