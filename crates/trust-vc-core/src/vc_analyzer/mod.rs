//! Verification condition analysis — feature extraction, difficulty estimation,
//! pattern detection, and solver configuration recommendations.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This module examines VCs to extract structural features, estimate solving
//! difficulty, detect common proof-obligation patterns, and recommend solver
//! configurations. It is a companion to the `solver_strategy` module: while
//! `solver_strategy` owns the strategy types and selection logic, this module
//! owns the VC representation and analysis that feeds into strategy selection.
//!
//! All types are self-contained — no imports from sibling modules.

mod ast;
mod difficulty;
mod patterns;
mod profiles;
mod simplify;
#[cfg(test)]
mod tests;

pub use ast::*;
#[allow(unused_imports)]
pub use difficulty::*;
pub use patterns::*;
pub use profiles::*;
pub use simplify::*;
