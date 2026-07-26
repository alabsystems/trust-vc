//! Expression variant rename tests: Neg, Implies, Ite, Cast, FnCall,
//! SpecialArith, WrappingArith, Match, Choose, and Quantifier coverage.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Split from rewrite_variant_coverage/mod.rs (#2145).

use super::*;

mod binders_and_triggers;
mod match_patterns;
mod simple_variants;
