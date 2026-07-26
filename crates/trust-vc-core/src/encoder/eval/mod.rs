//! Expression evaluation and encoding helpers for AYEncoder.
//!
//! Split from monolithic eval.rs into domain-specific submodules.
//! Part of #2522.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod condition;
mod const_eval;
mod function_registration;
mod substitution;

#[cfg(test)]
mod tests_condition;
#[cfg(test)]
mod tests_substitution;

// Re-export the substitute_inline_calls function for use by condition.rs
// and any other encoder submodule that needs it.
pub(super) use substitution::substitute_inline_calls;
pub(super) use substitution::substitute_vars_in_expr;
