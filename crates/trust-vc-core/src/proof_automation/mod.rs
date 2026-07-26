//! proof_automation.rs — Proof automation strategies for common verification patterns.
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates Apache 2.0
//!
//! Tactics that automatically construct proofs for common patterns without
//! requiring user annotation. Supports arithmetic lemma automation, induction
//! scheme selection, and proof search.

mod expr;
mod search;
#[cfg(test)]
mod tests;
mod types;

pub(crate) use expr::*;
pub(crate) use search::*;
pub(crate) use types::*;
