//! Proof/test-mode bridge for ghost-only proof statements.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

mod control_flow;
mod helpers;
mod prophecy;
mod rewrite;

#[cfg(test)]
mod tests;

pub(crate) use rewrite::bridge_proof_statements;
