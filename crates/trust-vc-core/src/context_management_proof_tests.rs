//! Proof coverage tests for context_management.rs
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Covers previously untested production paths: try_clone_context error path,
//! try_take_context error path, get_context panic on borrow conflict,
//! ContextGuard save/restore lifecycle, clear_context graceful skip,
//! clear_all_thread_locals completeness, ContextAccessError formatting,
//! and RAII guard panic-unwind safety (memory_verification phase).
//!
//! Wiring: Worker must add to context_management.rs (after existing mod tests):
//!   #[cfg(test)]
//!   #[path = "context_management_proof_tests.rs"]
//!   mod proof_tests;
//!
//! Part of #949.

use super::*;

#[path = "context_management_access_tests.rs"]
mod access_tests;

#[path = "context_management_guard_tests.rs"]
mod guard_tests;
