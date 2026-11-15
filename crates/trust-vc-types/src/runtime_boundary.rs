// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Centralized runtime-boundary panic helpers for ghost/verification-only methods.
//!
//! All ghost types in trust-vc-types have methods that intentionally panic at runtime.
//! These methods are intercepted by the verifier and never execute in verified code.
//! This module centralizes those panic calls so `clippy::panic` is allowed in exactly
//! one place rather than scattered across every ghost type.

/// Panics with a message indicating a ghost/verification-only method was called at runtime.
///
/// This is the single `#[allow(clippy::panic)]` site for all ghost-boundary panics in
/// `trust-vc-types`. The panic is intentional: these methods must never execute at runtime
/// in verified code.
#[cold]
#[inline(never)]
#[track_caller]
#[allow(clippy::panic)]
pub(crate) fn ghost_runtime_panic(type_name: &str, member: &str) -> ! {
    // quality-audit: allow-panic
    panic!("{type_name}::{member} called at runtime \u{2014} only valid in verification context")
}
