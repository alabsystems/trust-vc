// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared output format enums used across the cargo-trust-vc CLI.
//!
//! These types were consolidated from duplicate definitions in
//! `verify_pipeline`, `proof_dashboard`, `emit_hints`, and
//! `optimization_pipeline` to provide a single source of truth.

use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// ReportFormat
// ---------------------------------------------------------------------------

/// Output format for verification and dashboard reports.
///
/// Used by both the verification pipeline (`verify_pipeline`) and the proof
/// dashboard (`proof_dashboard`).  Not every consumer supports every variant;
/// unsupported variants fall back to [`ReportFormat::Text`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ReportFormat {
    /// Plain text (default).
    #[default]
    Text,
    /// JSON.
    Json,
    /// Markdown.
    Markdown,
    /// Comma-separated values (dashboard only).
    Csv,
}

// ---------------------------------------------------------------------------
// HintFormat
// ---------------------------------------------------------------------------

/// Output format for optimization hints emitted from proven verification facts.
///
/// Used by both the emit-hints pipeline (`emit_hints`) and the end-to-end
/// optimization pipeline (`optimization_pipeline`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
#[non_exhaustive]
pub enum HintFormat {
    /// `// SAFETY: Verified by trust_vc -- <assertion>`
    #[default]
    RustComment,
    /// `#[trust_vc::verified(<kind>)]`
    CompilerDirective,
    /// Structured JSON object per hint.
    Json,
    /// `; !trust_vc.verified {kind: "...", proof: "..."}`
    Llvm,
    /// Emit all formats (useful for full-pipeline debugging).
    All,
}
