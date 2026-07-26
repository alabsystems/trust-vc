// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Error types for the merge bundle runner.

use thiserror::Error;

/// Errors produced by the merge bundle runner.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum RunnerError {
    #[error("unsupported bundle version {found}; runner requires version >= {min_executable}")]
    UnsupportedVersion { found: u32, min_executable: u32 },

    #[error("bundle missing required expression_format field")]
    MissingExpressionFormat,

    #[error("unsupported expression format; runner requires smt_lib2_term_v1")]
    UnsupportedExpressionFormat,

    #[error("unsupported sort in {context}: {sort_desc}")]
    UnsupportedSort { context: String, sort_desc: String },

    #[error("SMT-LIB2 parse error: {0}")]
    SmtParse(String),

    #[error("ay executor error: {0}")]
    Executor(String),

    #[error("bundle I/O error: {0}")]
    Io(#[from] std::io::Error),

    #[error("bundle JSON error: {0}")]
    Json(#[from] serde_json::Error),

    #[error("merge contract error: {0}")]
    Contract(#[from] trust_vc_merge_contract::MergeBundleError),
}
