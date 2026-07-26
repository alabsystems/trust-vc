// trust-vc-oracle — Error types
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

/// Errors that can occur during oracle operations.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum OracleError {
    #[error("LLM backend exhausted after {attempts} attempts")]
    BackendExhausted { attempts: usize },

    #[error("LLM backend error: {message}")]
    BackendError { message: String },

    #[error("LLM backend '{backend}' is not available: {reason}")]
    BackendUnavailable { backend: String, reason: String },

    #[error("LLM backend timed out after {seconds}s")]
    BackendTimeout { seconds: u64 },

    #[error("annotation parse error: {message}")]
    AnnotationParse { message: String },

    #[error("verification infrastructure error: {0}")]
    Verification(#[from] trust_vc_core::TrustVcError),

    #[error("serialization error: {0}")]
    Serialization(#[from] serde_json::Error),

    #[error("source parse error: {message}")]
    SourceParse { message: String },
}
