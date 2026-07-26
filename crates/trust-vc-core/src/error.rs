//! Internal error types for the trust-vc-core verification pipeline.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

/// Canonical result alias for trust-vc-core bridge and infrastructure failures.
pub type TrustVcResult<T> = Result<T, TrustVcError>;

/// Typed infrastructure failures for parsing, lowering, and encoding.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum TrustVcError {
    #[error("{context}: {source}")]
    Parse {
        context: &'static str,
        #[source]
        source: syn::Error,
    },
    #[error("{context}: {source}")]
    Lowering {
        context: &'static str,
        #[source]
        source: crate::LoweringError,
    },
    #[error("{context}: {source}")]
    Io {
        context: &'static str,
        #[source]
        source: std::io::Error,
    },
    #[error("{context}: {detail}")]
    Encoding {
        context: &'static str,
        detail: String,
    },
    #[error("{context}: {detail}")]
    Internal {
        context: &'static str,
        detail: String,
    },
}

impl From<String> for TrustVcError {
    fn from(detail: String) -> Self {
        Self::Encoding {
            context: "encode expression",
            detail,
        }
    }
}

impl From<crate::LoweringError> for TrustVcError {
    fn from(source: crate::LoweringError) -> Self {
        Self::Lowering {
            context: "lower typed verification expression",
            source,
        }
    }
}

impl TrustVcError {
    /// Compatibility adapter for legacy public APIs that historically exposed
    /// only the raw encoding detail string, not the typed error context.
    pub(crate) fn into_legacy_string(self) -> String {
        match self {
            Self::Encoding { detail, .. } | Self::Internal { detail, .. } => detail,
            other => other.to_string(),
        }
    }
}
