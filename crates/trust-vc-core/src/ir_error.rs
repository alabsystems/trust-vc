//! Public typed IR errors.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

/// Typed parsing failures for strict `TrustVcType` parsing.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum TrustVcTypeParseError {
    #[error("Unknown type: {input}")]
    UnknownType { input: String },
    #[error("Invalid {kind} type syntax: {input}")]
    InvalidSyntax { kind: &'static str, input: String },
    #[error("Empty type string")]
    EmptyTypeString,
}

/// Typed well-foundedness failures for datatype registration.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum DatatypeWellFoundednessError {
    #[error(
        "Recursive datatype '{datatype}' references other datatype carriers ({targets}). \
         Mutual recursive datatype cycles are not supported yet. Add an indirection \
         layer (Box<T>, Arc<T>, or Rc<T>) and validate the full cycle before encoding."
    )]
    MutualRecursionUnsupported { datatype: String, targets: String },
    #[error(
        "Recursive cycle in datatype '{datatype}' has no base case variant. Every variant \
         contains a recursive reference. Add a non-recursive variant (e.g., Nil, Leaf, \
         Empty) or wrap recursive fields in Box<T>, Arc<T>, or Rc<T>."
    )]
    NoBaseCase { datatype: String },
}
