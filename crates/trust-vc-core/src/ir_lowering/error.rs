//! Shared lowering error surface.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use thiserror::Error;

/// Structured error type for lowering failures.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
#[non_exhaustive]
pub enum LoweringError {
    #[error("unsupported expression `{0}` in specification context — only pure, side-effect-free expressions are allowed in requires!/ensures!/invariant! blocks")]
    UnsupportedExpr(String),
    #[error("unsupported binary operator `{0}` — trust_vc supports arithmetic (+, -, *, /, %), comparison (==, !=, <, <=, >, >=), logical (&&, ||), and bitwise (&, |, ^, <<, >>) operators")]
    UnsupportedBinOp(String),
    #[error(
        "unsupported unary operator `{0}` — trust_vc supports negation (-) and logical not (!)"
    )]
    UnsupportedUnOp(String),
    #[error("unresolved variable `{0}` — ensure the variable is declared as a function parameter, let-binding, or quantifier-bound variable in the current scope")]
    UnresolvedVar(String),
    #[error("type inference failed: {0}")]
    TypeInference(String),
    #[error("invalid type `{0}` — expected a Rust primitive (u8..u128, i8..i128, bool, char), trust_vc ghost type (Seq, Set, Map, Multiset, Ghost, Tracked), or user-defined struct/enum")]
    InvalidType(String),
    #[error(
        "invalid literal `{0}` — trust_vc supports integer, boolean, character, and string literals"
    )]
    InvalidLiteral(String),
    /// An integer literal whose value lies outside the representable range of
    /// its declared/inferred integer type.
    ///
    /// The `Display` text reproduces upstream Verus's byte-exact diagnostic
    /// (`rust_to_vir_expr.rs::check_lit_int`): `integer literal out of range
    /// <IntRange>` — e.g. `integer literal out of range U(8)`. This is the
    /// diagnostic-parity surface for upstream #2778 `integers.rs`/`overflow.rs`
    /// `integer literal out of range` cases. The stored string is the complete
    /// upstream message, never a paraphrase, so substring assertions in the
    /// ported Verus suite match exactly.
    #[error("{0}")]
    IntegerLiteralOutOfRange(String),
    /// A `by(bit_vector)` proof references a value or type the bit-vector prover
    /// cannot model. The `Display` text reproduces upstream Verus's byte-exact
    /// diagnostics from `vir/src/bitvector_to_air.rs`:
    /// - `IntRange error: expected finite-width integer for bit-vector, got <Typ>`
    /// - ``error: bit_vector prover cannot handle type `<typ>` ``
    ///
    /// Diagnostic-parity surface for upstream #2778 `bitvector.rs`
    /// `not_supported_*_in_by_bit_vector` cases.
    #[error("{0}")]
    BitVectorUnsupportedType(String),
    /// A bit-shift whose shift amount is possibly negative (a signed RHS that is
    /// not provably non-negative). The `Display` text reproduces upstream
    /// Verus's byte-exact diagnostic from `vir/src/bitvector_to_air.rs`:
    /// `not supported: bit-shift with possibly negative shift (If you believe
    /// this value is always nonnegative, try casting the RHS to an unsigned
    /// type)`.
    ///
    /// Diagnostic-parity surface for upstream #2778 `overflow.rs`
    /// `spec_bitshift_negative` (`bit-shift with possibly negative shift`).
    #[error("{0}")]
    BitShiftPossiblyNegativeShift(String),
    #[error("unsupported method `{0}` — check that the receiver type supports this method in specification context; see trust-vc-types documentation for available ghost-type methods")]
    UnsupportedMethod(String),
    #[error("unsupported pattern `{0}` — trust_vc supports literal, identifier, wildcard (_), struct, and tuple-struct patterns in match expressions")]
    UnsupportedPattern(String),
    #[error("if expression requires else branch — all branches must produce a value in specification context")]
    MissingElseBranch,
    #[error("empty block expression — specification blocks must contain at least one expression")]
    EmptyBlock,
    #[error("invalid cast: {0}")]
    InvalidCast(String),
    #[error("expression depth exceeds internal limit of {limit} during {stage}")]
    ExpressionTooDeep { limit: usize, stage: &'static str },
}
