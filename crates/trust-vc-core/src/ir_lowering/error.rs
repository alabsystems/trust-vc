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
    /// A body-extraction INVALIDATION POISON (`<name>__invalidated_<k>`, minted
    /// by `vc_extraction::body_extract` when a binding went through an effect
    /// it does not model) or UNMODELED SHADOW (`<name>__unmodeled_shadow_<k>`,
    /// a new binding of a name that already denotes a value, whose own value
    /// it does not model) is reported under its SOURCE name, with a note.
    #[error("unresolved variable `{}` — ensure the variable is declared as a function parameter, let-binding, or quantifier-bound variable in the current scope{}", unresolved_var_source_name(.0), unresolved_var_invalidation_note(.0))]
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

/// Marker infix of a body-extraction invalidation poison symbol.
const INVALIDATION_POISON_INFIX: &str = "__invalidated_";

/// Marker infix of a body-extraction unmodeled shadow symbol.
pub(crate) const UNMODELED_SHADOW_INFIX: &str = "__unmodeled_shadow_";

/// Which kind of never-declared body-extraction symbol a name is.
#[derive(Clone, Copy, PartialEq, Eq)]
enum UnresolvedKind {
    Plain,
    InvalidationPoison,
    UnmodeledShadow,
}

/// `(source name, kind)` for an unresolved variable name: a symbol
/// `<name><infix><digits>` maps back to `<name>`.
fn split_extraction_symbol(name: &str) -> (&str, UnresolvedKind) {
    for (infix, kind) in [
        (
            INVALIDATION_POISON_INFIX,
            UnresolvedKind::InvalidationPoison,
        ),
        (UNMODELED_SHADOW_INFIX, UnresolvedKind::UnmodeledShadow),
    ] {
        if let Some(index) = name.rfind(infix) {
            let suffix = &name[index + infix.len()..];
            if index > 0 && !suffix.is_empty() && suffix.bytes().all(|b| b.is_ascii_digit()) {
                return (&name[..index], kind);
            }
        }
    }
    (name, UnresolvedKind::Plain)
}

fn unresolved_var_source_name(name: &str) -> &str {
    split_extraction_symbol(name).0
}

fn unresolved_var_invalidation_note(name: &str) -> &'static str {
    match split_extraction_symbol(name).1 {
        UnresolvedKind::Plain => "",
        UnresolvedKind::InvalidationPoison => {
            " (its value after an assignment, method call or borrow that vc_extraction does not track is unknown, so this read fails closed)"
        }
        UnresolvedKind::UnmodeledShadow => {
            " (a pattern, closure parameter or `let` binds this name again with a value vc_extraction does not model, so this read fails closed instead of reading the outer binding of the same name)"
        }
    }
}

#[cfg(test)]
mod tests {
    use super::LoweringError;

    #[test]
    fn extraction_symbols_report_their_source_name() {
        let shadow = LoweringError::UnresolvedVar("v__unmodeled_shadow_3".into()).to_string();
        assert!(shadow.contains("unresolved variable `v`"), "{shadow}");
        assert!(shadow.contains("binds this name again"), "{shadow}");

        let poison = LoweringError::UnresolvedVar("x__invalidated_0".into()).to_string();
        assert!(poison.contains("unresolved variable `x`"), "{poison}");
        assert!(poison.contains("does not track"), "{poison}");

        let plain = LoweringError::UnresolvedVar("y__unmodeled_shadow_".into()).to_string();
        assert!(
            plain.contains("unresolved variable `y__unmodeled_shadow_`"),
            "{plain}"
        );
        assert!(!plain.contains("binds this name again"), "{plain}");
    }
}
