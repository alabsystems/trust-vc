//! Shared arithmetic semantics for the encoder subsystem.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Root-cause fix for the ir_encoder soundness cluster (#2046).
//! Centralizes arithmetic mode, width, signedness resolution for
//! the IR encoder path.

use crate::ir::TrustVcType;

/// Per-operation arithmetic context resolved BEFORE encoding.
///
/// Instead of reading mutable global parser state (`quantifier_int_wrap`),
/// callers derive `ArithSemantics` from the expression and quantifier scope,
/// then pass it explicitly to encoding helpers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct ArithSemantics {
    pub width: u32,
    pub is_unsigned: bool,
}

/// Compute quantifier wrapping context from bound variable types.
///
/// Returns the widest integer width among all bound variables, with
/// signedness: unsigned only if ALL integer-typed bound vars are unsigned.
/// The widest width matches Rust's type promotion rules: narrower types
/// are promoted to wider ones before arithmetic. (#1794)
///
/// This replaces two divergent inline implementations:
/// - `quantifiers.rs:120-140` (legacy)
/// - `ir_encoder/advanced.rs:156-160` (IR: find_map/first, incorrect for #2036)
///
/// By centralizing, both paths use identical logic.
#[cfg(test)]
pub(super) fn resolve_quantifier_wrap(
    bound_vars: &[(String, TrustVcType)],
) -> Option<ArithSemantics> {
    let mut widest_width: Option<u32> = None;
    let mut all_unsigned = true;

    for (_, ty) in bound_vars {
        if let Some(w) = ty.bit_width() {
            if w > 0 {
                widest_width = Some(match widest_width {
                    Some(existing) => existing.max(w),
                    None => w,
                });
                if !ty.is_unsigned() {
                    all_unsigned = false;
                }
            }
        }
    }

    widest_width.map(|w| ArithSemantics {
        width: w,
        is_unsigned: all_unsigned,
    })
}

/// Convert `ArithSemantics` to the `(width, is_unsigned)` tuple used by
/// `wrap_int_with_ctx` and `int_mode_signed_div_rem_no_overflow_ctx`.
///
/// Provides a migration bridge: new code derives `ArithSemantics`, then
/// converts to the legacy tuple format expected by existing wrap helpers.
impl ArithSemantics {
    pub(super) fn as_wrap_tuple(self) -> (u32, bool) {
        (self.width, self.is_unsigned)
    }
}

/// Resolve wrapping context for a specific expression within a quantifier body.
///
/// Prefers the per-expression `TrustVcType` width when available (e.g., the
/// IR node carries a concrete `u32` type), falling back to the quantifier
/// scope's wrap context. This implements the "per-expression type > scope"
/// priority already present in `ir_encoder/arith.rs:260-264` but makes it
/// explicit and reusable.
pub(super) fn resolve_expr_wrap(
    ty: &TrustVcType,
    scope_wrap: Option<ArithSemantics>,
) -> Option<(u32, bool)> {
    ty.bit_width()
        .map(|w| (w, ty.is_unsigned()))
        .or_else(|| scope_wrap.map(|s| s.as_wrap_tuple()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_resolve_quantifier_wrap_single_i32() {
        let vars = vec![("x".to_string(), TrustVcType::Int { width: 32 })];
        let result = resolve_quantifier_wrap(&vars);
        assert_eq!(
            result,
            Some(ArithSemantics {
                width: 32,
                is_unsigned: false,
            })
        );
    }

    #[test]
    fn test_resolve_quantifier_wrap_single_u8() {
        let vars = vec![("x".to_string(), TrustVcType::Uint { width: 8 })];
        let result = resolve_quantifier_wrap(&vars);
        assert_eq!(
            result,
            Some(ArithSemantics {
                width: 8,
                is_unsigned: true,
            })
        );
    }

    #[test]
    fn test_resolve_quantifier_wrap_mixed_widths_uses_widest() {
        let vars = vec![
            ("x".to_string(), TrustVcType::Uint { width: 32 }),
            ("y".to_string(), TrustVcType::Uint { width: 8 }),
        ];
        let result = resolve_quantifier_wrap(&vars);
        assert_eq!(
            result,
            Some(ArithSemantics {
                width: 32,
                is_unsigned: true,
            })
        );
    }

    #[test]
    fn test_resolve_quantifier_wrap_mixed_signedness_defaults_to_signed() {
        let vars = vec![
            ("x".to_string(), TrustVcType::Uint { width: 32 }),
            ("y".to_string(), TrustVcType::Int { width: 32 }),
        ];
        let result = resolve_quantifier_wrap(&vars);
        assert_eq!(
            result,
            Some(ArithSemantics {
                width: 32,
                is_unsigned: false,
            })
        );
    }

    #[test]
    fn test_resolve_quantifier_wrap_no_integer_vars() {
        let vars = vec![("b".to_string(), TrustVcType::Bool)];
        let result = resolve_quantifier_wrap(&vars);
        assert_eq!(result, None);
    }

    #[test]
    fn test_resolve_quantifier_wrap_empty() {
        let vars: Vec<(String, TrustVcType)> = vec![];
        let result = resolve_quantifier_wrap(&vars);
        assert_eq!(result, None);
    }

    #[test]
    fn test_resolve_expr_wrap_prefers_expression_type() {
        let scope = Some(ArithSemantics {
            width: 8,
            is_unsigned: true,
        });
        let ty = TrustVcType::Int { width: 32 };
        let result = resolve_expr_wrap(&ty, scope);
        assert_eq!(result, Some((32, false)));
    }

    #[test]
    fn test_resolve_expr_wrap_falls_back_to_scope() {
        let scope = Some(ArithSemantics {
            width: 8,
            is_unsigned: true,
        });
        let ty = TrustVcType::Bool;
        let result = resolve_expr_wrap(&ty, scope);
        assert_eq!(result, Some((8, true)));
    }

    #[test]
    fn test_resolve_expr_wrap_none_when_both_missing() {
        let result = resolve_expr_wrap(&TrustVcType::Bool, None);
        assert_eq!(result, None);
    }
}
