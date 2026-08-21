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

/// True for the sorts whose values are mathematically unbounded and therefore
/// must NEVER be reduced modulo any bit width: Verus's `int` (`MathInt`),
/// `nat`, and spec-level `Real`.
///
/// This is the same set `ir_encoder/arith/int_arith.rs::is_math_integer` and
/// `ir_encoder/logic.rs`'s `is_math_typed` guard on, kept here so the wrap
/// resolver can decline instead of guessing.
fn is_unbounded_math_sort(ty: &TrustVcType) -> bool {
    matches!(
        ty,
        TrustVcType::MathInt | TrustVcType::Nat | TrustVcType::Real
    )
}

/// Resolve wrapping context for a specific expression within a quantifier body.
///
/// Prefers the per-expression `TrustVcType` width when available (e.g., the
/// IR node carries a concrete `u32` type), falling back to the quantifier
/// scope's wrap context. This implements the "per-expression type > scope"
/// priority already present in `ir_encoder/arith.rs:260-264` but makes it
/// explicit and reusable.
///
/// # The scope fallback must DECLINE for `int`/`nat`/`Real` (FV-C)
///
/// `TrustVcType::bit_width()` returns `None` for two distinct reasons, and
/// collapsing them was a cardinal false-verify:
///
/// * *"this expression has no width I could determine"* — the historical
///   motivation for the fallback: inside a quantifier body a fixed-width
///   operand may reach the encoder with an imprecise IR type, and the binder's
///   width is the best available reconstruction of the machine semantics.
/// * *"this expression is mathematically unbounded"* — `MathInt`, `Nat` and
///   `Real` have no width **by construction**. Adopting the binder's width
///   here does not reconstruct anything; it fabricates a modulus that the
///   source never had.
///
/// Because `QuantifierScope::wrap_semantics` is SCOPE-WIDE, the second case
/// silently reduced *every* `+`/`-`/`*` in a quantifier body mod 2^(binder
/// width) — including `int`-typed arithmetic that never mentions the binder.
/// `forall(|a: u8, b: u8| (a as int) + (b as int) <= 255)` therefore reported
/// `verified` even though `a == b == 200` refutes it, and the lie escaped
/// through `ensures`, so it crossed module boundaries.
///
/// Declining is the fail-closed answer: with no wrap context the operation
/// keeps faithful unbounded-integer semantics, which is exactly what `int` and
/// `nat` mean. The narrow reconstruction case is untouched — a genuinely
/// fixed-width expression still wraps, and so does an expression whose type is
/// merely unknown.
///
/// The two neighbours that already got this right and pin the intent:
/// `use_int_arithmetic` short-circuits to `None`
/// (`ir_encoder/arith/int_arith.rs`), and `QuantifierScope::from_bound_vars`
/// gates on the same `bit_width()`, so an `int`/`nat` BINDER contributes no
/// wrap. Only the expression-side test was missing.
pub(super) fn resolve_expr_wrap(
    ty: &TrustVcType,
    scope_wrap: Option<ArithSemantics>,
) -> Option<(u32, bool)> {
    if let Some(w) = ty.bit_width() {
        return Some((w, ty.is_unsigned()));
    }
    if is_unbounded_math_sort(ty) {
        return None;
    }
    scope_wrap.map(ArithSemantics::as_wrap_tuple)
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

    /// FV-C: `int`/`nat`/`Real` are unbounded BY CONSTRUCTION, so a `None`
    /// `bit_width()` here is not "width unknown" and must NOT be filled in
    /// from the enclosing quantifier binder.
    #[test]
    fn test_resolve_expr_wrap_declines_scope_for_unbounded_math_sorts() {
        let scope = Some(ArithSemantics {
            width: 8,
            is_unsigned: true,
        });
        for ty in [TrustVcType::MathInt, TrustVcType::Nat, TrustVcType::Real] {
            assert_eq!(
                resolve_expr_wrap(&ty, scope),
                None,
                "{ty:?} must never adopt the binder's modulus"
            );
        }
    }

    /// Narrowness pin for the same fix: a genuinely fixed-width expression
    /// still wraps, and a merely width-LESS non-math type still falls back.
    #[test]
    fn test_resolve_expr_wrap_still_wraps_fixed_width_under_scope() {
        let scope = Some(ArithSemantics {
            width: 8,
            is_unsigned: true,
        });
        assert_eq!(
            resolve_expr_wrap(&TrustVcType::Uint { width: 8 }, scope),
            Some((8, true))
        );
        assert_eq!(
            resolve_expr_wrap(&TrustVcType::Bool, scope),
            Some((8, true))
        );
    }
}
