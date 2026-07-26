//! Type helpers and result types for the ay encoder.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

#[cfg(not(feature = "native-seq"))]
use crate::ir::pointer_width;
use crate::ir::TrustVcType;
use ay_dpll::api::{ArraySort, Sort};

pub use crate::verify_result::VerifyResult;

fn float_sort(width: u32) -> Sort {
    match width {
        16 => Sort::FloatingPoint(5, 11),
        32 => Sort::FloatingPoint(8, 24),
        64 => Sort::FloatingPoint(11, 53),
        128 => Sort::FloatingPoint(15, 113),
        // Fail closed for unsupported widths instead of silently reusing Real.
        other => Sort::Uninterpreted(format!("Float{other}")),
    }
}

/// Converts a typed IR value into the encoder's backend sort.
pub(crate) fn sort_for_type(ty: &TrustVcType) -> Sort {
    match ty {
        TrustVcType::Unit => Sort::Uninterpreted("Unit".to_string()),
        TrustVcType::Bool => Sort::Bool,
        TrustVcType::Int { width } | TrustVcType::Uint { width } => Sort::bitvec(*width),
        TrustVcType::MathInt | TrustVcType::Nat => Sort::Int,
        TrustVcType::Real => Sort::Real,
        TrustVcType::Float { width } => float_sort(*width),
        #[cfg(feature = "native-seq")]
        TrustVcType::Seq(element) | TrustVcType::Array(element, _) => {
            Sort::seq(sort_for_type(element))
        }
        #[cfg(not(feature = "native-seq"))]
        TrustVcType::Seq(element) | TrustVcType::Array(element, _) => {
            Sort::Array(Box::new(ArraySort {
                index_sort: Sort::bitvec(pointer_width()),
                element_sort: sort_for_type(element),
            }))
        }
        TrustVcType::Set(element) => Sort::Array(Box::new(ArraySort {
            index_sort: sort_for_type(element),
            element_sort: Sort::Bool,
        })),
        TrustVcType::Multiset(element) => Sort::Array(Box::new(ArraySort {
            index_sort: sort_for_type(element),
            element_sort: Sort::Int,
        })),
        TrustVcType::Map(key, value) => Sort::Array(Box::new(ArraySort {
            index_sort: sort_for_type(key),
            element_sort: sort_for_type(value),
        })),
        TrustVcType::SpecFn(args, ret) => {
            Sort::Uninterpreted(format!("SpecFn{}To{}", args.len(), ret.to_type_string()))
        }
        // Native datatypes: ay registers the value sort as `Sort::Uninterpreted(name)`
        // (the term-level form of `Sort::Datatype`; see `Sort::as_term_sort`). Every
        // constructor/selector/tester term and datatype-typed variable shares it, and
        // `try_declare_datatype` populates ay's native datatype registry so the mbqi
        // tester-completion recognizers fire over symbolic datatype values.
        TrustVcType::Datatype { name, .. } | TrustVcType::RecursiveRef(name) => {
            crate::encoder::datatype::datatype_carrier_sort(name)
        }
        // Poly/TypeParam: type-erased polymorphic sort (#2053).
        TrustVcType::TypeParam(_) | TrustVcType::Poly => Sort::Uninterpreted("Poly".to_string()),
        // Opaque: retained for compatibility. verify_typed() rejects
        // contexts with Opaque variables (including nested) before this
        // translation is reached (#1926).
        TrustVcType::Opaque(_) => Sort::Int,
        // Char: Unicode scalar → 32-bit BV.
        TrustVcType::Char => Sort::bitvec(32),
        #[cfg(feature = "native-strings")]
        TrustVcType::StrSlice | TrustVcType::String => Sort::String,
        #[cfg(all(not(feature = "native-strings"), feature = "native-seq"))]
        TrustVcType::StrSlice | TrustVcType::String => Sort::seq(Sort::bitvec(32)),
        #[cfg(all(not(feature = "native-strings"), not(feature = "native-seq")))]
        TrustVcType::StrSlice | TrustVcType::String => Sort::Array(Box::new(ArraySort {
            index_sort: Sort::bitvec(pointer_width()),
            element_sort: Sort::bitvec(32),
        })),
    }
}

/// Returns the backend sort for use inside quantifier bodies.
pub(crate) fn quantifier_sort_for_type(ty: &TrustVcType) -> Sort {
    match ty {
        TrustVcType::Unit => Sort::Uninterpreted("Unit".to_string()),
        TrustVcType::Bool => Sort::Bool,
        TrustVcType::Int { .. }
        | TrustVcType::Uint { .. }
        | TrustVcType::MathInt
        | TrustVcType::Nat => Sort::Int,
        TrustVcType::Real => Sort::Real,
        TrustVcType::Float { width } => float_sort(*width),
        // Seq-bound variables keep the declared Seq sort so whole-Seq values can
        // flow into helper/trait UFs declared over `Seq<T>`. Widening only
        // applies to scalar bound variables, not to container element sorts
        // (#2690, recommends_trait_surface_blocker).
        TrustVcType::Seq(_) | TrustVcType::Array(_, _) => sort_for_type(ty),
        // Set-bound variables keep the declared Set sort so whole-Set values
        // can flow into helper/trait UFs declared over `Set<T>`. Scalar
        // keys used inside the body are coerced at collection-operation sites.
        TrustVcType::Set(_) => sort_for_type(ty),
        // Multiset-bound variables keep the declared Multiset sort. Counts are
        // Nat/Int-valued; operation-site coercions handle scalar element terms
        // where needed.
        TrustVcType::Multiset(_) => sort_for_type(ty),
        // Same rationale as Seq/Set: helper UFs are declared over the concrete
        // `Map<K, V>` sort, while key/value coercions handle int-mode bodies.
        TrustVcType::Map(_, _) => sort_for_type(ty),
        TrustVcType::SpecFn(args, ret) => {
            Sort::Uninterpreted(format!("SpecFn{}To{}", args.len(), ret.to_type_string()))
        }
        // Datatype-bound variables keep the native carrier sort so whole-datatype
        // values match ground constructor/selector terms (mirrors Seq/Set/Map).
        TrustVcType::Datatype { name, .. } | TrustVcType::RecursiveRef(name) => {
            crate::encoder::datatype::datatype_carrier_sort(name)
        }
        // Poly/TypeParam: type-erased polymorphic sort (#2053).
        TrustVcType::TypeParam(_) | TrustVcType::Poly => Sort::Uninterpreted("Poly".to_string()),
        TrustVcType::Opaque(_) => Sort::Int,
        // Char in quantifier bodies uses Int (consistent with Uint{32}) to avoid
        // sort mismatch with int-mode arithmetic. Fixes #2564.
        TrustVcType::Char => Sort::Int,
        #[cfg(feature = "native-strings")]
        TrustVcType::StrSlice | TrustVcType::String => Sort::String,
        #[cfg(all(not(feature = "native-strings"), feature = "native-seq"))]
        TrustVcType::StrSlice | TrustVcType::String => Sort::seq(Sort::bitvec(32)),
        #[cfg(all(not(feature = "native-strings"), not(feature = "native-seq")))]
        TrustVcType::StrSlice | TrustVcType::String => Sort::Array(Box::new(ArraySort {
            index_sort: Sort::Int,
            element_sort: Sort::Int,
        })),
    }
}

/// Infer the bit width for integer literals from variable type context.
///
/// Picks the most common integer width among declared variables. Breaks ties by
/// preferring wider width to avoid truncation. Falls back to 32 when no integer
/// variables are declared. Accepts an iterator of `TrustVcType` values to support both
/// AYEncoder (var_types only) and AstExpressionParser (var_types + local_var_types).
///
/// Uses a fixed-size array indexed by standard BV widths instead of allocating
/// a HashMap per call. Part of #2160.
pub(crate) fn infer_int_width_from_types<'a>(
    type_iter: impl Iterator<Item = &'a TrustVcType>,
) -> u32 {
    // Standard Rust integer BV widths. Covers i8/u8 through i128/u128 + Char(32).
    const WIDTHS: [u32; 5] = [8, 16, 32, 64, 128];
    let mut counts = [0usize; 5];

    for var_type in type_iter {
        if let Some(w) = var_type.bit_width() {
            // Linear scan of 5 elements is faster than HashMap lookup+insert.
            for i in 0..WIDTHS.len() {
                if WIDTHS[i] == w {
                    counts[i] += 1;
                    break;
                }
            }
        }
    }

    let mut best_width = 32u32;
    let mut best_count = 0usize;
    for i in 0..WIDTHS.len() {
        if counts[i] > best_count
            || (counts[i] == best_count && counts[i] > 0 && WIDTHS[i] > best_width)
        {
            best_count = counts[i];
            best_width = WIDTHS[i];
        }
    }
    best_width
}

/// Returns the minimum standard BV width (8, 16, 32, 64, 128) that can
/// represent `value` as either a signed or unsigned bitvector.
///
/// Used to widen literal BV constants that overflow the inferred context
/// width, preventing silent truncation (#1630).
/// Fixes #1872: was using signed-only check, over-widening unsigned-range values.
pub(crate) fn min_bv_width_for_value(value: i128) -> u32 {
    for &w in &[8u32, 16, 32, 64, 128] {
        if fits_in_bv(value, w) {
            return w;
        }
    }
    // Any i128 value fits in 128-bit (signed or unsigned), so this is unreachable.
    128
}

/// Returns the minimum standard BV width (8, 16, 32, 64, 128) that can
/// represent `value` in the *signed* two's-complement range
/// `[-(2^(w-1)), 2^(w-1) - 1]`.
///
/// Used by literal encoding to widen a *signed* literal that does not fit the
/// signed range of its inferred/declared width, rather than silently wrapping
/// it into a different (negative) value. A positive literal like `200` fits
/// the *unsigned* byte range but NOT the *signed* `i8` range, so encoding it
/// as a signed `BV8` yields `0xC8 = -56` and silently redefines the
/// constraint (casts-bitvec false-Verified cluster). Widening to the smallest
/// signed-correct width preserves the literal's mathematical value; later
/// width coercion sign-extends operands at comparison sites.
pub(crate) fn min_signed_bv_width_for_value(value: i128) -> u32 {
    for &w in &[8u32, 16, 32, 64, 128] {
        if fits_in_signed_bv(value, w) {
            return w;
        }
    }
    // Any i128 value fits in signed 128-bit, so this is unreachable.
    128
}

/// Returns the smallest standard BV width (8, 16, 32, 64, 128) where
/// `value` fits in the *signed* range `[-(2^(w-1)), 2^(w-1))`.
///
/// Returns true if `value` fits in a signed two's-complement bitvector
/// of the given width (i.e., within `[-(2^(w-1)), 2^(w-1) - 1]`).
///
/// Used by const-eval shortcuts to avoid folding comparisons where
/// i64 and BV semantics diverge due to wrap-around (fixes #1553).
/// Accepts i128 to handle u64 literals > i64::MAX without lossy cast (#1648).
pub(crate) fn fits_in_signed_bv(value: i128, width: u32) -> bool {
    if width == 0 {
        return false; // No value fits in a 0-width bitvector
    }
    if width >= 128 {
        return true;
    }
    let min = -(1i128 << (width - 1));
    let max = (1i128 << (width - 1)) - 1;
    value >= min && value <= max
}

/// Returns true if `value` can be represented in a bitvector of the given
/// width — either as signed or unsigned. This checks the full range
/// `[-(2^(w-1)), 2^w - 1]`, covering both two's-complement signed
/// and unsigned interpretations.
///
/// Used by literal parsing to decide if a value wraps within the target
/// BV width (e.g., 128 fits in BV8 as unsigned 128 / signed -128)
/// versus needing widening (e.g., 256 does not fit in BV8).
/// Fixes #1651/#1673: signed-only check rejected values like 128 in BV8
/// that are representable as unsigned, causing incorrect widening.
/// Accepts i128 to handle u64 literals > i64::MAX without lossy cast (#1648).
pub(crate) fn fits_in_bv(value: i128, width: u32) -> bool {
    if width == 0 {
        return false;
    }
    if width >= 128 {
        return true;
    }
    // Signed range: [-(2^(w-1)), 2^(w-1) - 1]
    let signed_min = -(1i128 << (width - 1));
    let signed_max = (1i128 << (width - 1)) - 1;
    if value >= signed_min && value <= signed_max {
        return true;
    }
    // Unsigned range: [0, 2^w - 1]
    if value >= 0 {
        let unsigned_max = (1u128 << width) - 1;
        return (value as u128) <= unsigned_max;
    }
    false
}
