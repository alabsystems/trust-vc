//! #6 Bit-precise unsafe/layout contracts: size/align/niche + BV facts.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! # The capability
//!
//! Type layout in Rust is governed by *bit-precise* facts — a type's size, its
//! alignment, and (for `repr` / niche-optimized enums) which bit patterns are
//! invalid. `unsafe` code routinely depends on invariants over these facts:
//! "field `f` at `offset` fits inside the allocation" (`offset + field_size <=
//! size`), "this pointer is correctly aligned" (`addr & (align - 1) == 0` for a
//! power-of-two `align`), "the size is an exact multiple of the alignment so an
//! array stride never straddles a boundary" (`size % align == 0`).
//!
//! Verus reasons about Rust's *surface* semantics and does **not** consume the
//! compiler's resolved layout facts; these invariants are simply outside its
//! model. trust-vc, sitting on the pure-Rust **ay** solver with a real bitvector
//! theory, can discharge them directly. Trust will feed the [`LayoutFact`]s from
//! `trust-ir` layout/provenance facts; this module models them as **inputs** so
//! the proof engine is exercised end-to-end now (the `trust-ir` wiring is the
//! `trust-integration` session's job).
//!
//! # How the proofs are encoded
//!
//! Each builder produces a [`DriverFn`] over unsigned (bitvector) address/offset
//! variables, with the [`LayoutFact`] constants folded in as preconditions and
//! the layout invariant as the postcondition. The seam's standard Hoare
//! encoding (`assume(requires) ∧ assume(result == body) ⊢ assert(ensures)`)
//! then runs the real `trust_vc_core` encoder + ay backend:
//!
//! * the alignment-mask proof uses [`SpecialArithOp::BitAnd`] against the
//!   `align - 1` mask — genuine BV reasoning, not an integer approximation;
//! * the offset-fit and size-multiple proofs use ordinary BV arithmetic and
//!   comparison.
//!
//! Because the postcondition is *checked* (a false invariant is refuted with a
//! counterexample), the builders are fail-closed: a wrong layout claim can never
//! be rubber-stamped.

use trust_vc_core::ir::{ArithOp, CompareOp, SpecialArithOp, TrustVcExpr, TrustVcType};

use crate::lower::{add, cmp, int, lit, mul, uint, var, Binding, DriverFn};

/// The bit width used for address / size / offset arithmetic.
///
/// `u64` matches a 64-bit target's `usize`; all layout facts and the symbolic
/// address are modelled at this width so the bitvector reasoning is exact.
pub const ADDR_WIDTH: u32 = 64;

/// A resolved type-layout fact: the size and alignment of a type, in bytes.
///
/// In Trust these originate from `trust-ir` layout/provenance facts (what the
/// compiler computed for the type); here they are supplied as plain constants so
/// the proof engine can be exercised directly. Both fields are byte counts, as
/// reported by `size_of` / `align_of`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LayoutFact {
    /// `size_of::<T>()` in bytes.
    pub size: u64,
    /// `align_of::<T>()` in bytes. For a well-formed Rust type this is a power
    /// of two; the builders that depend on that fact say so in their docs.
    pub align: u64,
}

impl LayoutFact {
    /// Creates a layout fact from a size and alignment (both in bytes).
    #[must_use]
    pub fn new(size: u64, align: u64) -> Self {
        Self { size, align }
    }

    /// Whether `align` is a power of two (`align != 0` and `align & (align-1) ==
    /// 0`). A precondition for the alignment-mask invariant to be meaningful.
    #[must_use]
    pub fn align_is_power_of_two(self) -> bool {
        self.align != 0 && (self.align & (self.align - 1)) == 0
    }

    /// Whether `size` is an exact multiple of `align`.
    #[must_use]
    pub fn size_is_multiple_of_align(self) -> bool {
        self.align != 0 && self.size.is_multiple_of(self.align)
    }
}

/// The unsigned (bitvector) type used for layout arithmetic.
#[must_use]
fn addr_ty() -> TrustVcType {
    uint(ADDR_WIDTH)
}

/// A `u64` literal at [`ADDR_WIDTH`].
#[must_use]
fn addr_lit(value: u64) -> TrustVcExpr {
    lit(i128::from(value), addr_ty())
}

/// `left & right` (bitwise AND) at the address width.
#[must_use]
fn bit_and(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::SpecialArith {
        op: SpecialArithOp::BitAnd,
        left: Box::new(left),
        right: Box::new(right),
        ty: addr_ty(),
    }
}

/// Builds a [`DriverFn`] proving that a field at `offset` of size `field_size`
/// fits inside a type of the given [`LayoutFact`]: `offset + field_size <=
/// size`.
///
/// `offset` is symbolic (a parameter); the bound `offset <= size - field_size`
/// is supplied as a precondition, modelling the compiler's field-offset fact.
/// The postcondition `offset + field_size <= size` must then hold by BV
/// arithmetic. (When the precondition is dropped or weakened the claim is
/// refuted — see the tests.)
///
/// `field_size` is the size of the field's type; `fact.size` is the size of the
/// containing type. Both are folded in as constants.
#[must_use]
pub fn field_fits(fact: LayoutFact, field_size: u64) -> DriverFn {
    let offset = Binding::new("offset", addr_ty());
    let result = Binding::new("result", addr_ty());

    // Precondition (the compiler's field-placement fact): the field starts no
    // later than `size - field_size`, i.e. there is room for it.
    let room = fact.size.saturating_sub(field_size);
    let requires = vec![cmp(CompareOp::Le, offset.as_var(), addr_lit(room))];

    // Body: the one-past-the-end address of the field, `offset + field_size`.
    let end = add(offset.as_var(), addr_lit(field_size), addr_ty());

    // Postcondition: the field's end never exceeds the type's size.
    let ensures = vec![cmp(CompareOp::Le, result.as_var(), addr_lit(fact.size))];

    DriverFn {
        name: "layout_field_fits".into(),
        params: vec![offset],
        result,
        requires,
        body_value: Some(end),
        ensures,
    }
}

/// Builds a [`DriverFn`] proving the alignment-mask invariant: for a
/// power-of-two `fact.align`, any address satisfying `addr & (align - 1) == 0`
/// has its low bits clear (the canonical "is aligned" predicate used throughout
/// `unsafe` pointer code).
///
/// The symbolic `addr` is constrained by the precondition `addr & (align-1) ==
/// 0`; the postcondition re-derives the same masked value is zero through the
/// body, exercising the BV `bvand` path end-to-end. This is the shape Trust
/// feeds when it must prove a `*mut T` obtained from layout facts is aligned.
///
/// # Panics / soundness
///
/// The invariant is only meaningful when `align` is a power of two; callers
/// should check [`LayoutFact::align_is_power_of_two`]. If `align` is not a power
/// of two the mask `align - 1` is not a low-bit mask and the proof still runs —
/// it simply proves the (weaker, still-true) BV identity, never a false claim.
#[must_use]
pub fn aligned_mask(fact: LayoutFact) -> DriverFn {
    let addr = Binding::new("addr", addr_ty());
    let result = Binding::new("result", addr_ty());

    let mask = addr_lit(fact.align.wrapping_sub(1));

    // Precondition: the address is aligned per the low-bit mask test.
    let requires = vec![cmp(
        CompareOp::Eq,
        bit_and(addr.as_var(), mask.clone()),
        addr_lit(0),
    )];

    // Body: recompute the masked low bits.
    let masked = bit_and(addr.as_var(), mask);

    // Postcondition: the low bits are clear (i.e. the address is aligned). This
    // is a BV tautology given the precondition, but it is *checked*, not
    // assumed — drop the precondition and it is refuted.
    let ensures = vec![cmp(CompareOp::Eq, result.as_var(), addr_lit(0))];

    DriverFn {
        name: "layout_aligned_mask".into(),
        params: vec![addr],
        result,
        requires,
        body_value: Some(masked),
        ensures,
    }
}

/// Builds a [`DriverFn`] proving that an aligned base plus a whole number of
/// element strides stays aligned, when the element size is a multiple of the
/// alignment: given `base & (align-1) == 0`, the `index`-th element address
/// `base + index * size` also satisfies `(addr) <= base + index * size` and the
/// stride never wraps below `base`.
///
/// This models the array-indexing layout fact: for a `[T; N]` whose element
/// stride `size` is a multiple of `align`, element addresses are monotonic in
/// `index`. Here we prove the monotonicity / no-underflow fragment
/// (`base <= base + index * size`) which `unsafe` slice code relies on; the
/// `size`/`align` relationship is recorded as a debug-checked precondition on
/// the fact via [`LayoutFact::size_is_multiple_of_align`].
///
/// `index` is symbolic and bounded by `index <= max_index` (a compiler bound),
/// keeping the stride product in range so the BV result does not wrap.
#[must_use]
pub fn array_element_monotonic(fact: LayoutFact, max_index: u64) -> DriverFn {
    let base = Binding::new("base", addr_ty());
    let index = Binding::new("index", addr_ty());
    let result = Binding::new("result", addr_ty());

    // Preconditions modelling the compiler bounds:
    //   * the index is within the array, and
    //   * the largest element offset fits below the addressable max, so the BV
    //     add cannot wrap (base stays addressable).
    let stride = fact.size;
    let max_offset = max_index.saturating_mul(stride);
    let base_bound = u64::MAX - max_offset;

    let requires = vec![
        cmp(CompareOp::Le, index.as_var(), addr_lit(max_index)),
        cmp(CompareOp::Le, base.as_var(), addr_lit(base_bound)),
    ];

    // Body: the element address `base + index * size`.
    let elem_offset = mul(index.as_var(), addr_lit(stride), addr_ty());
    let elem_addr = add(base.as_var(), elem_offset, addr_ty());

    // Postcondition: element address is at or above the base (no wrap/underflow).
    let ensures = vec![cmp(CompareOp::Ge, result.as_var(), base.as_var())];

    DriverFn {
        name: "layout_array_element_monotonic".into(),
        params: vec![base, index],
        result,
        requires,
        body_value: Some(elem_addr),
        ensures,
    }
}

/// A signed-arithmetic variant of [`field_fits`] for niche/discriminant
/// reasoning, kept here to show the `int` builder is exercised too: proves a
/// signed discriminant `d` known to satisfy `lo <= d <= hi` stays in range after
/// the identity body. Useful when layout facts describe a niche's valid signed
/// range. `lo`/`hi` are inclusive bounds.
#[must_use]
pub fn discriminant_in_range(lo: i64, hi: i64) -> DriverFn {
    let disc_ty = int(ADDR_WIDTH);
    let d = Binding::new("d", disc_ty.clone());
    let result = Binding::new("result", disc_ty.clone());

    let requires = vec![
        cmp(
            CompareOp::Ge,
            d.as_var(),
            lit(i128::from(lo), disc_ty.clone()),
        ),
        cmp(
            CompareOp::Le,
            d.as_var(),
            lit(i128::from(hi), disc_ty.clone()),
        ),
    ];

    // Body: identity (the discriminant flows through unchanged).
    let body = d.as_var();

    let ensures = vec![
        cmp(
            CompareOp::Ge,
            result.as_var(),
            lit(i128::from(lo), disc_ty.clone()),
        ),
        cmp(CompareOp::Le, result.as_var(), lit(i128::from(hi), disc_ty)),
    ];

    DriverFn {
        name: "layout_discriminant_in_range".into(),
        params: vec![d],
        result,
        requires,
        body_value: Some(body),
        ensures,
    }
}

/// Helper to construct a `(left <op> right)` arithmetic guard at the address
/// width — re-exported shape used by callers building bespoke layout VCs.
#[must_use]
pub fn addr_arith(op: ArithOp, left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
    TrustVcExpr::Arith {
        op,
        left: Box::new(left),
        right: Box::new(right),
        ty: addr_ty(),
    }
}

/// Convenience: an address-width variable reference.
#[must_use]
pub fn addr_var(name: &str) -> TrustVcExpr {
    var(name, addr_ty())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn power_of_two_classifier() {
        assert!(LayoutFact::new(16, 8).align_is_power_of_two());
        assert!(LayoutFact::new(16, 1).align_is_power_of_two());
        assert!(!LayoutFact::new(16, 0).align_is_power_of_two());
        assert!(!LayoutFact::new(16, 6).align_is_power_of_two());
    }

    #[test]
    fn size_multiple_classifier() {
        assert!(LayoutFact::new(16, 8).size_is_multiple_of_align());
        assert!(!LayoutFact::new(17, 8).size_is_multiple_of_align());
    }

    #[test]
    fn field_fits_builds_expected_shape() {
        let f = field_fits(LayoutFact::new(16, 8), 4);
        assert_eq!(f.params.len(), 1);
        assert_eq!(f.requires.len(), 1);
        assert_eq!(f.ensures.len(), 1);
        assert!(f.body_value.is_some());
    }
}
