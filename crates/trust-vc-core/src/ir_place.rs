//! Shared place IR for memory location reasoning.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `TrustVcPlace` models a memory location as a root variable plus a chain of
//! projections (field access, index). This is the shared abstraction that
//! replaces the private `MutRefPlace` in `mut_ref_proof.rs` and enables
//! first-class alias/disjointness reasoning.
//!
//! Originally part of #2515 (place-based reasoning).

use crate::ir::TrustVcType;
use crate::ir_expr::TrustVcExpr;

/// A memory location: root variable plus zero or more projections.
///
/// Examples:
/// - `counter` → root="counter", projections=[]
/// - `counter.count` → root="counter", projections=[Field("count", i32)]
/// - `outer.inner.count` → root="outer", projections=[Field("inner", Inner), Field("count", i32)]
/// - `s[i]` → root="s", projections=[Index(Var("i"), i32)]
/// - `state.entries[i]` → `root="state", projections=[Field("entries", Seq<i32>), Index(Var("i"), i32)]`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrustVcPlace {
    pub(crate) root_name: String,
    pub(crate) root_ty: TrustVcType,
    pub(crate) projections: Vec<PlaceProjection>,
    pub(crate) place_ty: TrustVcType,
}

/// A single projection step in a place path.
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(clippy::large_enum_variant)]
pub(crate) enum PlaceProjection {
    /// Named field access: `place.field_name`.
    Field {
        field_name: String,
        field_ty: TrustVcType,
    },
    /// Indexed access: `place[index]`.
    Index {
        index: TrustVcExpr,
        elem_ty: TrustVcType,
    },
}

impl TrustVcPlace {
    /// Creates a root-only place with no projections.
    #[must_use]
    pub(crate) fn root(name: impl Into<String>, ty: TrustVcType) -> Self {
        let ty_clone = ty.clone();
        Self {
            root_name: name.into(),
            root_ty: ty,
            projections: Vec::new(),
            place_ty: ty_clone,
        }
    }

    /// Appends a field projection and returns the extended place.
    #[must_use]
    pub(crate) fn field(mut self, field_name: impl Into<String>, field_ty: TrustVcType) -> Self {
        let ty = field_ty.clone();
        self.projections.push(PlaceProjection::Field {
            field_name: field_name.into(),
            field_ty,
        });
        self.place_ty = ty;
        self
    }

    /// Appends an index projection and returns the extended place.
    #[must_use]
    pub(crate) fn index(mut self, index_expr: TrustVcExpr, elem_ty: TrustVcType) -> Self {
        let ty = elem_ty.clone();
        self.projections.push(PlaceProjection::Index {
            index: index_expr,
            elem_ty,
        });
        self.place_ty = ty;
        self
    }

    /// Returns true if this place has no projections (is a bare root).
    #[must_use]
    #[cfg(test)]
    pub(crate) fn is_root(&self) -> bool {
        self.projections.is_empty()
    }

    /// Returns a new place with index expressions mapped through `f`.
    #[must_use]
    pub(crate) fn map_indices(&self, f: &dyn Fn(&TrustVcExpr) -> TrustVcExpr) -> Self {
        Self {
            root_name: self.root_name.clone(),
            root_ty: self.root_ty.clone(),
            projections: self
                .projections
                .iter()
                .map(|proj| match proj {
                    PlaceProjection::Index { index, elem_ty } => PlaceProjection::Index {
                        index: f(index),
                        elem_ty: elem_ty.clone(),
                    },
                    PlaceProjection::Field { .. } => proj.clone(),
                })
                .collect(),
            place_ty: self.place_ty.clone(),
        }
    }
}

/// Computes whether two places are statically disjoint.
///
/// Rules:
/// 1. Different roots → always disjoint (returns `BoolLit(true)`).
/// 2. Same root, first differing projection is a field mismatch → disjoint.
/// 3. Same root, first differing projection is an index mismatch → `i != j`.
/// 4. One place is a strict prefix of the other → NOT disjoint.
/// 5. Identical places → NOT disjoint.
#[must_use]
pub(crate) fn place_disjoint(left: &TrustVcPlace, right: &TrustVcPlace) -> TrustVcExpr {
    // Rule 1: different roots
    if left.root_name != right.root_name {
        return TrustVcExpr::BoolLit(true);
    }

    for (left_projection, right_projection) in left.projections.iter().zip(&right.projections) {
        match (left_projection, right_projection) {
            // Rule 2: field mismatch → unconditionally disjoint
            (
                PlaceProjection::Field { field_name: lf, .. },
                PlaceProjection::Field { field_name: rf, .. },
            ) => {
                if lf != rf {
                    return TrustVcExpr::BoolLit(true);
                }
            }
            // Rule 3: index mismatch → disjoint iff indices differ
            (
                PlaceProjection::Index { index: li, .. },
                PlaceProjection::Index { index: ri, .. },
            ) => {
                if li != ri {
                    return TrustVcExpr::Compare {
                        op: crate::ir_expr::CompareOp::Ne,
                        left: Box::new(li.clone()),
                        right: Box::new(ri.clone()),
                    };
                }
            }
            // Mixed field/index at same position → disjoint (different projection kinds)
            (PlaceProjection::Field { .. }, PlaceProjection::Index { .. })
            | (PlaceProjection::Index { .. }, PlaceProjection::Field { .. }) => {
                return TrustVcExpr::BoolLit(true);
            }
        }
    }

    // Rule 4 & 5: one is a prefix of the other, or identical → not disjoint
    TrustVcExpr::BoolLit(false)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::TrustVcType;

    fn i32_ty() -> TrustVcType {
        TrustVcType::Int { width: 32 }
    }

    fn seq_i32() -> TrustVcType {
        TrustVcType::Seq(Box::new(i32_ty()))
    }

    fn struct_ty(name: &str) -> TrustVcType {
        TrustVcType::Datatype {
            name: name.to_string(),
            variants: vec![],
        }
    }

    fn i32_var(name: &str) -> TrustVcExpr {
        TrustVcExpr::Var {
            name: name.to_string(),
            ty: i32_ty(),
        }
    }

    #[test]
    fn test_root_place() {
        let p = TrustVcPlace::root("x", i32_ty());
        assert_eq!(p.root_name, "x");
        assert!(p.is_root());
        assert_eq!(p.place_ty, i32_ty());
    }

    #[test]
    fn test_field_projection() {
        let p = TrustVcPlace::root("counter", struct_ty("Counter")).field("count", i32_ty());
        assert!(!p.is_root());
        assert_eq!(p.projections.len(), 1);
        assert_eq!(p.place_ty, i32_ty());
    }

    #[test]
    fn test_nested_field_projection() {
        let p = TrustVcPlace::root("outer", struct_ty("Outer"))
            .field("inner", struct_ty("Inner"))
            .field("count", i32_ty());
        assert_eq!(p.projections.len(), 2);
        assert_eq!(p.place_ty, i32_ty());
    }

    #[test]
    fn test_index_projection() {
        let p = TrustVcPlace::root("s", seq_i32()).index(i32_var("i"), i32_ty());
        assert_eq!(p.projections.len(), 1);
        assert_eq!(p.place_ty, i32_ty());
    }

    #[test]
    fn test_field_then_index() {
        let p = TrustVcPlace::root("state", struct_ty("State"))
            .field("entries", seq_i32())
            .index(i32_var("i"), i32_ty());
        assert_eq!(p.projections.len(), 2);
        assert_eq!(p.place_ty, i32_ty());
    }

    #[test]
    fn test_disjoint_different_roots() {
        let a = TrustVcPlace::root("x", i32_ty());
        let b = TrustVcPlace::root("y", i32_ty());
        assert_eq!(place_disjoint(&a, &b), TrustVcExpr::BoolLit(true));
    }

    #[test]
    fn test_disjoint_different_fields() {
        let a = TrustVcPlace::root("c", struct_ty("C")).field("count", i32_ty());
        let b = TrustVcPlace::root("c", struct_ty("C")).field("max", i32_ty());
        assert_eq!(place_disjoint(&a, &b), TrustVcExpr::BoolLit(true));
    }

    #[test]
    fn test_not_disjoint_same_place() {
        let a = TrustVcPlace::root("c", struct_ty("C")).field("count", i32_ty());
        let b = TrustVcPlace::root("c", struct_ty("C")).field("count", i32_ty());
        assert_eq!(place_disjoint(&a, &b), TrustVcExpr::BoolLit(false));
    }

    #[test]
    fn test_not_disjoint_prefix() {
        let a = TrustVcPlace::root("c", struct_ty("C"));
        let b = TrustVcPlace::root("c", struct_ty("C")).field("count", i32_ty());
        assert_eq!(place_disjoint(&a, &b), TrustVcExpr::BoolLit(false));
    }

    #[test]
    fn test_disjoint_index_different_vars() {
        let a = TrustVcPlace::root("s", seq_i32()).index(i32_var("i"), i32_ty());
        let b = TrustVcPlace::root("s", seq_i32()).index(i32_var("j"), i32_ty());
        let result = place_disjoint(&a, &b);
        assert!(
            matches!(
                result,
                TrustVcExpr::Compare {
                    op: crate::ir_expr::CompareOp::Ne,
                    ..
                }
            ),
            "expected i != j, got: {:?}",
            result
        );
    }

    #[test]
    fn test_not_disjoint_same_index() {
        let a = TrustVcPlace::root("s", seq_i32()).index(i32_var("i"), i32_ty());
        let b = TrustVcPlace::root("s", seq_i32()).index(i32_var("i"), i32_ty());
        assert_eq!(place_disjoint(&a, &b), TrustVcExpr::BoolLit(false));
    }

    #[test]
    fn test_clone_and_eq() {
        let p = TrustVcPlace::root("x", i32_ty()).field("a", i32_ty());
        let q = p.clone();
        assert_eq!(p, q);
    }
}
