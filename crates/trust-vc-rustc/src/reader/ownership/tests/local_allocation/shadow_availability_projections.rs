// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Original projected places preserve disjointness, move checking and reset order.
use super::*;
use thir::{ExprId, ExprKind, Thir};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Case {
    TupleDisjoint,
    TupleSame,
    StructDisjoint,
    StructSame,
    FieldReset,
    FieldResetOrder,
    FieldSibling,
    WholeReset,
    WholeResetOrder,
    PartialMove,
    PartialMoveExec,
}
impl Case {
    pub(super) fn error(self) -> Option<&'static str> {
        match self {
            Self::TupleSame
            | Self::StructSame
            | Self::FieldResetOrder
            | Self::FieldSibling
            | Self::WholeResetOrder => Some("E0502"),
            Self::PartialMoveExec => Some("E0382"),
            _ => None,
        }
    }
}
pub(super) fn declarations(case: Case) -> &'static str {
    if matches!(case, Case::StructDisjoint | Case::StructSame) {
        "struct Pair { left: u64, right: u64 }\n"
    } else {
        ""
    }
}
pub(super) fn source(case: Case) -> (&'static str, &'static str) {
    match case {
        Case::TupleDisjoint => ("fn target(mut original: (u64, u64))",
            "let loan = &mut original.0; #[verifier::proof_block] { #[verus::internal(spec)] let observed = original.1; } *loan = 7;"),
        Case::TupleSame => ("fn target(mut original: (u64, u64))",
            "let loan = &mut original.0; #[verifier::proof_block] { #[verus::internal(spec)] let observed = original.0; } *loan = 7;"),
        Case::StructDisjoint => ("fn target(mut original: Pair)",
            "let loan = &mut original.left; #[verifier::proof_block] { #[verus::internal(spec)] let observed = original.right; } *loan = 7;"),
        Case::StructSame => ("fn target(mut original: Pair)",
            "let loan = &mut original.left; #[verifier::proof_block] { #[verus::internal(spec)] let observed = original.left; } *loan = 7;"),
        Case::FieldReset => ("fn target(mut first: u64, mut second: u64)",
            "let mut holder = (&mut first, 0u64); let p = &mut *holder.0; holder.0 = &mut second; let q = &mut *holder.0; *p = 1; *q = 2;"),
        Case::FieldResetOrder => ("fn target(mut first: u64, mut second: u64)",
            "let mut holder = (&mut first, 0u64); let p = &mut *holder.0; holder.0 = { #[verifier::proof_block] { #[verus::internal(spec)] let observed = *holder.0; } &mut second }; *p = 1;"),
        Case::FieldSibling => ("fn target(mut first: u64, mut second: u64, mut third: u64)",
            "let mut holder = (&mut first, &mut second); let p = &mut *holder.0; holder.1 = &mut third; #[verifier::proof_block] { #[verus::internal(spec)] let observed = *holder.0; } *p = 7;"),
        Case::WholeReset => ("fn target(mut first: u64, mut second: u64)",
            "let mut holder = (&mut first, 0u64); let p = &mut *holder.0; holder = (&mut second, 0u64); let q = &mut *holder.0; *p = 1; *q = 2;"),
        Case::WholeResetOrder => ("fn target(mut first: u64, mut second: u64)",
            "let mut holder = (&mut first, 0u64); let p = &mut *holder.0; holder = { #[verifier::proof_block] { #[verus::internal(spec)] let observed = *holder.0; } (&mut second, 0u64) }; *p = 1;"),
        Case::PartialMove => ("fn target<T>(original: (T, T))",
            "let kept = original.0; #[verifier::proof_block] { #[verus::internal(spec)] let observed = original.0; } kept; original.1;"),
        Case::PartialMoveExec => ("fn target<T>(original: (T, T))",
            "let kept = original.0; #[verifier::proof_block] { #[verus::internal(spec)] let observed = original.0; } original.0; kept; original.1;"),
    }
}

pub(super) fn check(case: Case, counts: Counts) {
    let expected = match case {
        Case::TupleDisjoint | Case::TupleSame | Case::StructDisjoint | Case::StructSame => {
            (1, 1, 0, 0)
        }
        Case::FieldReset => (0, 2, 1, 0),
        Case::FieldResetOrder | Case::FieldSibling => (1, 1, 1, 0),
        Case::WholeReset => (0, 2, 0, 1),
        Case::WholeResetOrder => (1, 1, 0, 1),
        Case::PartialMove | Case::PartialMoveExec => (1, 0, 0, 0),
    };
    assert_eq!(
        (
            counts.projected_reads,
            counts.projected_ties,
            counts.projected_resets,
            counts.aggregate_resets
        ),
        expected,
        "{case:?}"
    );
}

/// Compare the actual source and the actual newly-built helper argument place.
/// A root-only mirror or a swapped index cannot satisfy this occurrence check.
pub(super) fn fields(body: &Thir<'_>, source: ExprId, mirrored: ExprId) -> usize {
    match (&body[source].kind, &body[mirrored].kind) {
        (ExprKind::Scope { value, .. }, _) => fields(body, *value, mirrored),
        (_, ExprKind::Scope { value, .. }) => fields(body, source, *value),
        (
            ExprKind::Field {
                lhs,
                variant_index,
                name,
            },
            ExprKind::Field {
                lhs: target,
                variant_index: target_variant,
                name: target_name,
            },
        ) => {
            assert_eq!((variant_index, name), (target_variant, target_name));
            assert_eq!(body[source].ty, body[mirrored].ty);
            1 + fields(body, *lhs, *target)
        }
        (ExprKind::Deref { arg }, ExprKind::Deref { arg: target }) => fields(body, *arg, *target),
        (ExprKind::VarRef { .. }, ExprKind::VarRef { .. }) => 0,
        _ => panic!("the mirrored helper place changed the original projection shape"),
    }
}

#[test]
fn tuple_shadow_read_preserves_disjoint_field_borrow() {
    run(super::Case::Projected(Case::TupleDisjoint));
}
#[test]
fn tuple_shadow_read_rejects_same_field_before_later_mutation() {
    run(super::Case::Projected(Case::TupleSame));
}
#[test]
fn struct_shadow_read_preserves_disjoint_field_borrow() {
    run(super::Case::Projected(Case::StructDisjoint));
}
#[test]
fn struct_shadow_read_rejects_same_field_before_later_mutation() {
    run(super::Case::Projected(Case::StructSame));
}
#[test]
fn projected_reference_overwrite_resets_only_the_new_field_version() {
    run(super::Case::Projected(Case::FieldReset));
}
#[test]
fn projected_reference_reset_follows_assignment_rhs() {
    run(super::Case::Projected(Case::FieldResetOrder));
}
#[test]
fn projected_reference_reset_preserves_sibling_loan() {
    run(super::Case::Projected(Case::FieldSibling));
}
#[test]
fn whole_aggregate_overwrite_resets_the_new_reference_version() {
    run(super::Case::Projected(Case::WholeReset));
}
#[test]
fn whole_aggregate_reset_follows_assignment_rhs() {
    run(super::Case::Projected(Case::WholeResetOrder));
}
#[test]
fn projected_shadow_read_after_generic_partial_move_is_accepted() {
    run(super::Case::Projected(Case::PartialMove));
}
#[test]
fn projected_shadow_transform_retains_original_partial_move_error() {
    run(super::Case::Projected(Case::PartialMoveExec));
}
