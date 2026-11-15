// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SPEC ARITHMETIC IS MATHEMATICAL, and it is the same arithmetic on BOTH
//! SIDES OF A CALL.
//!
//! In Verus a `requires` clause is SPEC code, and spec-mode `+`, `-`, `*` and
//! the unary `-` on a fixed-width `uN`/`iN` are the operations on mathematical
//! integers: `z + 1` is `z + 1`, never `0`, and `-z` at `i32::MIN` is
//! `2147483648`, not `i32::MIN`. Wrapping is spelled explicitly
//! (`add`/`sub`/`mul`, `wrapping_add`, …). trust-vc lowered those operators to
//! fixed-width IR everywhere, so a legitimate Verus program refuted:
//!
//! ```text
//! #[trust_vc::requires(z + 1u32 > z)]
//! fn g(z: u32) { … }
//! fn f(w: u32) { g(w); }      // ← REFUTED at w = u32::MAX
//! ```
//!
//! and three more measured shapes: `requires(z + 1u32 >= 1u32)`;
//! `requires(m == n - 1u32)` then `assert_by_nonlinear!(n >= 1u32)` (refuted
//! at `m = 0, n = 0`); `requires(d == a + b + c)` then
//! `assert_by_nonlinear!(d >= a)` (refuted at `a = 1, b = 0, c = MAX, d = 0`).
//! Each is a theorem of Verus's spec semantics.
//!
//! # Why the repair has to be at the IR level, and on both sides
//!
//! The caller DISCHARGES a `requires` (`__call_requires_*`) and the callee
//! ASSUMES it (`precondition`). Repairing only the caller would complete an
//! end-to-end FALSE VERIFIED: the callee would still derive the fixed-width
//! boundary fact from a clause the caller proved over the integers. So the
//! rewrite runs at the single prepared-obligation boundary
//! ([`crate::prepared_context`]), where both roles are built, and it is keyed
//! on the CHANNEL rather than on the direction — see
//! [`is_requires_channel`].
//!
//! # Why this cannot reopen the cross-reading false-verify class
//!
//! `encoder::verification::arith_reading` drops or guards a fact whose
//! fixed-width arithmetic would be RE-READ by a solve running the other
//! universe. A `MathInt` node is not re-read by anything: `int` denotes the
//! same object in both universes, which is the whole point of writing specs in
//! `int`. So a rewritten clause is `CrossReading::Identical` and crosses
//! unchanged — not because the gate was relaxed, but because there is no
//! longer a second reading of it to disagree with.
//!
//! The rewrite is deliberately NOT applied to `assume!`, to a body `assert!`,
//! to `by(bit_vector)` or to an `ensures`: each of those is pinned, in both
//! directions, by `tests/one_reading_per_subterm.rs`, and each would need its
//! own matched pair of sites. A one-sided change to any of them is exactly the
//! false-verify shape this module exists to avoid.
//!
//! # Moving `assume!` — the named residual, with its measured price
//!
//! Adding `ObligationKind::Assume` to [`is_requires_channel`] is the repair
//! that the `decreases` capability cost is charged against (see
//! `encoder::verification::arith_reading`'s
//! `a_wrapping_model_fact_is_guarded_into_the_measure_lane`). It is NOT free.
//! Applied and measured by the round-6 review it recovers NINE of the ten red
//! `loop_decreases!` fixtures, BREAKS a tenth that passes today
//! (`loop_invariant_basic::test_loop_decreases_lexicographic_with_invariant`),
//! and reds the false-verify pin
//! `a_wrapping_body_assumption_does_not_make_the_nonlinear_lane_vacuous`,
//! which stops refuting and goes to a fail-closed `Unknown`/`VacuousTruth`.
//!
//! That last one is arguably CORRECT once an `assume!` is spec code —
//! `z + 1u32 == 0u32` has no solution over the integers, so reporting the
//! contradiction beats publishing a proof from it — but "arguably correct"
//! is precisely the state in which a false-verify pin must be RE-KEYED
//! deliberately, with its own before/after table, and never quietly flipped
//! by a capability fix. The precedent is this tree's own correction of record
//! at `encoder::tests::vacuous_truth::
//! test_a_fixed_width_assumption_is_not_re_read_as_an_int_contradiction`.

use crate::ir::{ArithOp, TrustVcExpr, TrustVcType};
use crate::vc::ObligationKind;

/// Is this obligation part of the `requires` CHANNEL — the clause the caller
/// proves and the callee assumes?
///
/// Both roles must answer `true` or the two sides of one call stop meaning the
/// same thing:
///
/// * `ObligationKind::Requires` — the contract clause itself; asserted in
///   call-site mode, assumed at body level (`vc::context::builders`).
/// * `precondition` — the attribute path's spelling of the callee's own
///   assumption (`vc_extraction::attr_extract`, `trait_contracts`).
/// * `__call_requires_*` — the caller's discharge obligation
///   (`vc_extraction::body_extract`).
pub(crate) fn is_requires_channel(kind: ObligationKind, name: &str) -> bool {
    matches!(kind, ObligationKind::Requires)
        || name == "precondition"
        || name.starts_with("__call_requires_")
}

/// Rewrite the fixed-width `+`, `-`, `*` of a SPEC expression to mathematical
/// integers.
///
/// Only the `Arith` node's own result type moves; operands keep the types they
/// were lowered with, and the encoder bridges them (`encode_arith` coerces a
/// `BitVec` operand of a `MathInt` operation with `bv2int`/`bv2int_signed`, and
/// `encode_compare` does the same at the comparison boundary). That keeps the
/// change to ONE field and leaves variable declarations, sorts and counterexample
/// rendering exactly as they were.
///
/// # The descent set is a whitelist, on purpose
///
/// Recursion stops at every construct whose encoding depends on its operand
/// being fixed-width SORTED — a cast (`(a + b) as u8`), a shift or bitwise
/// operator, an explicit `wrapping_*`, a call argument, a collection index. Those
/// keep today's reading. Widening the set is a separate, measured change: each
/// one is a place where an `Int`-sorted subterm would reach a `BitVec`-expecting
/// encoder, and the failure mode there is an encode error, not a wrong answer.
///
/// `/` and `%` stay fixed-width too: the two universes can disagree about the
/// ROUNDING of a negative dividend with nothing overflowing anywhere, so moving
/// them is not the same one-line change and is not needed by any measured shape.
pub(crate) fn to_math_int_spec_arith(expr: &TrustVcExpr) -> TrustVcExpr {
    match expr {
        TrustVcExpr::Arith {
            op: op @ (ArithOp::Add | ArithOp::Sub | ArithOp::Mul),
            left,
            right,
            ty,
        } => {
            let left = Box::new(to_math_int_spec_arith(left));
            let right = Box::new(to_math_int_spec_arith(right));
            let ty = if is_fixed_width(ty) {
                TrustVcType::MathInt
            } else {
                ty.clone()
            };
            TrustVcExpr::Arith {
                op: *op,
                left,
                right,
                ty,
            }
        }
        // A spec NEGATION is mathematical too, and it is NOT reached by the
        // `Arith` arm above: `TrustVcExpr::Neg` carries no `ty` field, so the
        // descent used to pass straight through it and the operand was
        // BV-negated (wrapping) before any bridge saw it. `iN::MIN` is the one
        // value at which the two readings of a negation disagree —
        // `-(i32::MIN)` is `2147483648` over the integers and `i32::MIN` in
        // two's complement — so `#[requires(-z >= 0i32)]` called with
        // `g(i32::MIN)` refuted a program Verus accepts, and the shape survived
        // even when the clause carried a rewritten `+ 0i32` next to it.
        //
        // Re-express the negation as the subtraction it is, at `MathInt`: the
        // `Arith` encoder already bridges a fixed-width operand of a `MathInt`
        // operation with `bv2int_signed`, which is the same machinery every
        // other spec operator here relies on. A negative LITERAL folds to its
        // own constant instead — `-128i8` lowers to `Neg(IntLit { value: 128,
        // ty: i8 })`, and that constant is the same object in both universes
        // (the rule 8870e317 established), so the bridge is not needed and the
        // value-preserving literal widening in `encode_int_lit` is not
        // provoked.
        TrustVcExpr::Neg(inner) => {
            let inner_ty = crate::ir_lowering::infer_expr_type(inner);
            if !is_fixed_width(&inner_ty) {
                return TrustVcExpr::Neg(Box::new(to_math_int_spec_arith(inner)));
            }
            if let TrustVcExpr::IntLit { value, .. } = inner.as_ref() {
                if let Some(negated) = value.checked_neg() {
                    return TrustVcExpr::IntLit {
                        value: negated,
                        ty: TrustVcType::MathInt,
                    };
                }
            }
            TrustVcExpr::Arith {
                op: ArithOp::Sub,
                left: Box::new(TrustVcExpr::IntLit {
                    value: 0,
                    ty: TrustVcType::MathInt,
                }),
                right: Box::new(to_math_int_spec_arith(inner)),
                ty: TrustVcType::MathInt,
            }
        }
        TrustVcExpr::Not(inner) => TrustVcExpr::Not(Box::new(to_math_int_spec_arith(inner))),
        TrustVcExpr::Compare { op, left, right } => {
            let rewritten_left = to_math_int_spec_arith(left);
            let rewritten_right = to_math_int_spec_arith(right);
            let left = negated_literal_at_fixed_width_peer(left, &rewritten_right)
                .unwrap_or(rewritten_left);
            let right =
                negated_literal_at_fixed_width_peer(right, &left).unwrap_or(rewritten_right);
            TrustVcExpr::Compare {
                op: *op,
                left: Box::new(left),
                right: Box::new(right),
            }
        }
        TrustVcExpr::Logic { op, left, right } => TrustVcExpr::Logic {
            op: *op,
            left: Box::new(to_math_int_spec_arith(left)),
            right: Box::new(to_math_int_spec_arith(right)),
        },
        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => TrustVcExpr::Implies {
            premise: Box::new(to_math_int_spec_arith(premise)),
            conclusion: Box::new(to_math_int_spec_arith(conclusion)),
        },
        TrustVcExpr::Quantifier {
            kind,
            bound_vars,
            body,
            triggers,
            trigger_inference_mode,
        } => TrustVcExpr::Quantifier {
            kind: *kind,
            bound_vars: bound_vars.clone(),
            body: Box::new(to_math_int_spec_arith(body)),
            // A trigger must keep the SHAPE of the term it matches: rewriting
            // the body without the triggers would leave a `BitVec`-typed
            // pattern that no longer occurs in the encoded body.
            triggers: triggers.as_ref().map(|groups| {
                groups
                    .iter()
                    .map(|group| group.iter().map(to_math_int_spec_arith).collect())
                    .collect()
            }),
            trigger_inference_mode: *trigger_inference_mode,
        },
        // Everything else keeps today's reading — see the descent note above.
        other => other.clone(),
    }
}

/// A negated literal compared with a fixed-width operand, as the constant at
/// that operand's type.
///
/// The negation arm folds `-c` to the `int` constant `-c`, and the encoder
/// then bridges the fixed-width peer with `bv2int` to compare it. When the
/// peer's type holds `-c`, `bv2int(p) OP -c` and `p OP (-c at p's type)` are
/// the same predicate for every comparison, because the peer's type fixes
/// both the width and the signedness the comparison is read in. The second
/// form keeps the comparison in one sort, so the solver does not have to
/// reason through the bridge. A peer that is not fixed-width, or whose type
/// cannot hold `-c` (`x == -1` with `x: u32`), keeps the `int` constant.
fn negated_literal_at_fixed_width_peer(
    side: &TrustVcExpr,
    rewritten_peer: &TrustVcExpr,
) -> Option<TrustVcExpr> {
    let TrustVcExpr::Neg(inner) = side else {
        return None;
    };
    let TrustVcExpr::IntLit { value, ty } = inner.as_ref() else {
        return None;
    };
    if !is_fixed_width(ty) {
        return None;
    }
    let negated = value.checked_neg()?;
    let peer_ty = crate::ir_lowering::infer_expr_type(rewritten_peer);
    if !is_fixed_width(&peer_ty)
        || crate::ir_lowering::type_holds_integer(&peer_ty, negated) != Some(true)
    {
        return None;
    }
    Some(TrustVcExpr::IntLit {
        value: negated,
        ty: peer_ty,
    })
}

/// Does this type have a width the two arithmetic readings disagree about?
///
/// `MathInt`/`Nat`/`Real` already mean the same thing in both, so a spec-`int`
/// clause is returned untouched.
fn is_fixed_width(ty: &TrustVcType) -> bool {
    matches!(ty, TrustVcType::Int { .. } | TrustVcType::Uint { .. })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::CompareOp;

    fn u32_ty() -> TrustVcType {
        TrustVcType::Uint { width: 32 }
    }

    fn var(name: &str) -> TrustVcExpr {
        TrustVcExpr::Var {
            name: name.to_string(),
            ty: u32_ty(),
        }
    }

    fn lit(value: i128) -> TrustVcExpr {
        TrustVcExpr::IntLit {
            value,
            ty: u32_ty(),
        }
    }

    fn add(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
        TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(left),
            right: Box::new(right),
            ty: u32_ty(),
        }
    }

    /// Both roles of one `requires` clause answer the SAME way — the property
    /// the whole module exists for.
    #[test]
    fn both_sides_of_the_call_are_the_same_channel() {
        assert!(is_requires_channel(ObligationKind::Assume, "precondition"));
        assert!(is_requires_channel(
            ObligationKind::Assert,
            "__call_requires_pp0_g_0_0"
        ));
        assert!(is_requires_channel(ObligationKind::Requires, "anything"));
    }

    /// LIAR TWIN: the channels that keep the fixed-width reading, each pinned
    /// in both directions by `tests/one_reading_per_subterm.rs`.
    #[test]
    fn the_other_channels_are_not_rewritten() {
        for (kind, name) in [
            (ObligationKind::Assume, "assumption_0"),
            (ObligationKind::Assert, "assertion_0"),
            (ObligationKind::Assert, "postcondition"),
            (ObligationKind::AssertBy, "assert_by_nonlinear_0"),
            (ObligationKind::Ensures, "ensures_0"),
            (ObligationKind::Assume, "__call_ensures_pp1_g_0_0"),
        ] {
            assert!(
                !is_requires_channel(kind, name),
                "{name} ({kind:?}) must keep the fixed-width reading"
            );
        }
    }

    /// `z + 1u32 > z` becomes a statement about integers.
    #[test]
    fn a_fixed_width_sum_becomes_math_int() {
        let expr = TrustVcExpr::Compare {
            op: CompareOp::Gt,
            left: Box::new(add(var("z"), lit(1))),
            right: Box::new(var("z")),
        };
        let TrustVcExpr::Compare { left, right, .. } = to_math_int_spec_arith(&expr) else {
            panic!("shape preserved");
        };
        let TrustVcExpr::Arith {
            ty, left: inner, ..
        } = *left
        else {
            panic!("still an Arith");
        };
        assert_eq!(ty, TrustVcType::MathInt);
        // The OPERANDS keep their widths; only the operation moved.
        assert_eq!(*inner, var("z"));
        assert_eq!(*right, var("z"));
    }

    /// LIAR TWIN: a bare comparison carries no arithmetic and is returned
    /// byte-identical, so the rewrite cannot be mistaken for "retype
    /// everything".
    #[test]
    fn an_arithmetic_free_clause_is_unchanged() {
        let expr = TrustVcExpr::Compare {
            op: CompareOp::Lt,
            left: Box::new(var("z")),
            right: Box::new(lit(100)),
        };
        assert_eq!(to_math_int_spec_arith(&expr), expr);
    }

    /// A shift keeps its width — the `Int` universe has no `bvshl` to agree
    /// with, and the descent stops before it.
    #[test]
    fn a_shift_keeps_its_fixed_width_reading() {
        let shifted = TrustVcExpr::SpecialArith {
            op: crate::ir::SpecialArithOp::Shl,
            left: Box::new(add(var("z"), lit(1))),
            right: Box::new(lit(1)),
            ty: u32_ty(),
        };
        assert_eq!(to_math_int_spec_arith(&shifted), shifted);
    }

    /// So does an explicit `wrapping_*`: wrapping is what the user ASKED for.
    #[test]
    fn an_explicit_wrapping_operation_keeps_its_width() {
        let wrapping = TrustVcExpr::WrappingArith {
            mode: crate::ir::WrappingMode::Wrapping,
            op: ArithOp::Add,
            left: Box::new(var("a")),
            right: Box::new(var("b")),
            ty: u32_ty(),
        };
        assert_eq!(to_math_int_spec_arith(&wrapping), wrapping);
    }

    /// And a cast: `(a + b) as u8` truncates whatever it is handed, and the
    /// cast encoder needs its operand BV-sorted.
    #[test]
    fn a_cast_stops_the_descent() {
        let cast = TrustVcExpr::Cast {
            expr: Box::new(add(var("a"), var("b"))),
            from_ty: u32_ty(),
            to_ty: TrustVcType::Uint { width: 8 },
        };
        assert_eq!(to_math_int_spec_arith(&cast), cast);
    }

    fn i32_ty() -> TrustVcType {
        TrustVcType::Int { width: 32 }
    }

    /// A spec `-z` on a fixed-width operand becomes `0 - z` over the integers.
    /// `Neg` carries no `ty`, so nothing but this arm can move it, and
    /// `-(i32::MIN)` is the one value at which the two readings disagree.
    #[test]
    fn a_fixed_width_negation_becomes_a_math_int_subtraction() {
        let expr = TrustVcExpr::Neg(Box::new(TrustVcExpr::Var {
            name: "z".to_string(),
            ty: i32_ty(),
        }));
        let TrustVcExpr::Arith {
            op,
            left,
            right,
            ty,
        } = to_math_int_spec_arith(&expr)
        else {
            panic!("a fixed-width negation must become an Arith node");
        };
        assert_eq!(op, ArithOp::Sub);
        assert_eq!(ty, TrustVcType::MathInt);
        assert_eq!(
            *left,
            TrustVcExpr::IntLit {
                value: 0,
                ty: TrustVcType::MathInt
            }
        );
        // The OPERAND keeps its width; the encoder bridges it.
        assert_eq!(
            *right,
            TrustVcExpr::Var {
                name: "z".to_string(),
                ty: i32_ty()
            }
        );
    }

    /// A negative LITERAL is the same constant in both universes, so it folds
    /// rather than going through the bridge — `-128i8` lowers to
    /// `Neg(IntLit { value: 128, ty: i8 })` and must mean `-128`, not the
    /// value-preserving widening `encode_int_lit` would otherwise force.
    #[test]
    fn a_negative_literal_folds_to_its_own_constant() {
        let expr = TrustVcExpr::Neg(Box::new(TrustVcExpr::IntLit {
            value: 128,
            ty: TrustVcType::Int { width: 8 },
        }));
        assert_eq!(
            to_math_int_spec_arith(&expr),
            TrustVcExpr::IntLit {
                value: -128,
                ty: TrustVcType::MathInt
            }
        );
    }

    fn i64_var(name: &str) -> TrustVcExpr {
        TrustVcExpr::Var {
            name: name.to_string(),
            ty: TrustVcType::Int { width: 64 },
        }
    }

    fn neg_lit(value: i128, ty: TrustVcType) -> TrustVcExpr {
        TrustVcExpr::Neg(Box::new(TrustVcExpr::IntLit { value, ty }))
    }

    fn compare_eq(left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
        TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// A negated literal compared with a fixed-width operand whose type holds
    /// it becomes the constant at that operand's type, on either side.
    #[test]
    fn a_negated_literal_takes_the_type_of_a_fixed_width_peer() {
        let i64_ty = TrustVcType::Int { width: 64 };
        let expected = compare_eq(
            i64_var("x"),
            TrustVcExpr::IntLit {
                value: -1,
                ty: i64_ty.clone(),
            },
        );
        assert_eq!(
            to_math_int_spec_arith(&compare_eq(i64_var("x"), neg_lit(1, i64_ty.clone()))),
            expected
        );
        let flipped = to_math_int_spec_arith(&compare_eq(neg_lit(1, i32_ty()), i64_var("x")));
        assert_eq!(
            flipped,
            compare_eq(
                TrustVcExpr::IntLit {
                    value: -1,
                    ty: i64_ty
                },
                i64_var("x")
            )
        );
    }

    /// LIAR TWIN: an unsigned peer cannot hold `-1`, so the constant stays
    /// `int` and `x == -1` stays false for every `x: u32`. Retyping it to
    /// `u32` would read it as `4294967295`.
    #[test]
    fn a_negated_literal_an_unsigned_peer_cannot_hold_stays_math_int() {
        let expr = compare_eq(var("x"), neg_lit(1, i32_ty()));
        assert_eq!(
            to_math_int_spec_arith(&expr),
            compare_eq(
                var("x"),
                TrustVcExpr::IntLit {
                    value: -1,
                    ty: TrustVcType::MathInt
                }
            )
        );
    }

    /// LIAR TWIN: a peer the rewrite moved to `int` (`z + 1u32`) keeps the
    /// `int` constant, so the comparison is still read over the integers.
    #[test]
    fn a_negated_literal_beside_math_int_arithmetic_stays_math_int() {
        let expr = compare_eq(add(var("z"), lit(1)), neg_lit(1, i32_ty()));
        let TrustVcExpr::Compare { right, .. } = to_math_int_spec_arith(&expr) else {
            panic!("shape preserved");
        };
        assert_eq!(
            *right,
            TrustVcExpr::IntLit {
                value: -1,
                ty: TrustVcType::MathInt
            }
        );
    }

    /// LIAR TWIN: a negation whose operand is already `int` means the same
    /// thing in both universes, so it is returned byte-identical — the rewrite
    /// is not "retype every negation".
    #[test]
    fn a_math_int_negation_is_left_alone() {
        let expr = TrustVcExpr::Neg(Box::new(TrustVcExpr::Var {
            name: "n".to_string(),
            ty: TrustVcType::MathInt,
        }));
        assert_eq!(to_math_int_spec_arith(&expr), expr);
    }

    /// LIAR TWIN: the descent set is unchanged, so a negation UNDER a cast —
    /// where the cast encoder needs its operand BV-sorted — keeps today's
    /// reading.
    #[test]
    fn a_negation_under_a_cast_keeps_its_fixed_width_reading() {
        let cast = TrustVcExpr::Cast {
            expr: Box::new(TrustVcExpr::Neg(Box::new(TrustVcExpr::Var {
                name: "z".to_string(),
                ty: i32_ty(),
            }))),
            from_ty: i32_ty(),
            to_ty: TrustVcType::Int { width: 8 },
        };
        assert_eq!(to_math_int_spec_arith(&cast), cast);
    }

    /// Arithmetic UNDER a quantifier moves with the body, and the triggers move
    /// with it so the pattern still matches the encoded term.
    #[test]
    fn a_quantified_body_and_its_triggers_move_together() {
        let body = TrustVcExpr::Compare {
            op: CompareOp::Ge,
            left: Box::new(add(var("a"), var("i"))),
            right: Box::new(var("a")),
        };
        let quantified = TrustVcExpr::Quantifier {
            kind: crate::ir::QuantifierKind::Forall,
            bound_vars: vec![("i".to_string(), u32_ty())],
            body: Box::new(body),
            triggers: Some(vec![vec![add(var("a"), var("i"))]]),
            trigger_inference_mode: None,
        };
        let TrustVcExpr::Quantifier { body, triggers, .. } = to_math_int_spec_arith(&quantified)
        else {
            panic!("shape preserved");
        };
        let TrustVcExpr::Compare { left, .. } = *body else {
            panic!("still a Compare");
        };
        assert!(matches!(
            *left,
            TrustVcExpr::Arith {
                ty: TrustVcType::MathInt,
                ..
            }
        ));
        let groups = triggers.expect("triggers preserved");
        assert!(matches!(
            groups[0][0],
            TrustVcExpr::Arith {
                ty: TrustVcType::MathInt,
                ..
            }
        ));
    }
}
