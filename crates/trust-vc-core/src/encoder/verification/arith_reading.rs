// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! THE READING GATE: one subterm, one reading of its arithmetic.
//!
//! trust-vc solves different obligations in two different arithmetic
//! universes, and it uses the SAME term for a fixed-width subterm in both:
//!
//! * **fixed width** — every `uN`/`iN` variable is an ay `BitVec(N)` and
//!   `y + 1u32` WRAPS. This is the reading of the default lane, of
//!   `by(bit_vector)` and of every exec obligation.
//! * **math int** — `by(nonlinear_arith)` (so ay's integer theory can handle
//!   `*`, `/`, `%` symbolically) and the `decreases` measure lane declare those
//!   same variables as ay `Int`, where `y + 1u32` is LOSSLESS.
//!
//! A fact established under one reading was silently ASSERTED into a solve
//! running the other. At a boundary value the two readings CONTRADICT, so the
//! hypothesis set went unsatisfiable and every goal after it verified
//! vacuously. Measured before this gate, all eight VERIFIED:
//!
//! ```text
//! fn f(y: u32) {
//!     trust_vc::assume!(y == 0xffff_ffffu32);
//!     trust_vc::assert_by_nonlinear!(y + 1u32 > y);   // math-int TRUE
//!     trust_vc::assert!(1u32 == 2u32);                // ← VERIFIED
//! }
//! ```
//!
//! and the same shape with `-` at zero, `*` past the top bit, `u8`/`u32`/`u64`,
//! `i32` at `MAX`, with the false conclusion as a `postcondition` instead of a
//! body assert, and as a directly contradictory PAIR in one function
//! (`assert_by_nonlinear!(y + 1u32 > y)` beside
//! `assert_by_bit_vector!(y + 1u32 == 0u32)`).
//!
//! The gate is the obvious one and it is strictly fail-closed: a fact crosses
//! from one reading into the other ONLY when nothing in it is read differently
//! by the two. Otherwise it is DROPPED — dropping hypotheses can only make a
//! goal harder, so this can never turn a refutation into a `Verified`.

use std::collections::HashSet;

use crate::ir::{ArithOp, TrustVcExpr, TrustVcType};
use crate::ir_expr_traversal::{
    expr_references_any_name, walk_expr, walk_expr_scoped, ScopeAwareTrustVcExprVisitor,
    TrustVcExprVisitor,
};
use crate::prepared_context::PreparedObligation;

/// Which arithmetic universe a solve, or the proof of a fact, runs in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::encoder) enum ArithReading {
    /// `uN`/`iN` are `BitVec(N)`; arithmetic wraps.
    FixedWidth,
    /// `uN`/`iN` are unbounded `Int`; arithmetic is lossless.
    MathInt,
}

/// The reading an encoder built with this `use_int_for_measures` flag gives.
///
/// That flag is the actual sort selector in `setup_from_prepared_with_logic`,
/// so it — not the obligation's `solver_mode` — is what decides how the facts
/// this encoder is about to be handed will be READ. The `by(nonlinear_arith)`
/// lane, the `decreases`/measure lane and the int-mode timeout retry all reach
/// the same place through it.
pub(in crate::encoder) fn encoder_reading(use_int_for_measures: bool) -> ArithReading {
    if use_int_for_measures {
        ArithReading::MathInt
    } else {
        ArithReading::FixedWidth
    }
}

/// The reading a fact was ESTABLISHED under.
///
/// Mirrors `assertion::use_int_for_measures`: an obligation carrying the
/// `by(nonlinear_arith)` hint, and a measure obligation, are solved in the
/// `Int` universe. Everything else — a `requires`, an `assume!`, a
/// `by(bit_vector)` conclusion, a plain body assert, a loop invariant — was
/// established in the fixed-width one.
pub(in crate::encoder) fn fact_reading(fact: &PreparedObligation) -> ArithReading {
    let int_mode = fact
        .solver_mode
        .is_some_and(|mode| mode == crate::vc::SolverMode::NonlinearArith)
        || matches!(
            fact.kind,
            crate::vc::ObligationKind::MeasureNonNegative
                | crate::vc::ObligationKind::MeasureDecreases
        );
    encoder_reading(int_mode)
}

/// Is this a fixed-width integer type — one whose arithmetic the two readings
/// disagree about?
///
/// `MathInt`/`Nat`/`Real` are the SAME in both universes, so a spec-only
/// `int`/`nat` fact crosses freely; that is the whole point of writing specs in
/// `int`.
fn width_bearing(ty: &TrustVcType) -> bool {
    matches!(ty, TrustVcType::Int { .. } | TrustVcType::Uint { .. })
}

/// Does this expression contain a subterm the two readings evaluate
/// DIFFERENTLY?
///
/// Deliberately over-approximates, because over-approximating only drops more
/// facts:
///
/// * `+ - * / %` and unary `-` at a fixed width — wrapping vs lossless, and for
///   `/`/`%` the rounding of a negative dividend as well;
/// * every shift and bitwise operator at a fixed width — the `Int` universe has
///   no native `bvand`/`bvshl`, so these do not even denote the same function;
/// * a `Cast` touching a fixed width — truncation is invisible to `Int`;
/// * `WrappingArith` — wrapping/checked/saturating are width-defined outright.
///
/// It does NOT stop at a quantifier: `forall|i: u32| i + 1u32 > i` is read two
/// ways exactly like its ground instance.
/// How a fact's fixed-width content survives a change of reading.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::encoder) enum CrossReading {
    /// Nothing in it is read differently — it crosses unchanged.
    Identical,
    /// Every differing subterm is fixed-width `+`, `-`, `*` or a wrapping
    /// unary `-`. These agree with the unbounded reading EXACTLY WHEN they do
    /// not overflow, so the fact crosses GUARDED by its own no-overflow
    /// predicates.
    GuardableAdditive,
    /// Something in it has no such equivalence to appeal to — a shift, a
    /// bitwise operator (the `Int` universe has no `bvand` to agree with), a
    /// cast across a width, signed `/`/`%` (whose ROUNDING differs from the
    /// integer theory's even when nothing overflows), or an explicit
    /// wrapping/checked/saturating call. The fact is dropped.
    Unguardable,
}

/// Classify what happens to `expr` when it is re-read in the other universe.
pub(in crate::encoder) fn classify_cross_reading(expr: &TrustVcExpr) -> CrossReading {
    struct V {
        guardable: bool,
        unguardable: bool,
    }
    impl V {
        fn charge_guardable(&mut self) {
            self.guardable = true;
        }
        fn charge_unguardable(&mut self) {
            self.unguardable = true;
        }
    }
    impl TrustVcExprVisitor for V {
        fn visit_expr(&mut self, expr: &TrustVcExpr) {
            if self.unguardable {
                return;
            }
            match expr {
                // `+ - *` at a fixed width: equal to the lossless reading
                // exactly when they do not overflow, which is a predicate the
                // encoder already knows how to emit.
                TrustVcExpr::Arith {
                    op: ArithOp::Add | ArithOp::Sub | ArithOp::Mul,
                    ty,
                    ..
                } if width_bearing(ty) => {
                    self.charge_guardable();
                    walk_expr(self, expr);
                }
                // `/` and `%`: the two universes can disagree on ROUNDING with
                // no overflow anywhere, so there is no no-overflow predicate
                // that makes them equal.
                TrustVcExpr::Arith { ty, .. } if width_bearing(ty) => self.charge_unguardable(),
                TrustVcExpr::SpecialArith { ty, .. } if width_bearing(ty) => {
                    self.charge_unguardable()
                }
                TrustVcExpr::Cast { from_ty, to_ty, .. }
                    if width_bearing(from_ty) || width_bearing(to_ty) =>
                {
                    self.charge_unguardable()
                }
                TrustVcExpr::WrappingArith { .. } => self.charge_unguardable(),
                TrustVcExpr::Neg(inner) => match inner.as_ref() {
                    // `-K` for a LITERAL is the same constant in both
                    // universes; the only fixed-width negation that wraps is
                    // the one whose magnitude is `|iN::MIN|`. Charging every
                    // negative literal dropped a bare `assume!(a >= -100)` out
                    // of the nonlinear lane and over-rejected the legitimate
                    // `a * b >= -10000` that those bounds entail — measured,
                    // `encoder::tests::regression_overflow::
                    // overflow_i32_mul_small_safe`.
                    TrustVcExpr::IntLit { value, ty } => {
                        if literal_negation_wraps(*value, ty) {
                            self.charge_guardable();
                        }
                    }
                    other => {
                        if expr_type_is_width_bearing(other) {
                            self.charge_guardable();
                        }
                        walk_expr(self, expr);
                    }
                },
                _ => walk_expr(self, expr),
            }
        }
    }
    let mut v = V {
        guardable: false,
        unguardable: false,
    };
    v.visit_expr(expr);
    if v.unguardable {
        CrossReading::Unguardable
    } else if v.guardable {
        CrossReading::GuardableAdditive
    } else {
        CrossReading::Identical
    }
}

/// Does negating this literal read differently in the two universes?
///
/// Only at the one magnitude a fixed-width negation cannot represent: `-x` for
/// an unsigned `x != 0` (which wraps to `2^w - x`), and for a signed type the
/// value whose absolute value is `2^(w-1)` (`-iN::MIN == iN::MIN`). Every other
/// literal negates to the same number under both readings.
fn literal_negation_wraps(value: i128, ty: &TrustVcType) -> bool {
    match ty {
        TrustVcType::Uint { .. } => value != 0,
        TrustVcType::Int { width } => {
            let width = (*width).min(127);
            let magnitude = 1i128 << (width.saturating_sub(1));
            value.unsigned_abs() >= magnitude.unsigned_abs()
        }
        // Not a fixed-width type: both universes agree.
        _ => false,
    }
}

/// Best-effort type of an expression, used only by the `Neg` arm above. An
/// unknown type is charged as width bearing (fail-closed).
fn expr_type_is_width_bearing(expr: &TrustVcExpr) -> bool {
    match expr {
        TrustVcExpr::IntLit { ty, .. }
        | TrustVcExpr::Var { ty, .. }
        | TrustVcExpr::Arith { ty, .. }
        | TrustVcExpr::SpecialArith { ty, .. }
        | TrustVcExpr::IntConst { ty, .. }
        | TrustVcExpr::Ite { ty, .. } => width_bearing(ty),
        TrustVcExpr::Cast { to_ty, .. } => width_bearing(to_ty),
        TrustVcExpr::FnCall { return_ty, .. } => width_bearing(return_ty),
        TrustVcExpr::BoolLit(_) | TrustVcExpr::UnitLit | TrustVcExpr::StringLit(_) => false,
        _ => true,
    }
}

/// Build the IR guard that makes a FIXED-WIDTH fact safe to re-read over
/// unbounded `Int`, or `None` when there is nothing to guard.
///
/// Into the `Int` universe the two readings agree exactly when every
/// fixed-width `+`, `-`, `*` in the fact lands inside its own type, so the
/// guard is literally that: `MIN <= sub <= MAX` for each such subterm,
/// conjoined. Written as IR rather than as solver terms because the `Int` lane
/// deliberately emits NO no-overflow predicates of its own ("math integers have
/// no overflow"), so there is nothing there to borrow — and because in that
/// lane the range test is exactly the right statement, while in the
/// fixed-width lane it would be vacuously true and must NOT be used.
///
/// The result is `guard ==> fact`, which is true under BOTH readings whatever
/// the other one meant: where the arithmetic stays in range the two readings
/// are the same number, and where it does not the implication says nothing.
pub(in crate::encoder) fn int_lane_range_guarded(expr: &TrustVcExpr) -> Option<TrustVcExpr> {
    struct V {
        bounds: Vec<TrustVcExpr>,
        /// A width-bearing `+`/`-`/`*` was found whose operands include a name
        /// bound by an enclosing binder. See the escape note below.
        escaped_binder: bool,
    }
    impl V {
        fn bound(&mut self, subterm: &TrustVcExpr, ty: &TrustVcType) {
            self.bounds.push(TrustVcExpr::Compare {
                op: crate::ir::CompareOp::Ge,
                left: Box::new(subterm.clone()),
                right: Box::new(TrustVcExpr::IntConst {
                    ty: ty.clone(),
                    kind: crate::ir::IntConstKind::Min,
                }),
            });
            self.bounds.push(TrustVcExpr::Compare {
                op: crate::ir::CompareOp::Le,
                left: Box::new(subterm.clone()),
                right: Box::new(TrustVcExpr::IntConst {
                    ty: ty.clone(),
                    kind: crate::ir::IntConstKind::Max,
                }),
            });
        }
    }
    // SCOPE-AWARE, because the guard is hoisted to the TOP of the fact.
    //
    // The unscoped walk charged `forall|i: u32| a + i > a` exactly like its
    // ground instance and emitted `MIN <= a + i <= MAX` OUTSIDE the binder,
    // where `i` does not exist. Bound variables are uniquified, so the guard
    // could not silently capture a same-named parameter — but the expression
    // did not encode, and the int-lane branch turned that into a hard
    // `VerifyResult::Error` that blamed the user's source.
    //
    // A subterm that mentions a bound name has no top-level range test to
    // appeal to, so the whole fact is DROPPED (`None`) rather than guarded by a
    // condition that does not cover it. Dropping a hypothesis can only make a
    // goal harder, so this can never turn a refutation into a `Verified`;
    // guarding only the binder-free subterms would have left the quantified
    // arithmetic re-read and unguarded, which is the false-verify class this
    // module exists to close.
    impl ScopeAwareTrustVcExprVisitor for V {
        fn visit_expr_scoped(&mut self, expr: &TrustVcExpr, bound: &HashSet<&str>) -> bool {
            if self.escaped_binder {
                return false;
            }
            if let TrustVcExpr::Arith {
                op: ArithOp::Add | ArithOp::Sub | ArithOp::Mul,
                ty,
                ..
            } = expr
            {
                if width_bearing(ty) {
                    if !bound.is_empty() && expr_references_any_name(expr, bound) {
                        self.escaped_binder = true;
                        return false;
                    }
                    self.bound(expr, ty);
                }
            }
            true
        }
    }
    let mut v = V {
        bounds: Vec::new(),
        escaped_binder: false,
    };
    walk_expr_scoped(&mut v, expr, &HashSet::new());
    if v.escaped_binder {
        tracing::debug!(
            "cross-reading fact dropped: its fixed-width arithmetic mentions a bound \
             variable, so no top-level range guard covers it"
        );
        return None;
    }
    let mut guard = v.bounds.pop()?;
    while let Some(next) = v.bounds.pop() {
        guard = TrustVcExpr::Logic {
            op: crate::ir::LogicOp::And,
            left: Box::new(next),
            right: Box::new(guard),
        };
    }
    Some(TrustVcExpr::Implies {
        premise: Box::new(guard),
        conclusion: Box::new(expr.clone()),
    })
}

/// THE GATE, as the encode sites see it: what should be done with this
/// already-established fact on the way into an encoder whose reading is
/// `into`?
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::encoder) enum FactAdmission {
    /// Assert it exactly as it stands (the overwhelming majority: the two
    /// sides are equal in every solve that is not the nonlinear or the
    /// measure lane).
    AsIs,
    /// Assert `no_overflow(F) ==> F` instead.
    Guarded,
    /// Do not assert it at all.
    Drop,
}

/// Decide what to do with `fact` on the way into a solve reading `into`.
pub(in crate::encoder) fn fact_admission(
    fact: &PreparedObligation,
    into: ArithReading,
) -> FactAdmission {
    if fact_reading(fact) == into {
        return FactAdmission::AsIs;
    }
    match classify_cross_reading(&fact.expr) {
        CrossReading::Identical => FactAdmission::AsIs,
        CrossReading::GuardableAdditive => FactAdmission::Guarded,
        CrossReading::Unguardable => FactAdmission::Drop,
    }
}

/// May this fact be asserted UNCHANGED into a solve reading `into`?
pub(in crate::encoder) fn fact_crosses_into(fact: &PreparedObligation, into: ArithReading) -> bool {
    fact_admission(fact, into) == FactAdmission::AsIs
}

/// Convenience wrapper for the encode sites, which hold the raw flag.
pub(in crate::encoder) fn fact_admission_for(
    fact: &PreparedObligation,
    use_int_for_measures: bool,
) -> FactAdmission {
    let admission = fact_admission(fact, encoder_reading(use_int_for_measures));
    if admission != FactAdmission::AsIs {
        tracing::debug!(
            fact = %fact.name,
            fact_reading = ?fact_reading(fact),
            encoder_reading = ?encoder_reading(use_int_for_measures),
            ?admission,
            "a fact's fixed-width arithmetic is read differently by the target solve"
        );
    }
    admission
}

/// Would EVERY fact this solve holds reach the `into` reading UNCHANGED?
///
/// The int-mode timeout retry (`assertion::verify_main_attempt_with_retries`
/// step 1) re-solves a fixed-width goal over `Int` and ACCEPTS a `Verified`
/// from it. It runs only after the goal's own no-overflow predicates were
/// CHECKED, so where every fact also crosses `AsIs` the retry is the same
/// query under a reading that agrees with the first one everywhere it matters.
///
/// It is skipped as soon as one fact does not cross — but NOT for the reason
/// this gate shipped with at `b716c2c7`. That argument ("the retry would then
/// run against a smaller fact set, whose models are a superset of the ones the
/// overflow check ranged over") has the direction BACKWARDS: dropping or
/// weakening a hypothesis makes a goal HARDER and a proof over more models is
/// STRONGER, so a retry over a strictly weakened fact set was already safe.
///
/// The real exposure is the REWRITE, not the drop — and the witness this
/// comment carried at `dd122361` was itself FALSE. It named `z == -x + y`,
/// claiming a guard on the SUM leaves the negation under it free to be re-read
/// wrong. It does not, and the reason is elementary: reduction mod `2^N` is a
/// ring HOMOMORPHISM over `+`, `-`, `*` and unary `-`. For any cast-free tree
/// of those operators at ONE width, whose leaves are variables already in
/// range, the fixed-width value and the unbounded value of the WHOLE tree are
/// therefore congruent mod `2^N`. The fixed-width value always lies in
/// `[MIN, MAX]`, a complete residue system mod `2^N`, so a guard that pins the
/// unbounded value of the OUTERMOST node to that same interval forces the two
/// readings to be the SAME NUMBER, whatever wrapped underneath. At
/// `x == i32::MIN, y == -1` both readings of `-x + y` are `2147483647`. That
/// refutation is pinned numerically by
/// `the_outermost_bound_makes_both_readings_agree`, so the false witness
/// cannot come back.
///
/// THE CLASS IS STILL REAL, and the correct witness is a negation that
/// DOMINATES every node the guard bounds. `classify_cross_reading` charges a
/// width-bearing unary `-` as `GuardableAdditive` (so the fact is admitted
/// GUARDED rather than dropped), while `int_lane_range_guarded` emits bounds
/// for fixed-width `+`, `-` and `*` ONLY — never for a `Neg`. So
/// `z == -(x + y)` enters the `Int` lane under `MIN <= x + y <= MAX`: the
/// bound stops at the inner SUM, and the outermost node — the one whose value
/// is actually asserted equal to `z` — is left unbounded, which is exactly the
/// hypothesis the homomorphism argument needs and does not have. At
/// `x + y == i32::MIN` the guard is SATISFIED, the `Int` reading of
/// `-(x + y)` is `2147483648`, and the fixed-width reading that established
/// the fact was `i32::MIN`. The asserted fact is then FALSE where the
/// established one was true, which is the contradictory-hypothesis shape this
/// whole module exists to close: everything after it verifies vacuously.
/// Nothing downstream catches it on this path either — `vacuity_probe_result`
/// runs only when the context publishes an unverified axiom, which a plain
/// timeout retry need not do.
///
/// NOT A LIVE HOLE, AND THIS SKIP IS NOT A PATCH FOR ONE. The corrected
/// witness was probed END TO END and is fail-closed at BOTH revisions. Two
/// probes, and they are reported separately because their CATEGORIES differ:
/// the round-6 review's probe reported `Unknown`/`VacuousTruth` at HEAD and a
/// BYTE-IDENTICAL verdict at the merge base; the probe committed here,
/// `a_dominating_negation_hypothesis_is_fail_closed` in
/// `tests/one_reading_per_subterm.rs`, reports a model-less `Counterexample`
/// at HEAD (the merge-base half is not re-measured here). Neither publishes a
/// `Verified`, which is the whole bar. Round 7 added the DISCRIMINATING third:
/// `a_dominating_negation_pinned_to_the_boundary_is_fail_closed` pins `x + y`
/// to `i32::MIN` with two `Identical` facts, so the guard's premise HOLDS and
/// the hypothesis set really is contradictory — the shape described above,
/// reached without a broadcast lemma. It comes back
/// `Unknown { category: VacuousTruth }`: the engine reports the contradiction
/// rather than proving from it. The two probes that leave `x` and `y` free
/// cannot tell an incomplete guard from a sufficient one, and that one can. So the guard's incompleteness is real
/// and now pinned, but no path measured on either side turns it into a
/// published proof. The skip is CONSERVATISM against a rewrite whose guard is
/// known incomplete, not the repair for a live defect, and its whole cost is
/// COMPLETENESS: the retry it suppresses can only ever upgrade a TIMEOUT to
/// `Verified`.
///
/// Pinned by `a_guarded_assumption_closes_the_int_retry` and its four
/// sibling-list twins (the exposed class, one pin per fact list, so that
/// dropping a list from the scan reds a named test),
/// `the_guard_for_a_negation_does_not_cover_it` (the incompleteness itself, on
/// the corrected dominating-`Neg` witness) and
/// `the_outermost_bound_makes_both_readings_agree` (the refuted one).
///
/// DISCLOSED FINDING, appended VERBATIM from the round-7 review's
/// `remaining_imprecision` at integration time. It is recorded here, not
/// resolved: it narrows what the two probes above actually prove.
///
/// Round-7 disclosure. Two statements in the round-6 record are accurate but
/// read stronger than the evidence behind them. First, the end-to-end probe
/// a_dominating_negation_hypothesis_is_fail_closed does not construct the
/// contradictory hypothesis set its own doc comment describes: the Guarded
/// rewrite asserts "range implies fact", so with x and y free a solver
/// satisfies that hypothesis simply by letting x + y leave i32 range, the
/// incomplete guard never bites, and its model-less Counterexample is
/// therefore consistent with the guard being sufficient and with it being
/// incomplete alike - a non-regression witness, not an exploit attempt. This
/// review added the discriminating one, committed at a5075091 as
/// a_dominating_negation_pinned_to_the_boundary_is_fail_closed: two Identical
/// facts (a comparison against a non-wrapping negative literal crosses AsIs)
/// pin x + y to exactly i32::MIN, so the guard premise HOLDS, the Int reading
/// of the dominating Neg is 2147483648, and the int lane's own type-range
/// invariant for z refutes it. Measured at this HEAD it is fail-closed as
/// Unknown category VacuousTruth ("Assumptions are contradictory"), and it is
/// reached without a broadcast lemma or trait-postcondition axiom, so
/// vacuity_probe_result - whose context_publishes_unverified_axiom gate
/// excludes a plain assume! - is not what stands in the way. The conclusion
/// "real but not currently exploitable" stands and now rests on a probe that
/// could have falsified it. Second, the note in assertion_tests.rs that "the
/// three other call sites re-guard the same condition themselves" is not an
/// enumeration of call sites: exec_arith_overflow_in_scope has four
/// production callers (assertion.rs:637 and :903, assertion_bv_reuse.rs:205,
/// solve.rs:293); the named "check block" and "int_fallback_allowed" are two
/// consumers of the single :903 call, and the unnamed fourth caller - the
/// confirmation rerun's allow_int_fallback at :637 - is closed for a
/// nonlinear goal by its own not-effective_int_mode (initial_int_mode is
/// use_int_for_measures, true whenever is_nonlinear_arith is), not by a
/// literal not-is_nonlinear_arith. The substantive conclusion, that only the
/// solve.rs assume site reads the conjunct as its only guard, is correct as
/// measured. Third and last, neither round 6 nor this review re-measured
/// anything at the merge base, where crates/trust-vc-
/// core/src/encoder/verification/arith_reading.rs does not exist at all; the
/// merge-base halves of both witness probes remain attributed to the round-6
/// review rather than independently confirmed, and both the code and the
/// worker report say so.
pub(in crate::encoder) fn every_fact_crosses_into(
    slices: &super::VerificationSlices<'_>,
    into: ArithReading,
) -> bool {
    slices
        .assumptions
        .iter()
        .chain(slices.broadcast_assumptions)
        .chain(slices.verified_invariants)
        .chain(slices.verified_assert_by)
        .chain(slices.scoped_assumptions)
        .all(|fact| fact_crosses_into(fact, into))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{ArithOp, CompareOp, SpecialArithOp};

    fn u32_ty() -> TrustVcType {
        TrustVcType::Uint { width: 32 }
    }

    fn var(name: &str, ty: TrustVcType) -> TrustVcExpr {
        TrustVcExpr::Var {
            name: name.to_string(),
            ty,
        }
    }

    fn lit(value: i128, ty: TrustVcType) -> TrustVcExpr {
        TrustVcExpr::IntLit { value, ty }
    }

    fn cmp(op: CompareOp, left: TrustVcExpr, right: TrustVcExpr) -> TrustVcExpr {
        TrustVcExpr::Compare {
            op,
            left: Box::new(left),
            right: Box::new(right),
        }
    }

    /// A bare comparison of fixed-width variables means the same thing in both
    /// universes and must cross.
    #[test]
    fn a_bare_comparison_reads_the_same_in_both_universes() {
        let expr = cmp(CompareOp::Lt, var("a", u32_ty()), lit(100, u32_ty()));
        assert_eq!(classify_cross_reading(&expr), CrossReading::Identical);
    }

    /// LIAR TWIN: the same comparison with an ADDITION under it does not.
    #[test]
    fn a_comparison_over_fixed_width_addition_does_not() {
        let sum = TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(var("a", u32_ty())),
            right: Box::new(lit(1, u32_ty())),
            ty: u32_ty(),
        };
        let expr = cmp(CompareOp::Gt, sum, var("a", u32_ty()));
        assert_eq!(
            classify_cross_reading(&expr),
            CrossReading::GuardableAdditive
        );
    }

    /// The same addition at spec `int` width reads identically — that is what
    /// writing specs in `int` buys, and the gate must not take it away.
    #[test]
    fn spec_int_arithmetic_reads_the_same_in_both_universes() {
        let sum = TrustVcExpr::Arith {
            op: ArithOp::Add,
            left: Box::new(var("a", TrustVcType::MathInt)),
            right: Box::new(lit(1, TrustVcType::MathInt)),
            ty: TrustVcType::MathInt,
        };
        let expr = cmp(CompareOp::Gt, sum, var("a", TrustVcType::MathInt));
        assert_eq!(classify_cross_reading(&expr), CrossReading::Identical);
    }

    /// A shift is charged; the `Int` universe has no `bvshl` to agree with.
    #[test]
    fn a_fixed_width_shift_is_charged() {
        let shifted = TrustVcExpr::SpecialArith {
            op: SpecialArithOp::Shl,
            left: Box::new(var("a", u32_ty())),
            right: Box::new(lit(1, u32_ty())),
            ty: u32_ty(),
        };
        assert_eq!(
            classify_cross_reading(&cmp(CompareOp::Eq, shifted, var("b", u32_ty()))),
            CrossReading::Unguardable
        );
    }

    /// A cast touching a width is charged — truncation is invisible to `Int`.
    #[test]
    fn a_cast_touching_a_width_is_charged() {
        let cast = TrustVcExpr::Cast {
            expr: Box::new(var("a", u32_ty())),
            from_ty: u32_ty(),
            to_ty: TrustVcType::Uint { width: 8 },
        };
        assert_eq!(
            classify_cross_reading(&cmp(
                CompareOp::Eq,
                cast,
                lit(0, TrustVcType::Uint { width: 8 })
            )),
            CrossReading::Unguardable
        );
    }

    /// Arithmetic UNDER a quantifier is charged too: `forall|i: u32| i + 1 > i`
    /// is read two ways exactly like its ground instance.
    #[test]
    fn arithmetic_under_a_quantifier_is_charged() {
        let body = cmp(
            CompareOp::Gt,
            TrustVcExpr::Arith {
                op: ArithOp::Add,
                left: Box::new(var("i", u32_ty())),
                right: Box::new(lit(1, u32_ty())),
                ty: u32_ty(),
            },
            var("i", u32_ty()),
        );
        let quantified = TrustVcExpr::Quantifier {
            kind: crate::ir::QuantifierKind::Forall,
            bound_vars: vec![("i".to_string(), u32_ty())],
            body: Box::new(body),
            triggers: None,
            trigger_inference_mode: None,
        };
        assert_eq!(
            classify_cross_reading(&quantified),
            CrossReading::GuardableAdditive
        );
    }

    /// THE REGRESSION THIS FILE EXISTS FOR. `-100` is the same number in both
    /// universes, so a bare `a >= -100` must cross; charging it dropped the
    /// bound out of the nonlinear lane and refuted `a * b >= -10000`.
    #[test]
    fn a_negative_literal_bound_reads_the_same_in_both_universes() {
        let i32_ty = TrustVcType::Int { width: 32 };
        let neg = TrustVcExpr::Neg(Box::new(lit(100, i32_ty.clone())));
        let expr = cmp(CompareOp::Ge, var("a", i32_ty), neg);
        assert_eq!(classify_cross_reading(&expr), CrossReading::Identical);
    }

    /// THE SCOPED-WALKER PIN. A guard is hoisted to the TOP of the fact, so a
    /// subterm mentioning a BOUND variable has no top-level range test to
    /// appeal to: the fact is dropped whole rather than guarded by a condition
    /// that does not cover it. The unscoped walk emitted `MIN <= a + i <= MAX`
    /// outside the binder, and the assumption then failed to encode with
    /// "undefined variable `i`".
    #[test]
    fn a_guard_is_never_built_over_a_bound_variable() {
        let body = cmp(
            CompareOp::Ge,
            TrustVcExpr::Arith {
                op: ArithOp::Add,
                left: Box::new(var("a", u32_ty())),
                right: Box::new(var("i", u32_ty())),
                ty: u32_ty(),
            },
            var("a", u32_ty()),
        );
        let quantified = TrustVcExpr::Quantifier {
            kind: crate::ir::QuantifierKind::Forall,
            bound_vars: vec![("i".to_string(), u32_ty())],
            body: Box::new(body),
            triggers: None,
            trigger_inference_mode: None,
        };
        // Still CHARGED — the classification is unchanged, and must stay so or
        // the fact would cross unguarded.
        assert_eq!(
            classify_cross_reading(&quantified),
            CrossReading::GuardableAdditive
        );
        assert_eq!(int_lane_range_guarded(&quantified), None);
    }

    /// LIAR TWIN: the SAME arithmetic with nothing bound still produces a
    /// guard, and every name in it is free in the original fact.
    #[test]
    fn a_ground_fact_still_gets_its_guard() {
        let ground = cmp(
            CompareOp::Ge,
            TrustVcExpr::Arith {
                op: ArithOp::Add,
                left: Box::new(var("a", u32_ty())),
                right: Box::new(var("i", u32_ty())),
                ty: u32_ty(),
            },
            var("a", u32_ty()),
        );
        let guarded = int_lane_range_guarded(&ground).expect("a ground fact is guardable");
        let free_before = crate::ir_expr_traversal::free_root_names(&ground);
        let free_after = crate::ir_expr_traversal::free_root_names(&guarded);
        assert!(
            free_after.is_subset(&free_before),
            "the guard introduced a name the fact does not have: {free_after:?} vs {free_before:?}"
        );
        assert!(matches!(guarded, TrustVcExpr::Implies { .. }));
    }

    /// A binder that does NOT capture the arithmetic keeps its guard: the drop
    /// is keyed on capture, not on the mere presence of a quantifier.
    #[test]
    fn a_binder_that_captures_nothing_does_not_drop_the_fact() {
        let body = cmp(
            CompareOp::Ge,
            TrustVcExpr::Arith {
                op: ArithOp::Add,
                left: Box::new(var("a", u32_ty())),
                right: Box::new(lit(1, u32_ty())),
                ty: u32_ty(),
            },
            var("j", u32_ty()),
        );
        let quantified = TrustVcExpr::Quantifier {
            kind: crate::ir::QuantifierKind::Forall,
            bound_vars: vec![("j".to_string(), u32_ty())],
            body: Box::new(body),
            triggers: None,
            trigger_inference_mode: None,
        };
        let guarded = int_lane_range_guarded(&quantified).expect("a + 1 mentions no bound name");
        let free_after = crate::ir_expr_traversal::free_root_names(&guarded);
        assert!(
            !free_after.contains("j"),
            "the binder's name escaped: {free_after:?}"
        );
    }

    /// LIAR TWIN for that carve-out: the one magnitude whose negation really
    /// does wrap is still charged, and so is the negation of a VARIABLE.
    #[test]
    fn the_negation_that_wraps_is_still_charged() {
        let i32_ty = TrustVcType::Int { width: 32 };
        assert!(literal_negation_wraps(2147483648, &i32_ty));
        assert!(!literal_negation_wraps(2147483647, &i32_ty));
        assert!(literal_negation_wraps(1, &u32_ty()));
        assert!(!literal_negation_wraps(0, &u32_ty()));

        let neg_var = TrustVcExpr::Neg(Box::new(var("a", i32_ty.clone())));
        assert_eq!(
            classify_cross_reading(&cmp(CompareOp::Lt, neg_var, lit(0, i32_ty))),
            CrossReading::GuardableAdditive
        );
    }

    // ---------------------------------------------------------------------
    // THE SHORT-CIRCUIT: `fact_admission` is a NO-OP when the fact and the
    // solve already read the same universe. This is the load-bearing step in
    // the round-6 attribution of the two nested-loop summary suites, whose
    // every obligation is fixed-width on BOTH sides — the gate cannot have
    // moved a suite it never charges. Each control below carries the SAME
    // fact crossing the OTHER way as its twin, so none of them can pass by
    // `fact_admission` simply answering `AsIs` to everything.
    // ---------------------------------------------------------------------

    fn fact_with(
        kind: crate::vc::ObligationKind,
        mode: Option<crate::vc::SolverMode>,
        expr: TrustVcExpr,
    ) -> PreparedObligation {
        PreparedObligation {
            name: "f".to_string(),
            kind,
            location: None,
            condition_origin: crate::vc::ConditionOrigin::LoweredFromCondition,
            bound_vars: None,
            trigger_patterns: None,
            prepared_triggers: None,
            solver_mode: mode,
            is_opaque: false,
            is_inline: false,
            broadcast_group: None,
            invariant_namespace: None,
            trigger_inference_mode: None,
            broadcast_guard: None,
            raw_broadcast_guard_count: 0,
            step_meta: None,
            condition: String::new(),
            expr,
        }
    }

    /// `b == a + 1u32` — `GuardableAdditive`, the shape a nested-loop summary
    /// invariant has.
    fn wrapping_sum_eq() -> TrustVcExpr {
        cmp(
            CompareOp::Eq,
            var("b", u32_ty()),
            TrustVcExpr::Arith {
                op: ArithOp::Add,
                left: Box::new(var("a", u32_ty())),
                right: Box::new(lit(1, u32_ty())),
                ty: u32_ty(),
            },
        )
    }

    /// `b == a << 1u32` — `Unguardable`; there is no `bvshl` in the integers.
    fn shifted_eq() -> TrustVcExpr {
        cmp(
            CompareOp::Eq,
            var("b", u32_ty()),
            TrustVcExpr::SpecialArith {
                op: SpecialArithOp::Shl,
                left: Box::new(var("a", u32_ty())),
                right: Box::new(lit(1, u32_ty())),
                ty: u32_ty(),
            },
        )
    }

    /// A fixed-width invariant carrying wrapping `+` reaches a FIXED-WIDTH
    /// solve untouched, however hard the classifier charges it.
    #[test]
    fn a_wrapping_fact_reaches_a_fixed_width_solve_unchanged() {
        let fact = fact_with(crate::vc::ObligationKind::Assume, None, wrapping_sum_eq());
        assert_eq!(fact_reading(&fact), ArithReading::FixedWidth);
        assert_eq!(
            classify_cross_reading(&fact.expr),
            CrossReading::GuardableAdditive,
            "the classifier must still CHARGE it, or this pin is vacuous"
        );
        assert_eq!(
            fact_admission(&fact, ArithReading::FixedWidth),
            FactAdmission::AsIs
        );
    }

    /// LIAR TWIN: the SAME fact on the way into the integers is GUARDED, not
    /// `AsIs`. Without this the control above would pass on a gate that had
    /// stopped charging anything.
    #[test]
    fn the_same_wrapping_fact_is_guarded_into_math_int() {
        let fact = fact_with(crate::vc::ObligationKind::Assume, None, wrapping_sum_eq());
        assert_eq!(
            fact_admission(&fact, ArithReading::MathInt),
            FactAdmission::Guarded
        );
    }

    /// Even an UNGUARDABLE fact — a shift, which the integers cannot express
    /// at all — reaches a fixed-width solve unchanged.
    #[test]
    fn an_unguardable_fact_reaches_a_fixed_width_solve_unchanged() {
        let fact = fact_with(crate::vc::ObligationKind::Assume, None, shifted_eq());
        assert_eq!(
            classify_cross_reading(&fact.expr),
            CrossReading::Unguardable
        );
        assert_eq!(
            fact_admission(&fact, ArithReading::FixedWidth),
            FactAdmission::AsIs
        );
    }

    /// LIAR TWIN: the same shift is DROPPED on the way into the integers.
    #[test]
    fn the_same_unguardable_fact_is_dropped_into_math_int() {
        let fact = fact_with(crate::vc::ObligationKind::Assume, None, shifted_eq());
        assert_eq!(
            fact_admission(&fact, ArithReading::MathInt),
            FactAdmission::Drop
        );
    }

    /// The short-circuit is symmetric: a fact ESTABLISHED in the integers (a
    /// `by(nonlinear_arith)` conclusion) reaches the integer lane unchanged.
    #[test]
    fn an_int_lane_fact_reaches_the_int_lane_unchanged() {
        let fact = fact_with(
            crate::vc::ObligationKind::Assume,
            Some(crate::vc::SolverMode::NonlinearArith),
            wrapping_sum_eq(),
        );
        assert_eq!(fact_reading(&fact), ArithReading::MathInt);
        assert_eq!(
            fact_admission(&fact, ArithReading::MathInt),
            FactAdmission::AsIs
        );
    }

    /// LIAR TWIN: and is GUARDED coming back down into a fixed-width solve —
    /// the direction `b716c2c7` closed.
    #[test]
    fn the_same_int_lane_fact_is_guarded_into_fixed_width() {
        let fact = fact_with(
            crate::vc::ObligationKind::Assume,
            Some(crate::vc::SolverMode::NonlinearArith),
            wrapping_sum_eq(),
        );
        assert_eq!(
            fact_admission(&fact, ArithReading::FixedWidth),
            FactAdmission::Guarded
        );
    }

    /// THE DISCLOSED COST, pinned so it cannot change unnoticed. A
    /// `decreases` measure solves in the INTEGERS, and the `assume!` channel
    /// still reads WRAPPING (only `requires` moved, at `d93f0223`). So a
    /// hand-written model fact `n_entry == n + 1` is GUARDED on its way into
    /// the measure lane, and at `n == iN::MAX` the guard is false and the fact
    /// says nothing. That is what makes the ten `loop_decreases!` fixtures in
    /// `trust-vc` red on this branch, and it is a cost of closing the
    /// conflation, not a defect in the gate: under the wrapping reading those
    /// fixtures are genuinely unprovable.
    ///
    /// THE REPAIR IS NAMED, AND SO IS ITS PRICE — because a residual that names
    /// a repair without its price is how the next person ships it believing it
    /// is free. The repair is to move the `assume!` channel the way `d93f0223`
    /// moved `requires`: add `ObligationKind::Assume` to
    /// `spec_arith::is_requires_channel`, so a body assumption's `+`/`-`/`*`
    /// lowers to `MathInt` and crosses `AsIs` instead of being guarded.
    /// Applied and MEASURED by the round-6 review, it is a THREE-WAY trade,
    /// not a recovery:
    ///
    /// * it recovers NINE of the ten reds;
    /// * it BREAKS a tenth that is green today,
    ///   `loop_invariant_basic::test_loop_decreases_lexicographic_with_invariant`;
    /// * it reds a FALSE-VERIFY PIN,
    ///   `one_reading_per_subterm::a_wrapping_body_assumption_does_not_make_the_nonlinear_lane_vacuous`,
    ///   which stops refuting and goes to a fail-closed `Unknown`/`VacuousTruth`.
    ///
    /// That third item is the one that decides the shape of the change. Today
    /// that pin asserts `assume!(z + 1u32 == 0u32)` is satisfiable, because an
    /// `assume!` is read in the lane that was given it. Once an `assume!` IS
    /// spec code, `z + 1 == 0` has no solution over the integers and reporting
    /// the contradiction is the CORRECT answer — so the pin needs re-keying to
    /// the new semantics, exactly the correction of record this branch already
    /// performed for `encoder::tests::vacuous_truth::
    /// test_a_fixed_width_assumption_is_not_re_read_as_an_int_contradiction`.
    /// Re-keying a false-verify pin is a soundness-critical edit and gets its
    /// own adversarial round with its own before/after table; it is not a line
    /// to fold into a capability recovery. Net capability of the repair as
    /// measured is therefore +9/-1 on the fixtures plus one pin to re-key,
    /// and NONE of it is a reason to weaken the gate.
    #[test]
    fn a_wrapping_model_fact_is_guarded_into_the_measure_lane() {
        let fact = fact_with(crate::vc::ObligationKind::Assume, None, wrapping_sum_eq());
        let measure = fact_with(
            crate::vc::ObligationKind::MeasureDecreases,
            None,
            wrapping_sum_eq(),
        );
        assert_eq!(fact_reading(&measure), ArithReading::MathInt);
        assert_eq!(
            fact_admission(&fact, fact_reading(&measure)),
            FactAdmission::Guarded
        );
    }

    // ------------------------------------------------------------------
    // THE INT-RETRY SKIP (`every_fact_crosses_into`).
    //
    // It gates a retry that can only ever upgrade a TIMEOUT, so no end-to-end
    // fixture can tell it apart from its absence; these unit pins are what
    // make it measurable. See the function's own doc comment for WHY it is
    // kept: the `Guarded` rewrite's guard is incomplete for a unary `-`, and
    // the last two tests here pin exactly that incompleteness.
    // ------------------------------------------------------------------

    fn i32_ty() -> TrustVcType {
        TrustVcType::Int { width: 32 }
    }

    /// `a < 100u32` — reads the same in both universes, so it crosses `AsIs`.
    fn bare_bound() -> TrustVcExpr {
        cmp(CompareOp::Lt, var("a", u32_ty()), lit(100, u32_ty()))
    }

    /// Is the int-mode timeout retry still OPEN when `charged` sits in fact
    /// list `which` (0 assumptions, 1 broadcasts, 2 verified invariants,
    /// 3 `assert .. by` conclusions, 4 scoped assumptions) and every other
    /// list holds a fact that crosses?
    fn retry_open_with(which: usize, charged: TrustVcExpr) -> bool {
        let ctx = crate::prepared_context::PreparedVerificationContext::default();
        let crossing = fact_with(crate::vc::ObligationKind::Assume, None, bare_bound());
        let charged = fact_with(crate::vc::ObligationKind::Assume, None, charged);
        let lists: Vec<Vec<&PreparedObligation>> = (0..5)
            .map(|i| vec![if i == which { &charged } else { &crossing }])
            .collect();
        let slices = crate::encoder::verification::VerificationSlices::new(
            &ctx,
            lists[0].as_slice(),
            lists[1].as_slice(),
            lists[2].as_slice(),
            lists[3].as_slice(),
            lists[4].as_slice(),
        );
        every_fact_crosses_into(&slices, ArithReading::MathInt)
    }

    /// CONTROL, and it is what makes the five pins below non-vacuous: a
    /// context whose every fact crosses leaves the retry open, so a `false`
    /// there is the charged fact and not some unrelated refusal.
    #[test]
    fn a_context_whose_facts_all_cross_leaves_the_int_retry_open() {
        assert!(retry_open_with(0, bare_bound()));
    }

    /// ONE PIN PER FACT LIST: the scan must reach all five, because a fact
    /// the gate rewrites is a fact the retry must not run beside — wherever
    /// it is held. Dropping a list from the chain reds exactly one of these.
    #[test]
    fn a_guarded_assumption_closes_the_int_retry() {
        assert!(!retry_open_with(0, wrapping_sum_eq()));
    }

    #[test]
    fn a_guarded_broadcast_closes_the_int_retry() {
        assert!(!retry_open_with(1, wrapping_sum_eq()));
    }

    #[test]
    fn a_guarded_verified_invariant_closes_the_int_retry() {
        assert!(!retry_open_with(2, wrapping_sum_eq()));
    }

    #[test]
    fn a_guarded_assert_by_conclusion_closes_the_int_retry() {
        assert!(!retry_open_with(3, wrapping_sum_eq()));
    }

    #[test]
    fn a_guarded_scoped_assumption_closes_the_int_retry() {
        assert!(!retry_open_with(4, wrapping_sum_eq()));
    }

    /// A DROPPED fact closes it too. This half is pure conservatism — a
    /// hypothesis fewer can only make the goal harder — and it is pinned so
    /// that narrowing the skip to the `Guarded` class stays a deliberate,
    /// visible decision rather than a silent one.
    #[test]
    fn an_unguardable_assumption_closes_the_int_retry() {
        assert!(!retry_open_with(0, shifted_eq()));
    }

    /// `z == -x + y` at `i32` — a wrapping negation strictly UNDER the
    /// guardable sum. THE RETIRED WITNESS: the guard bounds the sum, which is
    /// the outermost node, and that already forces both readings to agree.
    /// Kept as the refutation's fixture (`the_outermost_bound_makes_both_readings_agree`).
    fn negation_sum_eq() -> TrustVcExpr {
        cmp(
            CompareOp::Eq,
            var("z", i32_ty()),
            TrustVcExpr::Arith {
                op: ArithOp::Add,
                left: Box::new(TrustVcExpr::Neg(Box::new(var("x", i32_ty())))),
                right: Box::new(var("y", i32_ty())),
                ty: i32_ty(),
            },
        )
    }

    /// `z == -(x + y)` at `i32` — the CORRECTED witness: a wrapping negation
    /// that DOMINATES the sum the guard builder bounds, so the outermost node
    /// of the fact's right-hand side carries no bound at all.
    fn dominating_negation_eq() -> TrustVcExpr {
        cmp(
            CompareOp::Eq,
            var("z", i32_ty()),
            TrustVcExpr::Neg(Box::new(TrustVcExpr::Arith {
                op: ArithOp::Add,
                left: Box::new(var("x", i32_ty())),
                right: Box::new(var("y", i32_ty())),
                ty: i32_ty(),
            })),
        )
    }

    /// The left-hand side of every range test the guard builder emitted.
    fn guard_bounds(guarded: &TrustVcExpr) -> Vec<TrustVcExpr> {
        fn collect(expr: &TrustVcExpr, out: &mut Vec<TrustVcExpr>) {
            match expr {
                TrustVcExpr::Logic {
                    op: crate::ir::LogicOp::And,
                    left,
                    right,
                } => {
                    collect(left, out);
                    collect(right, out);
                }
                TrustVcExpr::Compare { left, .. } => out.push((**left).clone()),
                other => panic!("unexpected guard shape: {other:?}"),
            }
        }
        let TrustVcExpr::Implies { premise, .. } = guarded else {
            panic!("a guarded fact is an implication, got {guarded:?}");
        };
        let mut out = Vec::new();
        collect(premise, &mut out);
        out
    }

    fn mentions_negation(expr: &TrustVcExpr) -> bool {
        struct V {
            found: bool,
        }
        impl TrustVcExprVisitor for V {
            fn visit_expr(&mut self, expr: &TrustVcExpr) {
                if matches!(expr, TrustVcExpr::Neg(_)) {
                    self.found = true;
                }
                walk_expr(self, expr);
            }
        }
        let mut v = V { found: false };
        v.visit_expr(expr);
        v.found
    }

    /// The right-hand side of a fact written as one top-level comparison —
    /// the term whose value the fact actually asserts, and therefore the node
    /// a range guard has to reach for the homomorphism argument to apply.
    fn compared_rhs(expr: &TrustVcExpr) -> &TrustVcExpr {
        let TrustVcExpr::Compare { right, .. } = expr else {
            panic!("fixture is a top-level comparison, got {expr:?}");
        };
        right
    }

    /// THE REFUTATION OF THE RETIRED WITNESS, pinned numerically so it cannot
    /// come back. Through `dd122361` this module claimed `z == -x + y` was
    /// re-read wrong inside its own guard. It is not, and the reason is a
    /// one-liner: reduction mod `2^N` is a ring HOMOMORPHISM over `+`, `-`,
    /// `*` and unary `-`. For a cast-free tree of those operators at one
    /// width, whose leaves are variables already in range, the fixed-width and
    /// the unbounded value of the WHOLE tree are congruent mod `2^N`; the
    /// fixed-width value always lies in `[MIN, MAX]`, a complete residue
    /// system, so a guard pinning the unbounded value of the OUTERMOST node to
    /// that interval forces the two readings to be the same number however
    /// much wrapped underneath. Here the guard's subject IS the outermost
    /// node, so the negation below it is covered.
    #[test]
    fn the_outermost_bound_makes_both_readings_agree() {
        let fact = fact_with(crate::vc::ObligationKind::Assume, None, negation_sum_eq());
        // Non-vacuity: this fact really is the GUARDED class, so the agreement
        // below is a property of the guard and not of the fact being dropped.
        assert_eq!(
            fact_admission(&fact, ArithReading::MathInt),
            FactAdmission::Guarded
        );
        assert!(mentions_negation(&fact.expr));

        let guarded = int_lane_range_guarded(&fact.expr).expect("a guardable fact gets a guard");
        let bounds = guard_bounds(&guarded);
        assert_eq!(bounds.len(), 2, "one MIN and one MAX test: {bounds:?}");
        let rhs = compared_rhs(&fact.expr);
        assert!(
            bounds.iter().all(|b| b == rhs),
            "the guard's subject is the OUTERMOST arithmetic node, so the negation \
             sits strictly under a bounded node: {bounds:?}"
        );

        // The arithmetic half. Inside the guard the two readings agree at
        // every boundary combination — including the exact point the retired
        // witness named as its counterexample.
        for x in [i32::MIN, i32::MIN + 1, -1i32, 0, 1, i32::MAX] {
            for y in [i32::MIN, -1i32, 0, 1, i32::MAX] {
                let unbounded = -(i64::from(x)) + i64::from(y);
                let fixed = i64::from(x.wrapping_neg().wrapping_add(y));
                if (i64::from(i32::MIN)..=i64::from(i32::MAX)).contains(&unbounded) {
                    assert_eq!(
                        unbounded, fixed,
                        "inside its own guard the two readings of `-x + y` must be the \
                         SAME number (x = {x}, y = {y})"
                    );
                }
            }
        }
        assert_eq!(
            -(i64::from(i32::MIN)) + i64::from(-1i32),
            2_147_483_647,
            "at `x == i32::MIN, y == -1` the unbounded reading is i32::MAX, in range"
        );
        assert_eq!(
            i32::MIN.wrapping_neg().wrapping_add(-1),
            2_147_483_647,
            "and the fixed-width reading is the same number — the retired witness \
             was not a counterexample at all"
        );
    }

    /// THE DISCLOSED INCOMPLETENESS, on the CORRECTED witness, pinned so it
    /// cannot change unnoticed and so the skip above has a measured reason to
    /// exist. The two halves of the `Guarded` rewrite disagree:
    /// `classify_cross_reading` charges a width-bearing unary `-` (so the fact
    /// is admitted GUARDED rather than dropped), while `int_lane_range_guarded`
    /// emits bounds for `+`, `-`, `*` ONLY — never for a `Neg`. That gap bites
    /// exactly when the negation DOMINATES every node the guard reaches, which
    /// is where the homomorphism argument above runs out of hypothesis: for
    /// `z == -(x + y)` the guard stops at the inner sum and the outermost node,
    /// the one whose value is asserted equal to `z`, carries no bound. At
    /// `x + y == i32::MIN` the guard HOLDS, the `Int` reading is `2^31` and the
    /// fixed-width reading that established the fact was `i32::MIN`, so inside
    /// its own guard the asserted fact is false.
    ///
    /// It is not a live hole: probed end to end the same shape is fail-closed
    /// at this HEAD (measured here) and, per the round-6 review, byte-identical
    /// at the merge base — see `every_fact_crosses_into`, which records both
    /// probes and the category they disagree on. The skip is conservatism
    /// against a guard whose incompleteness is real but not currently
    /// exploitable.
    #[test]
    fn the_guard_for_a_negation_does_not_cover_it() {
        let fact = fact_with(
            crate::vc::ObligationKind::Assume,
            None,
            dominating_negation_eq(),
        );
        // Non-vacuity: the fact really is admitted GUARDED, and really does
        // carry a negation — otherwise the pin below would prove nothing.
        assert_eq!(
            fact_admission(&fact, ArithReading::MathInt),
            FactAdmission::Guarded
        );
        assert!(mentions_negation(&fact.expr));

        let guarded = int_lane_range_guarded(&fact.expr).expect("a guardable fact gets a guard");
        let bounds = guard_bounds(&guarded);
        assert_eq!(bounds.len(), 2, "one MIN and one MAX test: {bounds:?}");

        // THE GAP. The outermost node of the fact's right-hand side is the
        // `Neg`, and nothing in the guard has it as a subject: every bound
        // stops at the sum strictly BELOW it.
        let rhs = compared_rhs(&fact.expr);
        assert!(
            matches!(rhs, TrustVcExpr::Neg(_)),
            "the corrected witness's outermost node is the negation: {rhs:?}"
        );
        assert!(
            !bounds.iter().any(|b| b == rhs),
            "no bound has the DOMINATING negation as its subject: {bounds:?}"
        );
        assert!(
            bounds.iter().all(|b| matches!(
                b,
                TrustVcExpr::Arith {
                    op: ArithOp::Add,
                    ..
                }
            )),
            "the guard bounds only the sum underneath: {bounds:?}"
        );

        // The arithmetic half: inside the satisfied guard the two readings are
        // DIFFERENT numbers.
        let x: i32 = -2_147_483_647;
        let y: i32 = -1;
        assert_eq!(
            i64::from(x) + i64::from(y),
            i64::from(i32::MIN),
            "the guarded sum lands in range, so `MIN <= x + y <= MAX` HOLDS"
        );
        assert_eq!(
            -(i64::from(x) + i64::from(y)),
            2_147_483_648,
            "the `Int` reading of the dominating negation"
        );
        assert_eq!(
            x.wrapping_add(y).wrapping_neg(),
            i32::MIN,
            "the fixed-width reading that ESTABLISHED the fact — inside its own \
             guard the asserted fact is false"
        );
    }

    /// LIAR TWIN: with no negation at all the same builder covers the whole
    /// arithmetic of the fact, so the gap above is a unary `-` that DOMINATES
    /// the bounded node — not the guard builder being empty in general, and
    /// not any unary `-` (one sitting under the bound is covered, which is
    /// what `the_outermost_bound_makes_both_readings_agree` measures).
    #[test]
    fn the_guard_for_a_plain_sum_does_cover_it() {
        let guarded =
            int_lane_range_guarded(&wrapping_sum_eq()).expect("a guardable fact gets a guard");
        let bounds = guard_bounds(&guarded);
        assert_eq!(bounds.len(), 2, "one MIN and one MAX test: {bounds:?}");
        assert!(
            bounds.iter().all(|b| matches!(
                b,
                TrustVcExpr::Arith {
                    op: ArithOp::Add,
                    ..
                }
            )),
            "every charged subterm is bounded: {bounds:?}"
        );
        assert!(!mentions_negation(&wrapping_sum_eq()));
    }

    /// LIAR TWIN for the cost pin: a model fact written in SPEC `int` crosses
    /// into the same measure lane `AsIs`. The cost is the READING, not the
    /// lane — which is why the sound repair is to move the channel, never to
    /// weaken the gate. What moving it costs is recorded on the cost pin
    /// above: it is +9/-1 on the fixtures and it re-keys a false-verify pin,
    /// not a free recovery.
    #[test]
    fn a_spec_int_model_fact_crosses_into_the_measure_lane_as_is() {
        let sum = cmp(
            CompareOp::Eq,
            var("b", TrustVcType::MathInt),
            TrustVcExpr::Arith {
                op: ArithOp::Add,
                left: Box::new(var("a", TrustVcType::MathInt)),
                right: Box::new(lit(1, TrustVcType::MathInt)),
                ty: TrustVcType::MathInt,
            },
        );
        let fact = fact_with(crate::vc::ObligationKind::Assume, None, sum);
        assert_eq!(
            fact_admission(&fact, ArithReading::MathInt),
            FactAdmission::AsIs
        );
    }
}
