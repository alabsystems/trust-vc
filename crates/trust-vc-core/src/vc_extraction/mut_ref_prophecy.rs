// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! New-mut-ref **Phase 1**: the first real semantic slice of the prophecy /
//! `new-mut-ref` core (`docs/archive/design-new-mut-ref.md`).
//!
//! For each scalar (`bool`/integer) `&mut T` parameter `P`, Verus' snapshot
//! model exposes two ground values of `sort_for_type(T)`:
//!
//! - `cur_P` — the *current* value `*P`, the entry snapshot, SSA-versioned
//!   through the body. At the verification boundary this is simply the declared
//!   parameter variable `P`.
//! - `fin_P` — a **fresh prophecy constant** equal to the prophesied *final*
//!   value `*final(P)`. It is allocated through the already-wired prophecy
//!   primitive: an IR `ProphecyNew { name, ty }` lowers to `solver.fresh_var`
//!   (`encoder/ir_encoder/prophecy.rs`), so `fin_P` starts life completely
//!   unconstrained.
//!
//! Spec ops map (per the design) to:
//!
//! | source surface                         | term  |
//! |----------------------------------------|-------|
//! | `*P` / `old(*P)` / `mut_ref_current(P)`| `cur_P` |
//! | bare `P` in a postcondition / `final(*P)` | `fin_P` |
//! | `has_resolved(P)`                      | `cur_P == fin_P` |
//!
//! The DESIGN calls for a **resolution** assumption at *every* function exit,
//! `fin_P == current_SSA_value`, encoded as an `Assume` over
//! `eq(ProphecyNew{fin_P}, current)`; `fin_P` is touched nowhere else, so those
//! equalities are the only facts the solver ever learns about the future value.
//! What this module actually SHIPS is a builder for ONE such equality
//! (`exit_resolution_obligation`) and no notion of an exit set, so "at every
//! exit" is an obligation on a caller that does not exist. Read the next
//! section before treating that as a detail — it is the whole soundness
//! argument, and it is not implemented.
//!
//! This module is intentionally a pure, side-effect-free *builder* over the
//! VC layer (`VerificationContext` + `TrustVcExpr`). The live
//! string-substitution `ErasedMutRefTarget` path in `body_extract.rs` is left
//! untouched (the design retires, never extends it).
//!
//! # DO NOT WIRE THIS AS IT STANDS — measured 2026-09-16
//!
//! An earlier version of this header claimed the builders "cannot introduce an
//! unsound encoding the prophecy primitive did not already permit". That is
//! **false**, and it is the sentence most likely to get this module wired. The
//! unsoundness is not in the primitive; it is in the OBLIGATION SHAPE the
//! builders hand back.
//!
//! `exit_resolution_obligation` emits an **unguarded** `Assume(fin_P == v)`.
//! It carries no path condition, and nothing anywhere checks that the exits a
//! caller emitted cover every path. Measured consequences, each pinned by a
//! test in this file's exit-totality block:
//!
//! - **One exit emitted out of two → false `Verified`.** `fin_P == v` then
//!   holds unconditionally, so a postcondition about the final value is proved
//!   on the paths the caller dropped. This is the branch-join and the
//!   zero-trip-loop case, i.e. exactly the refusal class a wiring would be
//!   trying to dissolve.
//! - **Both exits emitted with different values → contradictory assumptions.**
//!   The engine's vacuity guard catches this and refuses; it is the only thing
//!   standing between this shape and "prove anything". So the builders cannot
//!   model a differing-arm branch *at all*: one resolution is unsound, two are
//!   vacuous.
//! - **No place algebra.** Two `&mut` params that alias one location get
//!   independent prophecy constants, so contradictory finals for a single
//!   place are jointly satisfiable.
//!
//! # The fix shape, also measured
//!
//! All three hazards come from one missing ingredient: the exit's PATH
//! CONDITION. `Assume(path_cond => fin_P == v)` instead of `Assume(fin_P == v)`
//! and, pinned by the `guarded_*` tests below: an agreeing two-arm branch
//! VERIFIES its join (the case the live path over-rejects today), a
//! differing-arm branch gives a real counterexample instead of the vacuity
//! refusal, and — the load-bearing one — an INCOMPLETE exit set becomes
//! fail-closed by construction, with no separate totality check needed.
//!
//! So the guard is not a detail, it is the whole soundness argument, and it is
//! cheap to add to this signature. What is not cheap is supplying a real path
//! condition: `body_extract.rs` has **no exit set** at all
//! (`docs/archive/design-mutref-mode-wiring.md` records this as the prerequisite). Build the
//! exit set first, thread path conditions through it, then revisit these pins.
//!
//! Note also that the live path already implements the two-state `&mut`
//! parameter contract by SSA substitution
//! (`vc_extraction.rs::apply_mut_ref_final_state_to_postconditions` +
//! `body_extract.rs::capture_mut_ref_param_finals`), fail-closed on early
//! exit, escape and branch/loop havoc. Measured 2026-09-16: bare `x` and `*x`
//! in an `ensures`, and `old(*x)`, already denote the right states and refute
//! their liar twins. This module would be replacing a working mechanism, not
//! adding a missing one.
//!
//! # Soundness tripwires (design intent; only the first two are enforced here)
//!
//! - `fin_P` is constrained by **exactly one** equality per emitted exit.
//!   Nothing in this module emits any other constraint on the prophecy term.
//! - There is **no extensional `==`** for the `&mut` place itself; equalities
//!   are always between the *scalar* coordinates `cur_P` / `fin_P`.
//! - Exit-resolution completeness is **NOT** enforced — see the block above.
//!   It is a comment, and a comment is not a tripwire.

// Phase 1 landed the `(cur, fin)` builder substrate plus its solver-backed
// test battery, deliberately unwired (`88858fc6`, 2026-06-02 — no revert, no
// disabling commit; it was staged this way on purpose). The routing onto
// `body_extract.rs` was Phase 2+ of `docs/archive/design-new-mut-ref.md` and never
// happened. It must NOT happen as the builders stand — see the DO NOT WIRE
// block in the module header. The only consumers are the tests below.
#![allow(dead_code)]

use crate::ir::{TrustVcExpr, TrustVcType};
use crate::ir_builder;
use crate::vc::{ProofObligation, VerificationContext};

/// The prophecy name assigned to the final value of a scalar `&mut` parameter.
///
/// Kept distinct from the user-facing parameter name so the registry term for
/// `fin_P` can never collide with an ordinary variable named `P`.
#[must_use]
pub(crate) fn final_prophecy_name(param: &str) -> String {
    format!("__trust_vc_fin_{param}")
}

/// The IR term for `fin_P` (`*final(P)` / the bare `P` binding in a
/// postcondition). Resolving to the same `ProphecyNew { name }` everywhere is
/// what makes every reference share the one fresh prophecy constant.
#[must_use]
pub(crate) fn final_value_term(param: &str, inner_ty: &TrustVcType) -> TrustVcExpr {
    TrustVcExpr::ProphecyNew {
        name: final_prophecy_name(param),
        ty: inner_ty.clone(),
    }
}

/// The IR term for `cur_P` (`*P` / `old(*P)` / `mut_ref_current(P)`): the entry
/// snapshot, which at the verification boundary is the declared parameter
/// variable itself.
#[must_use]
pub(crate) fn current_value_term(param: &str, inner_ty: &TrustVcType) -> TrustVcExpr {
    ir_builder::var(param, inner_ty.clone())
}

/// The IR term for `has_resolved(P)`: `cur_P == fin_P`.
///
/// This is a scalar equality between the two coordinates — never an extensional
/// equality of the reference place — so it stays sound under the no-`==`-for-
/// `&mut` tripwire.
#[must_use]
pub(crate) fn has_resolved_term(param: &str, inner_ty: &TrustVcType) -> TrustVcExpr {
    ir_builder::eq(
        current_value_term(param, inner_ty),
        final_value_term(param, inner_ty),
    )
}

/// Registers the prophecy binding for a scalar `&mut` parameter so the prepared
/// context carries `fin_P`'s inner type into the type environment.
///
/// Idempotent w.r.t. the prophecy registry: the `ProphecyNew` name lookup in
/// `encode_prophecy_new` returns the same fresh term on every reference.
pub(crate) fn register_scalar_mut_ref_param(
    vc: &mut VerificationContext,
    param: &str,
    inner_ty: &TrustVcType,
) {
    vc.register_prophecy_binding(&final_prophecy_name(param), inner_ty.clone());
    // Make `*final(P)` / `final(*P)` legible in counterexamples.
    vc.register_counterexample_alias(final_prophecy_name(param), format!("*final({param})"), true);
}

/// Builds the single exit-resolution obligation `fin_P == current` for a scalar
/// `&mut` parameter.
///
/// `current` is the body's final SSA value of `*P` on this exit path. The
/// returned obligation is an **Assume**: it constrains the prophecy constant to
/// the resolved value, retroactively making all prior reasoning about `fin_P`
/// consistent. The caller is responsible for emitting one such obligation on
/// **every** exit path (the exit-resolution-completeness tripwire).
pub(crate) fn exit_resolution_obligation(
    param: &str,
    inner_ty: &TrustVcType,
    current: TrustVcExpr,
    exit_tag: &str,
) -> ProofObligation {
    let resolve = ir_builder::eq(final_value_term(param, inner_ty), current);
    ProofObligation::new_typed(
        format!("__trust_vc_mut_ref_resolve_{param}_{exit_tag}"),
        resolve,
        crate::vc::ObligationKind::Assume,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vc::{ObligationKind, TypedProofObligation, VariableDecl};
    use crate::VerifyResult;

    fn u64() -> TrustVcType {
        TrustVcType::Uint { width: 64 }
    }

    fn lit(v: i128) -> TrustVcExpr {
        ir_builder::int_lit(v, u64())
    }

    /// Shared scaffold: a scalar `&mut u64` param `x` whose body sets `*x = 5`,
    /// with a `requires(x == 0)` entry assumption and a single exit resolution
    /// `fin_x == 5`. Callers append assertion obligations and verify.
    fn scalar_mut_ref_ctx(extra: Vec<TypedProofObligation>) -> VerificationContext {
        let mut obligations = vec![
            // requires(*x == 0): the entry snapshot.
            TypedProofObligation::requires("req_entry", ir_builder::eq(cur(), lit(0))),
        ];
        // Exit resolution: fin_x == 5 (the body wrote 5).
        let resolve = exit_resolution_obligation("x", &u64(), lit(5), "ret");
        obligations.extend(extra);

        let mut vc =
            VerificationContext::from_typed_parts(vec![VariableDecl::new("x", u64())], obligations);
        register_scalar_mut_ref_param(&mut vc, "x", &u64());
        vc.push_obligation(resolve);
        vc
    }

    fn cur() -> TrustVcExpr {
        current_value_term("x", &u64())
    }

    fn fin() -> TrustVcExpr {
        final_value_term("x", &u64())
    }

    /// `final_value_term` is the fresh prophecy constant; `current_value_term`
    /// is the declared param var. They are distinct IR nodes.
    #[test]
    fn cur_and_fin_are_distinct_terms() {
        assert!(
            matches!(fin(), TrustVcExpr::ProphecyNew { ref name, .. } if name == "__trust_vc_fin_x")
        );
        assert!(matches!(cur(), TrustVcExpr::Var { ref name, .. } if name == "x"));
    }

    /// `has_resolved(P)` lowers to the scalar equality `cur_P == fin_P`, never
    /// an extensional `&mut` equality.
    #[test]
    fn has_resolved_is_scalar_cur_eq_fin() {
        match has_resolved_term("x", &u64()) {
            TrustVcExpr::Compare { op, left, right } => {
                assert_eq!(op, crate::ir_expr::CompareOp::Eq);
                assert!(matches!(*left, TrustVcExpr::Var { ref name, .. } if name == "x"));
                assert!(
                    matches!(*right, TrustVcExpr::ProphecyNew { ref name, .. } if name == "__trust_vc_fin_x")
                );
            }
            other => panic!("expected scalar Eq, got {other:?}"),
        }
    }

    /// The exit-resolution obligation is the single `Assume` constraining
    /// `fin_P`. (`fin_P`-unconstrained-except-exit tripwire, structural half.)
    #[test]
    fn exit_resolution_is_the_only_fin_constraint() {
        let ob = exit_resolution_obligation("x", &u64(), lit(5), "ret");
        assert_eq!(ob.kind(), ObligationKind::Assume);
        match ob.typed_expr() {
            Some(TrustVcExpr::Compare { op, left, .. }) => {
                assert_eq!(*op, crate::ir_expr::CompareOp::Eq);
                assert!(
                    matches!(**left, TrustVcExpr::ProphecyNew { ref name, .. } if name == "__trust_vc_fin_x")
                );
            }
            other => panic!("expected fin == current, got {other:?}"),
        }
    }

    /// POSITIVE: after `*x = 5` and exit resolution `fin_x == 5`, the
    /// postcondition `*final(x) == 5` (i.e. bare `x` / `fin_x`) verifies.
    #[test]
    fn final_value_after_resolution_verifies() {
        let post = TypedProofObligation::ensures("post_fin", ir_builder::eq(fin(), lit(5)));
        let vc = scalar_mut_ref_ctx(vec![post]);
        assert_eq!(vc.verify(), VerifyResult::Verified);
    }

    /// POSITIVE: the current/entry value `*x == 0` (from `requires`) is provable
    /// independently of the final value — `cur_P` and `fin_P` are separate.
    #[test]
    fn current_entry_value_verifies() {
        let post = TypedProofObligation::ensures("post_cur", ir_builder::eq(cur(), lit(0)));
        let vc = scalar_mut_ref_ctx(vec![post]);
        assert_eq!(vc.verify(), VerifyResult::Verified);
    }

    /// POSITIVE: `has_resolved(x)` is provable here because the body's final
    /// value equals the resolved prophecy AND happens to equal... no — here
    /// cur (entry) is 0 and fin is 5, so `has_resolved` must be FALSE. Asserting
    /// it must yield a counterexample, proving `has_resolved` is genuine
    /// `cur == fin` and not vacuously true.
    #[test]
    fn has_resolved_false_when_cur_differs_from_fin() {
        let post = TypedProofObligation::ensures("post_hr", has_resolved_term("x", &u64()));
        let vc = scalar_mut_ref_ctx(vec![post]);
        assert!(
            matches!(vc.verify(), VerifyResult::Counterexample { .. }),
            "has_resolved(x) must be falsifiable when entry(0) != final(5)"
        );
    }

    /// TRIPWIRE (the load-bearing one): reading the FINAL value before any
    /// resolution must NOT let the solver prove a *specific* false fact about
    /// it. `fin_x` is a fresh unconstrained constant, so `*final(x) == 5` is
    /// NOT entailed without the exit resolution — asserting it must produce a
    /// counterexample, never `Verified`. A spurious `Verified` here would mean
    /// the prophecy constant leaked a value (time-travel) and the whole model
    /// is unsound.
    #[test]
    fn final_value_unconstrained_before_resolution_is_not_provable() {
        // Build a context WITHOUT the exit resolution: just declare x, assume
        // the entry value, and assert a concrete claim about the final value.
        let mut vc = VerificationContext::from_typed_parts(
            vec![VariableDecl::new("x", u64())],
            vec![
                TypedProofObligation::requires("req_entry", ir_builder::eq(cur(), lit(0))),
                TypedProofObligation::ensures("post_fin", ir_builder::eq(fin(), lit(5))),
            ],
        );
        register_scalar_mut_ref_param(&mut vc, "x", &u64());
        // NOTE: deliberately NO exit_resolution_obligation pushed.
        let verdict = vc.verify();
        assert!(
            matches!(verdict, VerifyResult::Counterexample { .. }),
            "TRIPWIRE BREACH: final value provable without resolution -> {verdict:?}"
        );
    }

    /// TRIPWIRE companion: the *negation* of the unresolved claim is also not
    /// provable — confirming `fin_x` is genuinely unconstrained (could be 5 or
    /// not), not silently pinned to a default. Both `== 5` and `!= 5` over the
    /// unresolved prophecy must be falsifiable.
    #[test]
    fn final_value_negation_also_unprovable_before_resolution() {
        let mut vc = VerificationContext::from_typed_parts(
            vec![VariableDecl::new("x", u64())],
            vec![
                TypedProofObligation::requires("req_entry", ir_builder::eq(cur(), lit(0))),
                TypedProofObligation::ensures("post_fin_ne", ir_builder::ne(fin(), lit(5))),
            ],
        );
        register_scalar_mut_ref_param(&mut vc, "x", &u64());
        let verdict = vc.verify();
        assert!(
            matches!(verdict, VerifyResult::Counterexample { .. }),
            "fin_x must be unconstrained (!= 5 also unprovable) -> {verdict:?}"
        );
    }

    /// SOUNDNESS: a genuinely false postcondition about the resolved final value
    /// must be rejected even WITH resolution. Body resolves `fin_x == 5`;
    /// asserting `*final(x) == 6` must be a counterexample.
    #[test]
    fn wrong_final_value_after_resolution_is_counterexample() {
        let post = TypedProofObligation::ensures("post_bad", ir_builder::eq(fin(), lit(6)));
        let vc = scalar_mut_ref_ctx(vec![post]);
        assert!(
            matches!(vc.verify(), VerifyResult::Counterexample { .. }),
            "final == 6 must fail when resolution pins final == 5"
        );
    }

    /// EXIT-COMPLETENESS: with two distinct exit paths resolving `fin_x` to the
    /// SAME value 5, the shared postcondition still verifies (both resolutions
    /// agree). This models a branch where both arms write 5.
    #[test]
    fn two_agreeing_exit_resolutions_verify() {
        let r1 = exit_resolution_obligation("x", &u64(), lit(5), "then");
        let r2 = exit_resolution_obligation("x", &u64(), lit(5), "else");
        let mut vc = VerificationContext::from_typed_parts(
            vec![VariableDecl::new("x", u64())],
            vec![
                TypedProofObligation::requires("req_entry", ir_builder::eq(cur(), lit(0))),
                TypedProofObligation::ensures("post_fin", ir_builder::eq(fin(), lit(5))),
            ],
        );
        register_scalar_mut_ref_param(&mut vc, "x", &u64());
        vc.push_obligation(r1);
        vc.push_obligation(r2);
        assert_eq!(vc.verify(), VerifyResult::Verified);
    }

    /// `bool` scalar `&mut` params encode through the same path.
    #[test]
    fn bool_scalar_mut_ref_final_verifies() {
        let b = TrustVcType::Bool;
        let fin_b = final_value_term("flag", &b);
        let mut vc = VerificationContext::from_typed_parts(
            vec![VariableDecl::new("flag", b.clone())],
            vec![
                TypedProofObligation::requires(
                    "req_entry",
                    ir_builder::eq(current_value_term("flag", &b), ir_builder::bool_lit(false)),
                ),
                TypedProofObligation::ensures("post_fin", fin_b.clone()),
            ],
        );
        register_scalar_mut_ref_param(&mut vc, "flag", &b);
        // Resolve final to true.
        vc.push_obligation(exit_resolution_obligation(
            "flag",
            &b,
            ir_builder::bool_lit(true),
            "ret",
        ));
        assert_eq!(vc.verify(), VerifyResult::Verified);
    }

    // ============ EXIT-TOTALITY HAZARD PINS (measured 2026-09-16) ============
    //
    // These pin the MEASURED behaviour of the builders when a caller supplies
    // an INCOMPLETE or CONTRADICTORY exit set. They are not capability tests:
    // three of them pin an outcome that is FALSE in real Rust. They exist so
    // that the "do not wire this without exit totality" finding is executable
    // rather than a comment, and so that a future change which adds guarding
    // or totality checking FAILS here and forces a re-read of this block.
    //
    // Root cause: `exit_resolution_obligation` emits an UNGUARDED
    // `Assume(fin_P == v)`. Nothing carries the exit's path condition, and
    // nothing checks that the emitted exits cover every path. So:
    //   * one exit emitted out of two  -> `fin_P == v` holds unconditionally
    //     (hazard_*), a false `Verified` for every path the caller dropped;
    //   * both exits emitted with different values -> the assumption set is
    //     contradictory and the engine's vacuity guard fires (the one thing
    //     that saves this shape today).
    // A sound wiring must emit `Assume(path_cond => fin_P == v)` per exit plus
    // a totality fact over the guards. Neither exists in this module or on the
    // live extraction path (`body_extract.rs` has no exit set at all).

    /// GUARD PIN: two exits resolving `fin_x` to DIFFERENT values make the
    /// assumption set contradictory, and the engine refuses rather than
    /// proving the blatantly false `cur_x == 999`. This is the only thing
    /// standing between the unguarded-`Assume` shape and "prove anything".
    ///
    /// Liar twin: `two_agreeing_exit_resolutions_verify` above — the same two
    /// resolutions with the SAME value stay consistent and verify.
    #[test]
    fn disagreeing_exit_resolutions_are_refused_not_vacuously_proved() {
        let mut vc = VerificationContext::from_typed_parts(
            vec![VariableDecl::new("x", u64())],
            vec![
                TypedProofObligation::requires("req_entry", ir_builder::eq(cur(), lit(0))),
                // FALSE: the entry value is pinned to 0 by the requires.
                TypedProofObligation::ensures("post_false", ir_builder::eq(cur(), lit(999))),
            ],
        );
        register_scalar_mut_ref_param(&mut vc, "x", &u64());
        vc.push_obligation(exit_resolution_obligation("x", &u64(), lit(5), "then"));
        vc.push_obligation(exit_resolution_obligation("x", &u64(), lit(7), "else"));
        let verdict = vc.verify();
        assert!(
            !matches!(verdict, VerifyResult::Verified),
            "contradictory exit resolutions must never publish a Verified -> {verdict:?}"
        );
    }

    /// HAZARD PIN (false in real Rust): only the taken branch's exit is
    /// resolved. `fin_x == 7` then verifies unconditionally, even though the
    /// unemitted exit leaves `*x` at its entry value 0.
    ///
    /// This is the false `Verified` that wiring this module to a branch join
    /// would introduce. It is pinned, not fixed, because fixing it needs the
    /// path-guarded resolution + exit totality that do not exist yet.
    #[test]
    fn hazard_incomplete_exit_set_proves_a_false_final_value() {
        let mut vc = VerificationContext::from_typed_parts(
            vec![VariableDecl::new("x", u64())],
            vec![
                TypedProofObligation::requires("req_entry", ir_builder::eq(cur(), lit(0))),
                TypedProofObligation::ensures("post_fin", ir_builder::eq(fin(), lit(7))),
            ],
        );
        register_scalar_mut_ref_param(&mut vc, "x", &u64());
        // Only ONE of the two real exits is resolved.
        vc.push_obligation(exit_resolution_obligation("x", &u64(), lit(7), "then"));
        assert_eq!(
            vc.verify(),
            VerifyResult::Verified,
            "hazard pin drifted: an incomplete exit set is now detected — if this \
             is a deliberate fix, re-read the exit-totality block above and \
             promote these pins"
        );
    }

    /// HAZARD PIN (false in real Rust): the zero-trip-loop instance of the
    /// same hole. A resolution emitted from inside a loop body holds even when
    /// the loop runs zero times.
    #[test]
    fn hazard_zero_trip_loop_exit_resolution_proves_the_loop_body_value() {
        let mut vc = VerificationContext::from_typed_parts(
            vec![VariableDecl::new("x", u64()), VariableDecl::new("n", u64())],
            vec![
                TypedProofObligation::requires("req_entry", ir_builder::eq(cur(), lit(0))),
                TypedProofObligation::ensures("post_fin", ir_builder::eq(fin(), lit(7))),
            ],
        );
        register_scalar_mut_ref_param(&mut vc, "x", &u64());
        vc.push_obligation(exit_resolution_obligation("x", &u64(), lit(7), "loop_body"));
        assert_eq!(
            vc.verify(),
            VerifyResult::Verified,
            "hazard pin drifted: a zero-trip loop resolution is now guarded"
        );
    }

    /// HAZARD PIN (false in real Rust): two `&mut` params that alias one place
    /// get INDEPENDENT prophecy constants, so `fin_x == 5 && fin_y == 6` is
    /// jointly satisfiable for a single location. The builders carry no place
    /// algebra, so nothing relates `fin_x` and `fin_y`.
    ///
    /// Liar twin below: once the alias is stated as `fin_x == fin_y`, the
    /// `fin_y == 6` half is correctly refuted — so the hole is the MISSING
    /// alias fact, not the encoding.
    #[test]
    fn hazard_aliasing_mut_ref_params_get_independent_finals() {
        let vc = aliasing_pair_ctx();
        assert_eq!(
            vc.verify(),
            VerifyResult::Verified,
            "hazard pin drifted: aliasing &mut finals are now related"
        );
    }

    /// LIAR TWIN of the pin above: the hole is the MISSING alias fact, not the
    /// encoding. State `fin_x == fin_y` and resolve the single shared place
    /// once (to 5), and the split claim's `fin_y == 6` half is correctly
    /// REFUTED. Only one resolution is emitted here, so the assumption set
    /// stays consistent and the verdict is a genuine counterexample rather
    /// than the vacuity refusal.
    #[test]
    fn aliasing_mut_ref_finals_refuted_once_the_alias_fact_is_supplied() {
        let mut vc = VerificationContext::from_typed_parts(
            vec![VariableDecl::new("x", u64()), VariableDecl::new("y", u64())],
            vec![
                TypedProofObligation::requires(
                    "req_alias",
                    ir_builder::eq(cur(), current_value_term("y", &u64())),
                ),
                TypedProofObligation::ensures(
                    "post_split",
                    ir_builder::and(
                        ir_builder::eq(fin(), lit(5)),
                        ir_builder::eq(final_value_term("y", &u64()), lit(6)),
                    ),
                ),
            ],
        );
        register_scalar_mut_ref_param(&mut vc, "x", &u64());
        register_scalar_mut_ref_param(&mut vc, "y", &u64());
        // The fact the builders cannot express: both params name one place.
        vc.push_obligation(ProofObligation::new_typed(
            "alias_fact",
            ir_builder::eq(fin(), final_value_term("y", &u64())),
            ObligationKind::Assume,
        ));
        // One place, one resolution.
        vc.push_obligation(exit_resolution_obligation("x", &u64(), lit(5), "ret"));
        let verdict = vc.verify();
        assert!(
            matches!(verdict, VerifyResult::Counterexample { .. }),
            "with fin_x == fin_y stated and one resolution, the split final \
             claim must be refuted -> {verdict:?}"
        );
    }

    /// Shared scaffold for the aliasing pair: `x` and `y` denote one place
    /// (equal entry values), each exit-resolved to a DIFFERENT final value.
    fn aliasing_pair_ctx() -> VerificationContext {
        let mut vc = VerificationContext::from_typed_parts(
            vec![VariableDecl::new("x", u64()), VariableDecl::new("y", u64())],
            vec![
                TypedProofObligation::requires(
                    "req_alias",
                    ir_builder::eq(cur(), current_value_term("y", &u64())),
                ),
                TypedProofObligation::ensures(
                    "post_split",
                    ir_builder::and(
                        ir_builder::eq(fin(), lit(5)),
                        ir_builder::eq(final_value_term("y", &u64()), lit(6)),
                    ),
                ),
            ],
        );
        register_scalar_mut_ref_param(&mut vc, "x", &u64());
        register_scalar_mut_ref_param(&mut vc, "y", &u64());
        vc.push_obligation(exit_resolution_obligation("x", &u64(), lit(5), "ret"));
        vc.push_obligation(exit_resolution_obligation("y", &u64(), lit(6), "ret"));
        vc
    }

    /// A `&mut` that is never written emits no resolution at all, so `fin_x`
    /// stays free and `has_resolved(x)` is correctly NOT provable. (The
    /// fail-closed direction of the same incompleteness.)
    #[test]
    fn never_written_mut_ref_cannot_prove_has_resolved() {
        let mut vc = VerificationContext::from_typed_parts(
            vec![VariableDecl::new("x", u64())],
            vec![
                TypedProofObligation::requires("req_entry", ir_builder::eq(cur(), lit(0))),
                TypedProofObligation::ensures("post_hr", has_resolved_term("x", &u64())),
            ],
        );
        register_scalar_mut_ref_param(&mut vc, "x", &u64());
        assert!(
            matches!(vc.verify(), VerifyResult::Counterexample { .. }),
            "an unresolved prophecy must not prove has_resolved"
        );
    }

    // ===== THE FIX SHAPE, MEASURED (2026-09-16) =====
    //
    // The three hazards above all come from ONE missing ingredient: the exit's
    // PATH CONDITION. Attach it — `Assume(path_cond => fin_P == v)` instead of
    // `Assume(fin_P == v)` — and all three measurements change, including the
    // one that matters most: an INCOMPLETE exit set stops being unsound and
    // becomes fail-closed on its own, with no separate totality check.
    //
    // These three tests are the evidence for that claim. They are deliberately
    // NOT a new API: `exit_resolution_obligation` is unchanged, and the guard
    // is applied here by hand. Adding the parameter is cheap; supplying a real
    // path condition is not, because `body_extract.rs` has no exit set. Do that
    // first.

    /// The `c` of the modelled `if c { *x = .. } else { *x = .. }`.
    fn branch_cond() -> TrustVcExpr {
        ir_builder::var("c", TrustVcType::Bool)
    }

    /// `Assume(guard => fin_x == v)` — the shape `exit_resolution_obligation`
    /// does NOT produce.
    fn guarded_resolution(guard: TrustVcExpr, v: i128, tag: &str) -> ProofObligation {
        ProofObligation::new_typed(
            format!("__trust_vc_mut_ref_resolve_x_{tag}"),
            ir_builder::implies(guard, ir_builder::eq(fin(), lit(v))),
            ObligationKind::Assume,
        )
    }

    /// A two-arm branch, both guards emitted, both arms writing 7. Claiming
    /// `*final(x) == 7` VERIFIES.
    ///
    /// This is the case the live path currently over-rejects (a deref write in
    /// both arms of an `if` havocs the root at the region exit), so the guarded
    /// prophecy shape is a genuine capability gain — unlike the unguarded one,
    /// which goes vacuous on exactly this input.
    #[test]
    fn guarded_agreeing_branch_exits_verify_the_join() {
        let vc = guarded_branch_ctx(7, 7, 7);
        assert_eq!(vc.verify(), VerifyResult::Verified);
    }

    /// The same branch with arms writing DIFFERENT values: claiming the
    /// then-arm's value is a genuine `Counterexample` (witness `c = false`),
    /// not the vacuity refusal the unguarded shape produces. The guard keeps
    /// the assumption set consistent, so the engine can still reason.
    #[test]
    fn guarded_differing_branch_exits_refute_a_one_arm_claim() {
        let vc = guarded_branch_ctx(7, 9, 7);
        assert!(
            matches!(vc.verify(), VerifyResult::Counterexample { .. }),
            "a claim true on only one arm must be refuted, not vacuously proved"
        );
    }

    /// THE LOAD-BEARING ONE: emit only ONE of the two guarded exits. Under the
    /// unguarded shape this is the false `Verified` pinned by
    /// `hazard_incomplete_exit_set_proves_a_false_final_value`. Guarded, the
    /// unemitted path leaves `fin_x` free and the claim is REFUTED.
    ///
    /// So the path condition is not only the fix for the join — it makes
    /// exit-resolution incompleteness fail closed by construction, which is
    /// what a wiring actually needs (a caller cannot be trusted to enumerate
    /// every exit).
    #[test]
    fn guarded_incomplete_exit_set_fails_closed_instead_of_proving() {
        let mut vc = VerificationContext::from_typed_parts(
            vec![
                VariableDecl::new("x", u64()),
                VariableDecl::new("c", TrustVcType::Bool),
            ],
            vec![
                TypedProofObligation::requires("req_entry", ir_builder::eq(cur(), lit(0))),
                TypedProofObligation::ensures("post_fin", ir_builder::eq(fin(), lit(7))),
            ],
        );
        register_scalar_mut_ref_param(&mut vc, "x", &u64());
        vc.push_obligation(guarded_resolution(branch_cond(), 7, "then"));
        // The `else` exit is deliberately NOT emitted.
        assert!(
            matches!(vc.verify(), VerifyResult::Counterexample { .. }),
            "a guarded resolution must leave the unemitted path unconstrained"
        );
    }

    /// Scaffold: `if c { *x = v_then } else { *x = v_else }`, both exits
    /// guarded, asserting `*final(x) == claim`.
    fn guarded_branch_ctx(v_then: i128, v_else: i128, claim: i128) -> VerificationContext {
        let mut vc = VerificationContext::from_typed_parts(
            vec![
                VariableDecl::new("x", u64()),
                VariableDecl::new("c", TrustVcType::Bool),
            ],
            vec![
                TypedProofObligation::requires("req_entry", ir_builder::eq(cur(), lit(0))),
                TypedProofObligation::ensures("post_fin", ir_builder::eq(fin(), lit(claim))),
            ],
        );
        register_scalar_mut_ref_param(&mut vc, "x", &u64());
        vc.push_obligation(guarded_resolution(branch_cond(), v_then, "then"));
        vc.push_obligation(guarded_resolution(
            ir_builder::not(branch_cond()),
            v_else,
            "else",
        ));
        vc
    }
}
