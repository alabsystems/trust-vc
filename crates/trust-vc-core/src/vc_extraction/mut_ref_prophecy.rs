// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! New-mut-ref **Phase 1**: the first real semantic slice of the prophecy /
//! `new-mut-ref` core (`design-new-mut-ref.md`).
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
//! At **every** function exit we emit a single **resolution** assumption,
//! `fin_P == current_SSA_value`, encoded as an `Assume` over
//! `eq(ProphecyNew{fin_P}, current)`. Because `fin_P` is otherwise touched
//! nowhere, this single equality is the *only* fact the solver ever learns
//! about the future value — which is exactly the soundness invariant Verus'
//! prophecy variables rely on.
//!
//! This module is intentionally a pure, side-effect-free *builder* over the
//! VC layer (`VerificationContext` + `TrustVcExpr`). It reuses the already
//! tested prophecy primitive end-to-end and adds **no** new solver behavior of
//! its own, so it cannot introduce an unsound encoding the prophecy primitive
//! did not already permit. The live string-substitution `ErasedMutRefTarget`
//! path in `body_extract.rs` is left untouched (the design retires, never
//! extends it); this builder is the sound `(cur, fin)` substrate later phases
//! route onto.
//!
//! # Soundness tripwires (enforced here, asserted by tests)
//!
//! - `fin_P` is constrained by **exactly one** equality — the exit resolution.
//!   Nothing in this module emits any other constraint on the prophecy term.
//! - There is **no extensional `==`** for the `&mut` place itself; equalities
//!   are always between the *scalar* coordinates `cur_P` / `fin_P`.
//! - The exit resolution is materialized once per requested exit value, so a
//!   caller that wires every exit path gets resolution on every exit path.

// Phase 1 lands the sound `(cur, fin)` builder substrate plus its full
// solver-backed test battery. The live `body_extract.rs` extraction path is
// routed onto these builders in Phase 2+ (per `design-new-mut-ref.md`);
// until then the only non-test consumers are the tests below, so the builders
// would otherwise read as dead code.
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
}
