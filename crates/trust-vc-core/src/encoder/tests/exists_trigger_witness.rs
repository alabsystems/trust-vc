//! Tests for existential-ensures witness instantiation driven by a user
//! `#[trigger]` term.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! These exercise `encode_refutation_expr` for `exists |n: nat| #[trigger]
//! g(n) >= x`, the shape of upstream Verus `real.rs::archimedean_nat`. The
//! refutation `forall n. ¬body(n)` is emitted with the user trigger so ay's
//! E-matching instantiates the existential against a ground `g(w)` already in
//! the assumption set — discharging the existential with `n := w` without a
//! general MBQI engine.

use super::*;

use crate::ir::{CompareOp, QuantifierKind, TrustVcExpr, TrustVcType};

/// Self-contained encoder harness mirroring the `nat_to_real(n) >= x` shape:
/// `x: real`, an uninterpreted `g: Int -> Real` standing in for `nat_to_real`,
/// and an `Int`-sorted witness constant `c`.
struct ExistsTriggerEnv {
    solver: Solver,
    variables: std::collections::HashMap<String, Term>,
    collection_lengths: std::collections::HashMap<String, Term>,
    var_types: std::collections::HashMap<String, TrustVcType>,
    functions: std::collections::HashMap<String, ay_dpll::api::FuncDecl>,
}

impl ExistsTriggerEnv {
    fn new() -> Self {
        ExistsTriggerEnv {
            solver: Solver::try_new(ay_dpll::api::Logic::All).unwrap(),
            variables: std::collections::HashMap::new(),
            collection_lengths: std::collections::HashMap::new(),
            var_types: std::collections::HashMap::new(),
            functions: std::collections::HashMap::new(),
        }
    }

    fn declare_var(&mut self, name: &str, ty: TrustVcType) {
        let sort = crate::encoder::types::sort_for_type(&ty);
        let term = self.solver.declare_const(name, sort);
        self.variables.insert(name.to_string(), term);
        self.var_types.insert(name.to_string(), ty);
    }

    /// Declare `nat_to_real`-like `g: Int -> Real`.
    fn declare_nat_to_real(&mut self, name: &str) {
        let arg_sort = crate::encoder::types::quantifier_sort_for_type(&TrustVcType::Nat);
        let decl = self
            .solver
            .try_declare_fun(name, &[arg_sort], ay_dpll::api::Sort::Real)
            .expect("test function declaration should succeed");
        self.functions.insert(name.to_string(), decl);
    }

    fn parser(&mut self) -> AstExpressionParser<'_> {
        AstExpressionParser::new(
            &mut self.solver,
            &self.variables,
            &mut self.collection_lengths,
            &self.var_types,
            &self.functions,
        )
    }
}

/// `g(n) >= x` body for `exists |n: nat| #[trigger] g(n) >= x`.
fn archimedean_exists(fn_name: &str) -> TrustVcExpr {
    let g_n = TrustVcExpr::FnCall {
        name: fn_name.to_string(),
        args: vec![TrustVcExpr::Var {
            name: "n".to_string(),
            ty: TrustVcType::Nat,
        }],
        return_ty: TrustVcType::Real,
    };
    let body = TrustVcExpr::Compare {
        op: CompareOp::Ge,
        left: Box::new(g_n.clone()),
        right: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::Real,
        }),
    };
    TrustVcExpr::Quantifier {
        kind: QuantifierKind::Exists,
        bound_vars: vec![("n".to_string(), TrustVcType::Nat)],
        body: Box::new(body),
        // User-supplied trigger: the `nat_to_real(n)` term.
        triggers: Some(vec![vec![g_n]]),
        trigger_inference_mode: None,
    }
}

/// `g(n) >= x` body for `exists |n: nat| g(n) >= x` with NO explicit trigger.
/// Mirrors upstream `archimedean_nat`'s `exists |n: nat| nat_to_real(n) >= x`,
/// which carries no `#[trigger]`. The triggerless-exists trigger inference must
/// synthesize `nat_to_real(n)` from the body so the refutation is still a
/// triggered universal.
fn archimedean_exists_triggerless(fn_name: &str) -> TrustVcExpr {
    let g_n = TrustVcExpr::FnCall {
        name: fn_name.to_string(),
        args: vec![TrustVcExpr::Var {
            name: "n".to_string(),
            ty: TrustVcType::Nat,
        }],
        return_ty: TrustVcType::Real,
    };
    let body = TrustVcExpr::Compare {
        op: CompareOp::Ge,
        left: Box::new(g_n),
        right: Box::new(TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::Real,
        }),
    };
    TrustVcExpr::Quantifier {
        kind: QuantifierKind::Exists,
        bound_vars: vec![("n".to_string(), TrustVcType::Nat)],
        body: Box::new(body),
        triggers: None,
        trigger_inference_mode: None,
    }
}

/// Assert the ground witness fact `g(c) >= x` for a fresh `Int` constant
/// `c >= 0`, emulating the proof-body `assert(x < nat_to_real(a + 1))`. The act
/// of asserting `g(c) >= x` registers `g(c)` as a ground term for E-matching.
fn assert_ground_witness(env: &mut ExistsTriggerEnv, fn_name: &str, holds: bool) {
    let c = env.solver.declare_const("c", ay_dpll::api::Sort::Int);
    let zero = env.solver.int_const(0);
    let c_nonneg = env.solver.try_ge(c, zero).unwrap();
    env.solver.try_assert_term(c_nonneg).unwrap();

    env.variables.insert("c".to_string(), c);
    env.var_types.insert("c".to_string(), TrustVcType::Nat);

    let g_c = {
        let mut parser = env.parser();
        parser
            .encode_trust_vc_expr(&TrustVcExpr::FnCall {
                name: fn_name.to_string(),
                args: vec![TrustVcExpr::Var {
                    name: "c".to_string(),
                    ty: TrustVcType::Nat,
                }],
                return_ty: TrustVcType::Real,
            })
            .expect("g(c) should encode")
    };
    let x = *env.variables.get("x").unwrap();
    let fact = if holds {
        env.solver.try_ge(g_c, x).unwrap()
    } else {
        // floor-too-low style: g(c) < x — does NOT witness the existential.
        env.solver.try_lt(g_c, x).unwrap()
    };
    env.solver.try_assert_term(fact).unwrap();
}

/// SHOULD-VERIFY: with a ground witness `g(c) >= x` in scope, the triggered
/// refutation `forall n. ¬(g(n) >= x)` is UNSAT — the existential is discharged
/// by instantiating the trigger with `n := c`. This is the archimedean_nat
/// mechanism.
#[test]
fn test_exists_trigger_witness_discharges_existential() {
    let mut env = ExistsTriggerEnv::new();
    env.declare_var("x", TrustVcType::Real);
    env.declare_nat_to_real("nat_to_real");
    assert_ground_witness(&mut env, "nat_to_real", /* holds */ true);

    let refutation = {
        let mut parser = env.parser();
        parser
            .encode_refutation_expr(&archimedean_exists("nat_to_real"))
            .expect("exists-with-trigger refutation should encode")
    };
    env.solver.try_assert_term(refutation).unwrap();

    let result = env.solver.check_sat();
    assert!(
        result.is_unsat(),
        "ground witness g(c) >= x must discharge exists |n| g(n) >= x via \
         trigger instantiation; got {:?}",
        result
    );
}

/// SHOULD-FAIL: with only a floor-too-low ground fact `g(c) < x` and no
/// supporting witness, the triggered refutation `forall n. ¬(g(n) >= x)` stays
/// satisfiable — the existential is NOT proven. Soundness guard: the mechanism
/// must not manufacture a witness that the assumptions do not establish.
#[test]
fn test_exists_trigger_without_witness_is_not_refuted() {
    let mut env = ExistsTriggerEnv::new();
    env.declare_var("x", TrustVcType::Real);
    env.declare_nat_to_real("nat_to_real");
    assert_ground_witness(&mut env, "nat_to_real", /* holds */ false);

    let refutation = {
        let mut parser = env.parser();
        parser
            .encode_refutation_expr(&archimedean_exists("nat_to_real"))
            .expect("exists-with-trigger refutation should encode")
    };
    env.solver.try_assert_term(refutation).unwrap();

    let result = env.solver.check_sat();
    assert!(
        !result.is_unsat(),
        "without an established witness the existential must not be discharged; \
         got {:?}",
        result
    );
}

/// DISCRIMINATING: the refutation must respect the `nat` domain guard. A ground
/// witness at a NEGATIVE index must not discharge `exists |n: nat| ...` — the
/// `n >= 0` guard on the universal refutation keeps the out-of-domain instance
/// from contradicting the refutation.
#[test]
fn test_exists_trigger_witness_respects_nat_lower_bound() {
    let mut env = ExistsTriggerEnv::new();
    env.declare_var("x", TrustVcType::Real);
    env.declare_nat_to_real("nat_to_real");

    // Ground fact g(c) >= x but with c < 0 (outside the nat domain). The
    // refutation forall is guarded by n >= 0, so this instance cannot fire.
    let c = env.solver.declare_const("c", ay_dpll::api::Sort::Int);
    let neg_one = env.solver.int_const(-1);
    let c_neg = env.solver.try_le(c, neg_one).unwrap();
    env.solver.try_assert_term(c_neg).unwrap();
    env.variables.insert("c".to_string(), c);
    env.var_types.insert("c".to_string(), TrustVcType::Nat);
    let g_c = {
        let mut parser = env.parser();
        parser
            .encode_trust_vc_expr(&TrustVcExpr::FnCall {
                name: "nat_to_real".to_string(),
                args: vec![TrustVcExpr::Var {
                    name: "c".to_string(),
                    ty: TrustVcType::Nat,
                }],
                return_ty: TrustVcType::Real,
            })
            .expect("g(c) should encode")
    };
    let x = *env.variables.get("x").unwrap();
    let fact = env.solver.try_ge(g_c, x).unwrap();
    env.solver.try_assert_term(fact).unwrap();

    let refutation = {
        let mut parser = env.parser();
        parser
            .encode_refutation_expr(&archimedean_exists("nat_to_real"))
            .expect("exists-with-trigger refutation should encode")
    };
    env.solver.try_assert_term(refutation).unwrap();

    let result = env.solver.check_sat();
    assert!(
        !result.is_unsat(),
        "a negative-index witness must not discharge exists over nat; got {:?}",
        result
    );
}

/// DISCRIMINATING: the refutation of an exists-with-trigger must be a *real*
/// universally-quantified term carrying the user trigger pattern — NOT a negated
/// `exists` routed through ay's CEGQI path. This is the structural property that
/// distinguishes trigger-driven witness instantiation from the generic
/// negated-`exists` fallback (which would produce a `Not` over an `Exists`).
#[test]
fn test_exists_trigger_refutation_is_triggered_forall() {
    let mut env = ExistsTriggerEnv::new();
    env.declare_var("x", TrustVcType::Real);
    env.declare_nat_to_real("nat_to_real");

    let mut parser = env.parser();
    let refutation = parser
        .encode_refutation_expr(&archimedean_exists("nat_to_real"))
        .expect("exists-with-trigger refutation should encode");

    assert_eq!(
        parser.solver.term_sort(refutation),
        ay_dpll::api::Sort::Bool,
        "exists refutation must be a Bool-sorted term"
    );
    assert_eq!(
        parser.solver.term_kind(refutation),
        ay_dpll::api::TermKind::Forall,
        "exists refutation must be a universal `forall n. ¬body(n)`, not a \
         negated exists; got {:?}",
        parser.solver.term_kind(refutation)
    );
    let triggers = parser
        .solver
        .quantifier_triggers(refutation)
        .expect("refutation forall should expose triggers");
    assert!(
        triggers.iter().any(|group| !group.is_empty()),
        "the user `#[trigger] nat_to_real(n)` pattern must be attached to the \
         refutation forall for E-matching; got {:?}",
        triggers
    );
}

/// DISCRIMINATING: a *triggerless* existential (no `#[trigger]`, the upstream
/// `archimedean_nat` shape) must still refute to a triggered universal — the
/// trigger inferred from the body (`nat_to_real(n)`) is attached so E-matching
/// can fire, rather than falling back to the negated-`exists` CEGQI path.
#[test]
fn test_triggerless_exists_refutation_infers_trigger() {
    let mut env = ExistsTriggerEnv::new();
    env.declare_var("x", TrustVcType::Real);
    env.declare_nat_to_real("nat_to_real");

    let mut parser = env.parser();
    let refutation = parser
        .encode_refutation_expr(&archimedean_exists_triggerless("nat_to_real"))
        .expect("triggerless exists refutation should encode");

    assert_eq!(
        parser.solver.term_kind(refutation),
        ay_dpll::api::TermKind::Forall,
        "triggerless exists must refute to a universal with an inferred trigger, \
         not a negated exists; got {:?}",
        parser.solver.term_kind(refutation)
    );
    let triggers = parser
        .solver
        .quantifier_triggers(refutation)
        .expect("refutation forall should expose triggers");
    assert!(
        triggers.iter().any(|group| !group.is_empty()),
        "an inferred `nat_to_real(n)` trigger must be attached to the triggerless \
         refutation forall for E-matching; got {:?}",
        triggers
    );
}

/// The inferred-trigger refutation must still be SOUND: with a ground witness
/// `g(c) >= x` it discharges the existential (UNSAT), exactly as the
/// user-trigger path does.
#[test]
fn test_triggerless_exists_discharges_with_ground_witness() {
    let mut env = ExistsTriggerEnv::new();
    env.declare_var("x", TrustVcType::Real);
    env.declare_nat_to_real("nat_to_real");
    assert_ground_witness(&mut env, "nat_to_real", /* holds */ true);

    let refutation = {
        let mut parser = env.parser();
        parser
            .encode_refutation_expr(&archimedean_exists_triggerless("nat_to_real"))
            .expect("triggerless exists refutation should encode")
    };
    env.solver.try_assert_term(refutation).unwrap();

    assert!(
        env.solver.check_sat().is_unsat(),
        "ground witness must discharge the triggerless existential via the \
         inferred trigger"
    );
}

/// SOUNDNESS: the inferred trigger must not manufacture a witness. With only a
/// floor-too-low ground fact `g(c) < x` the refutation stays satisfiable.
#[test]
fn test_triggerless_exists_without_witness_is_not_refuted() {
    let mut env = ExistsTriggerEnv::new();
    env.declare_var("x", TrustVcType::Real);
    env.declare_nat_to_real("nat_to_real");
    assert_ground_witness(&mut env, "nat_to_real", /* holds */ false);

    let refutation = {
        let mut parser = env.parser();
        parser
            .encode_refutation_expr(&archimedean_exists_triggerless("nat_to_real"))
            .expect("triggerless exists refutation should encode")
    };
    env.solver.try_assert_term(refutation).unwrap();

    assert!(
        !env.solver.check_sat().is_unsat(),
        "without an established witness the triggerless existential must not be \
         discharged"
    );
}

/// SOUNDNESS: a constructive equality candidate outside the binder domain is
/// not a witness. `c < 0` cannot satisfy `exists |n: nat| n == c`, even though
/// substituting the equality body alone would yield the tautology `c == c`.
#[test]
fn test_equality_witness_respects_nat_domain_guard() {
    let mut env = ExistsTriggerEnv::new();
    env.declare_var("c", TrustVcType::Nat);
    let c = *env.variables.get("c").unwrap();
    let zero = env.solver.int_const(0);
    let c_negative = env.solver.try_lt(c, zero).unwrap();
    env.solver.try_assert_term(c_negative).unwrap();

    let exists = TrustVcExpr::Quantifier {
        kind: QuantifierKind::Exists,
        bound_vars: vec![("n".to_string(), TrustVcType::Nat)],
        body: Box::new(TrustVcExpr::Compare {
            op: CompareOp::Eq,
            left: Box::new(TrustVcExpr::Var {
                name: "n".to_string(),
                ty: TrustVcType::Nat,
            }),
            right: Box::new(TrustVcExpr::Var {
                name: "c".to_string(),
                ty: TrustVcType::Nat,
            }),
        }),
        triggers: None,
        trigger_inference_mode: None,
    };
    let refutation = {
        let mut parser = env.parser();
        parser
            .encode_refutation_expr(&exists)
            .expect("equality-witness refutation should encode")
    };
    env.solver.try_assert_term(refutation).unwrap();

    assert!(
        !env.solver.check_sat().is_unsat(),
        "an out-of-domain equality candidate must not discharge a nat existential"
    );
}
