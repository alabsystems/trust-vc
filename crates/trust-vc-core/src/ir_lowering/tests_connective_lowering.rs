// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Structural lowering tests for the Verus boolean connectives `==>`, `<==`,
//! and `<==>` as they flow through `parse_expr_str_with_chains` and the marker
//! lowering in `dispatch/macros.rs`.
//!
//! These pin the *sound boolean rewrite*:
//!   - `P ==> Q`  lowers to `Implies { premise: P, conclusion: Q }`.
//!   - `P <== Q`  lowers to `Implies { premise: Q, conclusion: P }` (reverse).
//!   - `P <==> Q` lowers to `And(Implies { P, Q }, Implies { Q, P })`.
//!
//! No new IR node is introduced; equivalence reuses `Implies` + `Logic(And)`.

use super::{lower_syn_expr, TypeEnv};
use crate::chained_comparisons::parse_expr_str_with_chains;
use crate::ir::{LogicOp, TrustVcType};
use crate::ir_expr::TrustVcExpr;

fn env_with(vars: &[(&str, TrustVcType)]) -> TypeEnv {
    let mut env = TypeEnv::new();
    for (name, ty) in vars {
        env.insert((*name).to_string(), ty.clone());
    }
    env
}

fn lower(src: &str, env: &TypeEnv) -> TrustVcExpr {
    let expr = parse_expr_str_with_chains(src).unwrap_or_else(|err| panic!("parse `{src}`: {err}"));
    lower_syn_expr(&expr, env).unwrap_or_else(|err| panic!("lower `{src}`: {err:?}"))
}

fn bool_env() -> TypeEnv {
    env_with(&[("p", TrustVcType::Bool), ("q", TrustVcType::Bool)])
}

#[test]
fn forward_implies_lowers_to_implies_node() {
    let lowered = lower("p ==> q", &bool_env());
    match lowered {
        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => {
            assert!(
                matches!(*premise, TrustVcExpr::Var { ref name, .. } if name == "p"),
                "premise should be `p`, got {premise:?}"
            );
            assert!(
                matches!(*conclusion, TrustVcExpr::Var { ref name, .. } if name == "q"),
                "conclusion should be `q`, got {conclusion:?}"
            );
        }
        other => panic!("expected Implies, got {other:?}"),
    }
}

#[test]
fn reverse_implies_swaps_operands() {
    // `p <== q` is `q ==> p`: premise = q, conclusion = p.
    let lowered = lower("p <== q", &bool_env());
    match lowered {
        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => {
            assert!(
                matches!(*premise, TrustVcExpr::Var { ref name, .. } if name == "q"),
                "reverse implication premise should be `q`, got {premise:?}"
            );
            assert!(
                matches!(*conclusion, TrustVcExpr::Var { ref name, .. } if name == "p"),
                "reverse implication conclusion should be `p`, got {conclusion:?}"
            );
        }
        other => panic!("expected Implies, got {other:?}"),
    }
}

#[test]
fn iff_lowers_to_conjunction_of_both_directions() {
    // `p <==> q` => `(p ==> q) && (q ==> p)`.
    let lowered = lower("p <==> q", &bool_env());
    let TrustVcExpr::Logic {
        op: LogicOp::And,
        left,
        right,
    } = lowered
    else {
        panic!("expected And, got {lowered:?}");
    };

    match *left {
        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => {
            assert!(
                matches!(*premise, TrustVcExpr::Var { ref name, .. } if name == "p"),
                "forward direction premise should be `p`, got {premise:?}"
            );
            assert!(
                matches!(*conclusion, TrustVcExpr::Var { ref name, .. } if name == "q"),
                "forward direction conclusion should be `q`, got {conclusion:?}"
            );
        }
        other => panic!("expected forward Implies, got {other:?}"),
    }

    match *right {
        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => {
            assert!(
                matches!(*premise, TrustVcExpr::Var { ref name, .. } if name == "q"),
                "backward direction premise should be `q`, got {premise:?}"
            );
            assert!(
                matches!(*conclusion, TrustVcExpr::Var { ref name, .. } if name == "p"),
                "backward direction conclusion should be `p`, got {conclusion:?}"
            );
        }
        other => panic!("expected backward Implies, got {other:?}"),
    }
}

#[test]
fn iff_is_looser_than_implies_in_lowering() {
    // `p ==> q <==> q` parses as `(p ==> q) <==> q`. The And's forward
    // direction therefore has an `Implies` as its premise.
    let lowered = lower("p ==> q <==> q", &bool_env());
    let TrustVcExpr::Logic {
        op: LogicOp::And,
        left,
        ..
    } = lowered
    else {
        panic!("expected And, got {lowered:?}");
    };
    match *left {
        TrustVcExpr::Implies { premise, .. } => {
            assert!(
                matches!(*premise, TrustVcExpr::Implies { .. }),
                "the `<==>` LHS should be the whole `p ==> q` implication, got {premise:?}"
            );
        }
        other => panic!("expected forward Implies, got {other:?}"),
    }
}
