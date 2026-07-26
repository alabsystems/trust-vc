// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashMap;

use super::ForcedFlagGuard;
use crate::encoder::verification::test_hooks::{
    FORCE_ENCODE_CONDITION_PANIC, FORCE_TRUST_VC_EXPR_ENCODE_PANIC,
};
use crate::encoder::{AYEncoder, AstExpressionParser};
use crate::ir::TrustVcExpr;
use ay_dpll::api::{FuncDecl, Logic, Solver, Term};

#[test]
fn test_with_flag_unwind_safe_restores_prior_true_after_panic() {
    let mut flag = true;
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        crate::encoder::with_flag_unwind_safe!(flag, false, {
            panic!("forced with_flag_unwind_safe panic");
        });
    }));

    assert!(
        result.is_err(),
        "forced with_flag_unwind_safe panic should unwind through the guard"
    );
    assert!(
        flag,
        "with_flag_unwind_safe must restore the prior true value"
    );
}

#[test]
fn test_encode_trust_vc_expr_restores_depth_guard_after_panic() {
    let mut solver = Solver::try_new(Logic::All).expect("test solver should construct");
    let variables: HashMap<String, Term> = HashMap::new();
    let mut collection_lengths: HashMap<String, Term> = HashMap::new();
    let var_types: HashMap<String, crate::ir::TrustVcType> = HashMap::new();
    let functions: HashMap<String, FuncDecl> = HashMap::new();
    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    let result = {
        let _panic = ForcedFlagGuard::new(&FORCE_TRUST_VC_EXPR_ENCODE_PANIC);
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            parser.encode_trust_vc_expr(&TrustVcExpr::BoolLit(true))
        }))
    };

    assert!(
        result.is_err(),
        "forced encode_trust_vc_expr panic should unwind through the guard"
    );
    assert!(
        !parser.expr_depth_guard_active,
        "expr_depth_guard_active must be restored after panic"
    );
}

#[test]
fn test_add_typed_assumption_restores_encoder_flags_after_panic() {
    let mut encoder = AYEncoder::new();
    encoder.state.in_assumption_context = true;
    encoder.state.preserve_assumption_quantifier_sorts = false;

    let result = {
        let _panic = ForcedFlagGuard::new(&FORCE_ENCODE_CONDITION_PANIC);
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            encoder.add_typed_assumption_with_concrete_quantifier_sorts(
                "panic_assume",
                &TrustVcExpr::BoolLit(true),
                None,
            )
        }))
    };

    assert!(
        result.is_err(),
        "forced assumption panic should unwind through both encoder flag guards"
    );
    assert!(
        encoder.state.in_assumption_context,
        "in_assumption_context must restore to its prior value"
    );
    assert!(
        !encoder.state.preserve_assumption_quantifier_sorts,
        "preserve_assumption_quantifier_sorts must restore to its prior value"
    );
}

#[test]
fn test_add_typed_assumption_restores_preserve_quantifier_sorts_from_true_after_panic() {
    let mut encoder = AYEncoder::new();
    encoder.state.in_assumption_context = true;
    encoder.state.preserve_assumption_quantifier_sorts = true;

    let result = {
        let _panic = ForcedFlagGuard::new(&FORCE_ENCODE_CONDITION_PANIC);
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            encoder.add_typed_assumption("panic_assume", &TrustVcExpr::BoolLit(true), None)
        }))
    };

    assert!(
        result.is_err(),
        "forced assumption panic should unwind through both encoder flag guards"
    );
    assert!(
        encoder.state.in_assumption_context,
        "in_assumption_context must restore to its prior true value"
    );
    assert!(
        encoder.state.preserve_assumption_quantifier_sorts,
        "preserve_assumption_quantifier_sorts must restore to its prior true value"
    );
}

#[test]
fn test_reconcile_equality_assumptions_restores_assumption_context_after_panic() {
    let mut encoder = AYEncoder::new();
    encoder.state.in_assumption_context = true;

    let exprs = vec![TrustVcExpr::BoolLit(true)];
    let result = {
        let _panic = ForcedFlagGuard::new(&FORCE_ENCODE_CONDITION_PANIC);
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            encoder.reconcile_equality_assumptions(&exprs)
        }))
    };

    assert!(
        result.is_err(),
        "forced reconcile panic should unwind through the assumption-context guard"
    );
    assert!(
        encoder.state.in_assumption_context,
        "reconcile_equality_assumptions must restore in_assumption_context"
    );
}
