//! Provenance tests for obligation collection.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use crate::context_management::get_context;
use crate::context_management::with_clean_thread_locals;
use crate::ir::{TrustVcExpr, TrustVcType};
use crate::obligation_collection::{
    collect_obligation, collect_symbolic_assume_expr, collect_symbolic_let_binding_expr,
    collect_variable,
};
use crate::vc::{ConditionOrigin, ObligationKind};

#[test]
fn test_symbolic_helpers_mark_prebuilt_origin() {
    with_clean_thread_locals(|| {
        let expr = TrustVcExpr::Var {
            name: "x".to_string(),
            ty: TrustVcType::Bool,
        };
        collect_symbolic_let_binding_expr(
            "ghost_stmt_view_x".to_string(),
            "x == p.view()".to_string(),
            expr.clone(),
        );
        collect_symbolic_assume_expr(
            "ghost_stmt_resolve_p".to_string(),
            "p.view() == x".to_string(),
            expr,
        );

        let context = get_context().expect("symbolic helpers should initialize a context");
        assert!(
            context.obligations.iter().all(|obligation| {
                obligation.condition_origin() == ConditionOrigin::PreBuiltExprCache
            }),
            "symbolic helper obligations should be marked as cache-backed"
        );
    });
}

#[test]
fn test_collect_obligation_prefers_typed_origin_when_lowering_succeeds() {
    with_clean_thread_locals(|| {
        collect_variable("x".to_string(), "i32".to_string());
        collect_obligation(
            ObligationKind::Assert,
            "typed_origin".to_string(),
            "x > 0".to_string(),
            None,
        );

        let context = get_context().expect("context should exist");
        let obligation = context
            .obligations
            .iter()
            .find(|obligation| obligation.name() == "typed_origin")
            .expect("typed obligation should be collected");

        assert_eq!(
            obligation.condition_origin(),
            ConditionOrigin::LoweredFromCondition
        );
        assert_eq!(
            obligation.condition(),
            "x > 0",
            "typed-lowered obligations should preserve the source condition string"
        );
    });
}

#[test]
fn test_collect_obligation_marks_legacy_translation_fallback_origin() {
    with_clean_thread_locals(|| {
        collect_obligation(
            ObligationKind::Assert,
            "translated_origin".to_string(),
            "missing_var > 0".to_string(),
            None,
        );

        let context = get_context().expect("context should exist");
        let obligation = context
            .obligations
            .iter()
            .find(|obligation| obligation.name() == "translated_origin")
            .expect("translated obligation should be collected");

        assert_eq!(
            obligation.condition_origin(),
            ConditionOrigin::LegacyTranslatedString
        );
    });
}
