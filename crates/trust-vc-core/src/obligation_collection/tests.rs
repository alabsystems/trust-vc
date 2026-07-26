// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::context_management::{get_context, with_clean_thread_locals};
use crate::ir::{TrustVcExpr, TrustVcType};
use crate::verify_macro::clear_all_thread_locals;

#[test]
fn symbolic_helpers_cache_prebuilt_assumptions() {
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
            expr.clone(),
        );

        let context = get_context().expect("symbolic helpers should initialize a context");
        assert_eq!(
            context.obligations.len(),
            2,
            "both symbolic assumptions should be collected"
        );
        assert!(
            context
                .obligations
                .iter()
                .all(|obligation| obligation.kind == crate::vc::ObligationKind::Assume),
            "symbolic helpers should collect Assume obligations"
        );
        assert!(
            take_pre_built_expr("ghost_stmt_view_x", "x == p.view()").is_some(),
            "let-binding helper should cache its pre-built expression"
        );
        assert!(
            take_pre_built_expr("ghost_stmt_resolve_p", "p.view() == x").is_some(),
            "assume helper should cache its pre-built expression"
        );
    });
}

#[test]
fn register_prophecy_local_persists_binding_in_context() {
    with_clean_thread_locals(|| {
        register_prophecy_local("p".to_string(), "u64".to_string());

        let context = get_context().expect("prophecy registration should initialize a context");
        assert_eq!(
            context.prophecy_bindings().get("p"),
            Some(&TrustVcType::Uint { width: 64 }),
            "prophecy registration should retain the inner type"
        );
    });
}

#[test]
fn collect_variable_marks_shared_reference_as_erased() {
    with_clean_thread_locals(|| {
        collect_variable("x".to_string(), "& 'a u64".to_string());

        let context = get_context().expect("variable collection should initialize a context");
        assert_eq!(
            context.get_variable_type("x"),
            Some(&TrustVcType::Uint { width: 64 })
        );
        assert!(
            context.is_erased_shared_ref_var("x"),
            "shared reference variables should support erased dereference lowering"
        );
    });
}

#[test]
fn collect_variable_runtime_marks_shared_reference_as_erased() {
    with_clean_thread_locals(|| {
        let value = 7u64;
        let reference = &value;
        collect_variable_runtime("r", &reference);

        let context =
            get_context().expect("runtime variable collection should initialize a context");
        assert_eq!(
            context.get_variable_type("r"),
            Some(&TrustVcType::Uint { width: 64 })
        );
        assert!(
            context.is_erased_shared_ref_var("r"),
            "runtime shared references should support erased dereference lowering"
        );
    });
}

/// Bool runtime value capture must produce "b == true" or "b == false",
/// NOT "b == 1" or "b == 0". The integer form creates a Bool vs Int sort
/// mismatch in ay. Fixes #2558.
#[test]
fn bool_runtime_capture_uses_string_not_integer() {
    with_clean_thread_locals(|| {
        let val_true: bool = true;
        collect_let_binding_runtime_value_from_ref("flag", &val_true);

        let context = get_context().expect("bool capture should initialize a context");
        let assumptions: Vec<_> = context
            .obligations
            .iter()
            .filter(|o| matches!(o.kind, crate::vc::ObligationKind::Assume))
            .collect();
        assert_eq!(assumptions.len(), 1, "should have one assumption");
        assert!(
            assumptions[0].condition.contains("true"),
            "bool=true should produce 'flag == true', got: {}",
            assumptions[0].condition
        );
        assert!(
            !assumptions[0].condition.contains(" 1"),
            "bool capture must NOT use integer 1 (#2558), got: {}",
            assumptions[0].condition
        );

        clear_all_thread_locals();

        let val_false: bool = false;
        collect_let_binding_runtime_value_from_ref("b", &val_false);

        let context2 = get_context().expect("bool capture should initialize a context");
        let assumptions2: Vec<_> = context2
            .obligations
            .iter()
            .filter(|o| matches!(o.kind, crate::vc::ObligationKind::Assume))
            .collect();
        assert_eq!(assumptions2.len(), 1, "should have one assumption");
        assert!(
            assumptions2[0].condition.contains("false"),
            "bool=false should produce 'b == false', got: {}",
            assumptions2[0].condition
        );
        assert!(
            !assumptions2[0].condition.contains(" 0"),
            "bool capture must NOT use integer 0 (#2558), got: {}",
            assumptions2[0].condition
        );
    });
}
