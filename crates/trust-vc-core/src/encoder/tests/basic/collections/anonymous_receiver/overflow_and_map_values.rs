// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Overflow guard label propagation and map_values key_ty metadata tests.

use super::*;

fn overflow_labels_after_anonymous_set_op(
    op: crate::ir::CollectionOp,
    len_guard_label: Option<&str>,
) -> Result<Vec<String>, String> {
    use crate::encoder::parser_state::{CollectionKind, CollectionMeta};
    use crate::ir_expr::TrustVcExpr;
    use ay_dpll::api::{ArraySort, Sort};

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let mut functions = std::collections::HashMap::new();
    let pw = crate::ir::pointer_width();

    let set_sort = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::bitvec(32),
        element_sort: Sort::Bool,
    }));
    let mk_set = solver
        .try_declare_fun("mk_set_for_len", &[], set_sort)
        .expect("declare mk_set_for_len");
    functions.insert("mk_set_for_len".to_string(), mk_set);

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    let receiver = TrustVcExpr::FnCall {
        name: "mk_set_for_len".to_string(),
        args: vec![],
        return_ty: crate::ir::TrustVcType::Set(Box::new(crate::ir::TrustVcType::Int { width: 32 })),
    };
    let receiver_term = parser
        .encode_trust_vc_expr(&receiver)
        .expect("encode anonymous set receiver");
    let len_term = parser
        .solver
        .fresh_var("__anon_set_len_meta", Sort::bitvec(pw));
    let len_guard = len_guard_label.map(|label| {
        (
            std::borrow::Cow::Owned(label.to_string()),
            parser
                .solver
                .declare_const("__anon_set_len_guard", Sort::Bool),
        )
    });
    parser.register_collection_meta(
        receiver_term,
        CollectionMeta {
            kind: CollectionKind::Set,
            len_term: Some(len_term),
            len_guard,
            elem_ty: Some(crate::ir::TrustVcType::Int { width: 32 }),
            key_ty: None,
            dom_term: None,
        },
    );

    let (args, ty) = match op {
        crate::ir::CollectionOp::Len => (
            vec![],
            crate::ir::TrustVcType::Uint {
                width: crate::ir::pointer_width(),
            },
        ),
        crate::ir::CollectionOp::IsEmpty => (vec![], crate::ir::TrustVcType::Bool),
        crate::ir::CollectionOp::Contains => (
            vec![TrustVcExpr::IntLit {
                value: 5,
                ty: crate::ir::TrustVcType::Int { width: 32 },
            }],
            crate::ir::TrustVcType::Bool,
        ),
        _ => unreachable!("helper covers len/is_empty/contains only"),
    };

    let encoded = parser
        .encode_trust_vc_expr(&TrustVcExpr::CollectionOp {
            op,
            receiver: Box::new(receiver),
            receiver_name: None,
            args,
            ty,
        })
        .map_err(|e| e.to_string())?;
    if matches!(op, crate::ir::CollectionOp::Len) {
        assert_eq!(
            encoded, len_term,
            "anonymous len() should resolve the registered term-keyed length"
        );
    }

    Ok(parser
        .overflow_checks
        .into_iter()
        .map(|(label, _)| label.into_owned())
        .collect())
}

#[test]
fn test_len_on_anonymous_set_uses_term_keyed_length_without_guard() {
    let labels = overflow_labels_after_anonymous_set_op(crate::ir::CollectionOp::Len, None)
        .expect("anonymous len() should use term-keyed metadata");
    assert!(
        labels.is_empty(),
        "unguarded anonymous len() should not enqueue overflow checks"
    );
}

#[test]
fn test_is_empty_on_anonymous_set_emits_registered_len_guard() {
    let labels = overflow_labels_after_anonymous_set_op(
        crate::ir::CollectionOp::IsEmpty,
        Some("anonymous set len guard"),
    )
    .expect("anonymous is_empty() should use term-keyed metadata");
    assert_eq!(
        labels,
        vec!["anonymous set len guard".to_string()],
        "is_empty() should emit the stored length guard when consuming len metadata"
    );
}

#[test]
fn test_contains_on_anonymous_set_does_not_emit_registered_len_guard() {
    let labels = overflow_labels_after_anonymous_set_op(
        crate::ir::CollectionOp::Contains,
        Some("anonymous set len guard"),
    )
    .expect("anonymous contains() should still encode from term-keyed metadata");
    assert!(
        labels.is_empty(),
        "non-length operations should not emit stored len guards"
    );
}

/// DISCRIMINATING: map_values on anonymous Map receiver succeeds when key_ty
/// is populated in term-keyed metadata. Without #2507 fix, this fails with
/// "Map operation requires a named receiver with known type" because
/// `map_key_value_types` could not resolve the key type from anonymous results.
#[test]
fn test_map_values_on_anonymous_map_uses_term_keyed_key_ty() {
    use crate::encoder::parser_state::{CollectionKind, CollectionMeta};
    use crate::ir_expr::TrustVcExpr;
    use ay_dpll::api::{ArraySort, Sort};

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let mut functions = std::collections::HashMap::new();
    let pw = crate::ir::pointer_width();

    // Declare a zero-arity UF that returns Map<i32, Bool>
    let map_sort = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::bitvec(32),
        element_sort: Sort::Bool,
    }));
    let mk_map = solver
        .try_declare_fun("mk_map", &[], map_sort)
        .expect("declare mk_map");
    functions.insert("mk_map".to_string(), mk_map);

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );

    // Encode the anonymous Map receiver
    let receiver = TrustVcExpr::FnCall {
        name: "mk_map".to_string(),
        args: vec![],
        return_ty: crate::ir::TrustVcType::Map(
            Box::new(crate::ir::TrustVcType::Int { width: 32 }),
            Box::new(crate::ir::TrustVcType::Bool),
        ),
    };
    let receiver_term = parser
        .encode_trust_vc_expr(&receiver)
        .expect("encode anonymous map receiver");

    // Register Map metadata WITH key_ty (#2507)
    let len_term = parser.solver.fresh_var("__anon_map_len", Sort::bitvec(pw));
    let dom_sort = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::bitvec(32),
        element_sort: Sort::Bool,
    }));
    let dom_term = parser.solver.fresh_var("__anon_map_dom", dom_sort);
    parser.register_collection_meta(
        receiver_term,
        CollectionMeta {
            kind: CollectionKind::Map,
            len_term: Some(len_term),
            len_guard: None,
            elem_ty: Some(crate::ir::TrustVcType::Bool),
            key_ty: Some(crate::ir::TrustVcType::Int { width: 32 }),
            dom_term: Some(dom_term),
        },
    );

    // Build map_values(|v: Bool| v) — identity closure
    let closure = TrustVcExpr::SpecClosure {
        params: vec![("v".to_string(), crate::ir::TrustVcType::Bool)],
        body: Box::new(TrustVcExpr::Var {
            name: "v".to_string(),
            ty: crate::ir::TrustVcType::Bool,
        }),
        ty: crate::ir::TrustVcType::SpecFn(
            vec![crate::ir::TrustVcType::Bool],
            Box::new(crate::ir::TrustVcType::Bool),
        ),
    };

    let expr = TrustVcExpr::CollectionOp {
        op: crate::ir::CollectionOp::MapMapValues,
        receiver: Box::new(receiver),
        receiver_name: None,
        args: vec![closure],
        ty: crate::ir::TrustVcType::Map(
            Box::new(crate::ir::TrustVcType::Int { width: 32 }),
            Box::new(crate::ir::TrustVcType::Bool),
        ),
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "map_values on anonymous Map with key_ty metadata must encode: {:?}",
        result.err()
    );
}
