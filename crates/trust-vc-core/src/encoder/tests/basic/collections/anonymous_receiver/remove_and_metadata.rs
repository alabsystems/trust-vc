// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Contains_key and remove tests for anonymous receivers: Map contains_key,
//! Set remove, Map remove, and named Map source-term metadata preservation.

use super::*;

fn encode_contains_key_on_anonymous_map_with_term_meta() -> Result<(), String> {
    use crate::encoder::parser_state::{CollectionKind, CollectionMeta};
    use crate::ir_expr::TrustVcExpr;
    use ay_dpll::api::{ArraySort, Sort};

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let mut functions = std::collections::HashMap::new();
    let pw = crate::ir::pointer_width();

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
    let len_term = parser.solver.fresh_var("__anon_map_len", Sort::bitvec(pw));
    let dom_term = parser.solver.fresh_var(
        "__anon_map_dom",
        Sort::Array(Box::new(ArraySort {
            index_sort: Sort::bitvec(32),
            element_sort: Sort::Bool,
        })),
    );
    parser.register_collection_meta(
        receiver_term,
        CollectionMeta {
            kind: CollectionKind::Map,
            len_term: Some(len_term),
            len_guard: None,
            elem_ty: Some(crate::ir::TrustVcType::Bool),
            key_ty: None,
            dom_term: Some(dom_term),
        },
    );

    let expr = TrustVcExpr::CollectionOp {
        op: crate::ir::CollectionOp::ContainsKey,
        receiver: Box::new(receiver),
        receiver_name: None,
        args: vec![TrustVcExpr::IntLit {
            value: 5,
            ty: crate::ir::TrustVcType::Int { width: 32 },
        }],
        ty: crate::ir::TrustVcType::Bool,
    };

    parser
        .encode_trust_vc_expr(&expr)
        .map(|_| ())
        .map_err(|e| e.to_string())
}

#[test]
fn test_contains_key_on_anonymous_map_uses_term_keyed_domain_metadata() {
    if let Err(message) = encode_contains_key_on_anonymous_map_with_term_meta() {
        panic!(
            "anonymous Map receiver should use registered dom metadata for contains_key(), got: {}",
            message
        );
    }
}

fn encode_remove_on_anonymous_set_with_term_meta() -> Result<(), String> {
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
        .try_declare_fun("mk_set", &[], set_sort)
        .expect("declare mk_set");
    functions.insert("mk_set".to_string(), mk_set);

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    let receiver = TrustVcExpr::FnCall {
        name: "mk_set".to_string(),
        args: vec![],
        return_ty: crate::ir::TrustVcType::Set(Box::new(crate::ir::TrustVcType::Int { width: 32 })),
    };
    let receiver_term = parser
        .encode_trust_vc_expr(&receiver)
        .expect("encode anonymous set receiver");
    let len_term = parser.solver.fresh_var("__anon_set_len", Sort::bitvec(pw));
    parser.register_collection_meta(
        receiver_term,
        CollectionMeta {
            kind: CollectionKind::Set,
            len_term: Some(len_term),
            len_guard: None,
            elem_ty: Some(crate::ir::TrustVcType::Int { width: 32 }),
            key_ty: None,
            dom_term: None,
        },
    );

    let expr = TrustVcExpr::CollectionOp {
        op: crate::ir::CollectionOp::Remove,
        receiver: Box::new(receiver),
        receiver_name: None,
        args: vec![TrustVcExpr::IntLit {
            value: 5,
            ty: crate::ir::TrustVcType::Int { width: 32 },
        }],
        ty: crate::ir::TrustVcType::Set(Box::new(crate::ir::TrustVcType::Int { width: 32 })),
    };

    parser
        .encode_trust_vc_expr(&expr)
        .map(|_| ())
        .map_err(|e| e.to_string())
}

#[test]
fn test_remove_on_anonymous_set_uses_term_keyed_kind_metadata() {
    if let Err(message) = encode_remove_on_anonymous_set_with_term_meta() {
        panic!(
            "anonymous Set receiver should use registered kind metadata for remove(), got: {}",
            message
        );
    }
}

fn encode_remove_on_anonymous_map_with_term_meta() -> Result<(), String> {
    use crate::encoder::parser_state::{CollectionKind, CollectionMeta};
    use crate::ir_expr::TrustVcExpr;
    use ay_dpll::api::{ArraySort, Sort};

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let mut functions = std::collections::HashMap::new();
    let pw = crate::ir::pointer_width();

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
    let len_term = parser
        .solver
        .fresh_var("__anon_map_remove_len", Sort::bitvec(pw));
    let dom_term = parser.solver.fresh_var(
        "__anon_map_remove_dom",
        Sort::Array(Box::new(ArraySort {
            index_sort: Sort::bitvec(32),
            element_sort: Sort::Bool,
        })),
    );
    parser.register_collection_meta(
        receiver_term,
        CollectionMeta {
            kind: CollectionKind::Map,
            len_term: Some(len_term),
            len_guard: None,
            elem_ty: Some(crate::ir::TrustVcType::Bool),
            key_ty: None,
            dom_term: Some(dom_term),
        },
    );

    let expr = TrustVcExpr::CollectionOp {
        op: crate::ir::CollectionOp::Remove,
        receiver: Box::new(receiver),
        receiver_name: None,
        args: vec![TrustVcExpr::IntLit {
            value: 5,
            ty: crate::ir::TrustVcType::Int { width: 32 },
        }],
        ty: crate::ir::TrustVcType::Map(
            Box::new(crate::ir::TrustVcType::Int { width: 32 }),
            Box::new(crate::ir::TrustVcType::Bool),
        ),
    };

    parser
        .encode_trust_vc_expr(&expr)
        .map(|_| ())
        .map_err(|e| e.to_string())
}

#[test]
fn test_remove_on_anonymous_map_uses_term_keyed_domain_metadata() {
    if let Err(message) = encode_remove_on_anonymous_map_with_term_meta() {
        panic!(
            "anonymous Map receiver should use registered dom metadata for remove(), got: {}",
            message
        );
    }
}

fn encode_remove_on_named_map_preserves_source_term_metadata() -> Result<(), String> {
    use crate::ir_expr::TrustVcExpr;
    use ay_dpll::api::{ArraySort, Sort};

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let mut variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let mut var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();
    let pw = crate::ir::pointer_width();
    let map_ty = crate::ir::TrustVcType::Map(
        Box::new(crate::ir::TrustVcType::Int { width: 32 }),
        Box::new(crate::ir::TrustVcType::Bool),
    );
    let map_sort = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::bitvec(32),
        element_sort: Sort::Bool,
    }));
    let receiver_term = solver.fresh_var("m", map_sort);
    let original_len = solver.fresh_var("__named_map_len", Sort::bitvec(pw));
    let original_dom = solver.fresh_var(
        "__named_map_dom",
        Sort::Array(Box::new(ArraySort {
            index_sort: Sort::bitvec(32),
            element_sort: Sort::Bool,
        })),
    );
    variables.insert("m".to_string(), receiver_term);
    variables.insert("m_dom".to_string(), original_dom);
    collection_lengths.insert("m".to_string(), original_len);
    var_types.insert("m".to_string(), map_ty.clone());

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    let expr = TrustVcExpr::CollectionOp {
        op: crate::ir::CollectionOp::Remove,
        receiver: Box::new(TrustVcExpr::Var {
            name: "m".to_string(),
            ty: map_ty.clone(),
        }),
        receiver_name: Some("m".to_string()),
        args: vec![TrustVcExpr::IntLit {
            value: 5,
            ty: crate::ir::TrustVcType::Int { width: 32 },
        }],
        ty: map_ty,
    };

    let result_term = parser
        .encode_trust_vc_expr(&expr)
        .map_err(|e| e.to_string())?;
    let updated_len = parser
        .collection_lengths
        .get("m")
        .copied()
        .expect("named receiver length should update after remove");
    let updated_dom = parser
        .domain_terms
        .get("m_dom")
        .copied()
        .expect("named receiver dom should update after remove");

    assert_ne!(
        result_term, receiver_term,
        "Map::remove should return a fresh result term instead of aliasing the source receiver"
    );
    assert_ne!(
        updated_len, original_len,
        "Map::remove should publish a new length term for the result metadata"
    );
    assert_ne!(
        updated_dom, original_dom,
        "Map::remove should publish a new domain term for the result metadata"
    );
    assert_eq!(
        parser.lookup_collection_len(receiver_term, Some("m")),
        Some(original_len),
        "source receiver should keep its original term-keyed length metadata"
    );
    assert_eq!(
        parser.lookup_collection_dom(receiver_term, Some("m")),
        Some(original_dom),
        "source receiver should keep its original term-keyed domain metadata"
    );
    assert_eq!(
        parser.lookup_collection_len(result_term, Some("m")),
        Some(updated_len),
        "remove result should resolve the updated length metadata"
    );
    assert_eq!(
        parser.lookup_collection_dom(result_term, Some("m")),
        Some(updated_dom),
        "remove result should resolve the updated domain metadata"
    );
    Ok(())
}

#[test]
fn test_remove_on_named_map_keeps_source_term_metadata() {
    if let Err(message) = encode_remove_on_named_map_preserves_source_term_metadata() {
        panic!(
            "named Map receiver should preserve source metadata and isolate remove() result metadata, got: {}",
            message
        );
    }
}
