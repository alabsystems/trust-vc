// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Contains tests for anonymous receivers: Set, u64 Set, Multiset, Seq,
//! and Seq-to-Set derived view provenance.

use super::*;

#[test]
fn test_contains_on_typed_anonymous_set_receiver_uses_set_semantics() {
    use crate::ir_expr::TrustVcExpr;
    use ay_dpll::api::{ArraySort, Sort};

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let mut functions = std::collections::HashMap::new();

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
    let expr = TrustVcExpr::CollectionOp {
        op: crate::ir::CollectionOp::Contains,
        receiver: Box::new(TrustVcExpr::FnCall {
            name: "mk_set".to_string(),
            args: vec![],
            return_ty: crate::ir::TrustVcType::Set(Box::new(crate::ir::TrustVcType::Int {
                width: 32,
            })),
        }),
        receiver_name: None,
        args: vec![TrustVcExpr::IntLit {
            value: 5,
            ty: crate::ir::TrustVcType::Int { width: 32 },
        }],
        ty: crate::ir::TrustVcType::Bool,
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "typed anonymous Set receiver should use Set semantics instead of unknown-type error: {:?}",
        result.err()
    );
}

#[test]
fn test_contains_on_typed_anonymous_u64_set_receiver_coerces_literal_width() {
    use crate::ir_expr::TrustVcExpr;
    use ay_dpll::api::{ArraySort, Sort};

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let mut functions = std::collections::HashMap::new();

    let set_sort = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::bitvec(64),
        element_sort: Sort::Bool,
    }));
    let mk_u64_set = solver
        .try_declare_fun("mk_u64_set", &[], set_sort)
        .expect("declare mk_u64_set");
    functions.insert("mk_u64_set".to_string(), mk_u64_set);

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    let expr = TrustVcExpr::CollectionOp {
        op: crate::ir::CollectionOp::Contains,
        receiver: Box::new(TrustVcExpr::FnCall {
            name: "mk_u64_set".to_string(),
            args: vec![],
            return_ty: crate::ir::TrustVcType::Set(Box::new(crate::ir::TrustVcType::Uint {
                width: 64,
            })),
        }),
        receiver_name: None,
        args: vec![TrustVcExpr::IntLit {
            value: 5,
            ty: crate::ir::TrustVcType::Int { width: 32 },
        }],
        ty: crate::ir::TrustVcType::Bool,
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "typed anonymous Set<u64> receiver should widen default-width literals instead of producing a sort mismatch: {:?}",
        result.err()
    );
}

#[test]
fn test_contains_on_typed_anonymous_multiset_receiver_uses_count_semantics() {
    use crate::ir_expr::TrustVcExpr;
    use ay_dpll::api::{ArraySort, Sort};

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let mut functions = std::collections::HashMap::new();

    let multiset_sort = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::bitvec(32),
        element_sort: Sort::Int,
    }));
    let mk_multiset = solver
        .try_declare_fun("mk_multiset", &[], multiset_sort)
        .expect("declare mk_multiset");
    functions.insert("mk_multiset".to_string(), mk_multiset);

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    let expr = TrustVcExpr::CollectionOp {
        op: crate::ir::CollectionOp::Contains,
        receiver: Box::new(TrustVcExpr::FnCall {
            name: "mk_multiset".to_string(),
            args: vec![],
            return_ty: crate::ir::TrustVcType::Multiset(Box::new(crate::ir::TrustVcType::Int {
                width: 32,
            })),
        }),
        receiver_name: None,
        args: vec![TrustVcExpr::IntLit {
            value: 5,
            ty: crate::ir::TrustVcType::Int { width: 32 },
        }],
        ty: crate::ir::TrustVcType::Bool,
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "typed anonymous Multiset receiver should use count>0 semantics instead of unknown-type error: {:?}",
        result.err()
    );
}

#[test]
fn test_contains_on_typed_anonymous_seq_receiver_fails_closed_without_length_tracking() {
    use crate::ir_expr::TrustVcExpr;
    use ay_dpll::api::{ArraySort, Sort};

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let mut functions = std::collections::HashMap::new();
    let pw = crate::ir::pointer_width();

    let seq_sort = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::bitvec(pw),
        element_sort: Sort::bitvec(32),
    }));
    let mk_seq = solver
        .try_declare_fun("mk_seq", &[], seq_sort)
        .expect("declare mk_seq");
    functions.insert("mk_seq".to_string(), mk_seq);

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    let expr = TrustVcExpr::CollectionOp {
        op: crate::ir::CollectionOp::Contains,
        receiver: Box::new(TrustVcExpr::FnCall {
            name: "mk_seq".to_string(),
            args: vec![],
            return_ty: crate::ir::TrustVcType::Seq(Box::new(crate::ir::TrustVcType::Int {
                width: 32,
            })),
        }),
        receiver_name: None,
        args: vec![TrustVcExpr::IntLit {
            value: 5,
            ty: crate::ir::TrustVcType::Int { width: 32 },
        }],
        ty: crate::ir::TrustVcType::Bool,
    };

    let result = parser.encode_trust_vc_expr(&expr);
    match result {
        Err(message) => {
            assert!(
                message
                    .to_string()
                    .contains("No length tracking for Seq '<anonymous>' in contains()"),
                "typed anonymous Seq receiver should fail closed with missing-length error, got: {}",
                message
            );
        }
        Ok(_) => {
            panic!("typed anonymous Seq receiver should fail closed instead of using Set semantics")
        }
    }
}

#[test]
fn test_contains_on_anonymous_seq_to_set_receiver_uses_derived_view_provenance() {
    use crate::encoder::parser_state::{CollectionKind, CollectionMeta};
    use crate::ir_expr::TrustVcExpr;
    use ay_dpll::api::{ArraySort, Sort};

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let mut functions = std::collections::HashMap::new();
    let pw = crate::ir::pointer_width();

    let seq_sort = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::bitvec(pw),
        element_sort: Sort::bitvec(32),
    }));
    let mk_seq = solver
        .try_declare_fun("mk_seq_with_meta", &[], seq_sort)
        .expect("declare mk_seq_with_meta");
    functions.insert("mk_seq_with_meta".to_string(), mk_seq);

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    let receiver = TrustVcExpr::FnCall {
        name: "mk_seq_with_meta".to_string(),
        args: vec![],
        return_ty: crate::ir::TrustVcType::Seq(Box::new(crate::ir::TrustVcType::Int { width: 32 })),
    };
    let receiver_term = parser
        .encode_trust_vc_expr(&receiver)
        .expect("encode anonymous seq receiver");
    let len_term = parser.solver.fresh_var("__anon_seq_len", Sort::bitvec(pw));
    parser.register_collection_meta(
        receiver_term,
        CollectionMeta {
            kind: CollectionKind::Seq,
            len_term: Some(len_term),
            len_guard: None,
            elem_ty: Some(crate::ir::TrustVcType::Int { width: 32 }),
            key_ty: None,
            dom_term: None,
        },
    );

    let expr = TrustVcExpr::CollectionOp {
        op: crate::ir::CollectionOp::Contains,
        receiver: Box::new(TrustVcExpr::CollectionOp {
            op: crate::ir::CollectionOp::ToSet,
            receiver: Box::new(receiver),
            receiver_name: None,
            args: vec![],
            ty: crate::ir::TrustVcType::Set(Box::new(crate::ir::TrustVcType::Int { width: 32 })),
        }),
        receiver_name: None,
        args: vec![TrustVcExpr::IntLit {
            value: 5,
            ty: crate::ir::TrustVcType::Int { width: 32 },
        }],
        ty: crate::ir::TrustVcType::Bool,
    };

    let result = parser.encode_trust_vc_expr(&expr);
    assert!(
        result.is_ok(),
        "anonymous seq.to_set().contains(...) should resolve through term-keyed derived-view provenance: {:?}",
        result.err()
    );
}
