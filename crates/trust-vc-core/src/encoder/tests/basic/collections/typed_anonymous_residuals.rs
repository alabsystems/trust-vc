//! Residual typed-anonymous collection regressions for #2371.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

#[test]
fn test_contains_on_typed_anonymous_map_receiver_fails_closed_with_map_guidance() {
    use crate::ir_expr::TrustVcExpr;
    use ay_dpll::api::{ArraySort, Sort};

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let mut functions = std::collections::HashMap::new();

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
    let expr = TrustVcExpr::CollectionOp {
        op: crate::ir::CollectionOp::Contains,
        receiver: Box::new(TrustVcExpr::FnCall {
            name: "mk_map".to_string(),
            args: vec![],
            return_ty: crate::ir::TrustVcType::Map(
                Box::new(crate::ir::TrustVcType::Int { width: 32 }),
                Box::new(crate::ir::TrustVcType::Bool),
            ),
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
                message.to_string().contains("Map::contains() does not exist"),
                "typed anonymous Map receiver should infer Map kind and fail closed with contains_key guidance, got: {}",
                message
            );
        }
        Ok(_) => panic!(
            "typed anonymous Map receiver should fail closed with Map-specific guidance instead of encoding as Set/Seq"
        ),
    }
}

#[test]
fn test_contains_on_non_collection_receiver_fails_closed_with_known_type_error() {
    use crate::ir_expr::TrustVcExpr;

    let mut solver = Solver::try_new(Logic::All).unwrap();
    let variables = std::collections::HashMap::new();
    let mut collection_lengths = std::collections::HashMap::new();
    let var_types = std::collections::HashMap::new();
    let functions = std::collections::HashMap::new();

    let mut parser = AstExpressionParser::new(
        &mut solver,
        &variables,
        &mut collection_lengths,
        &var_types,
        &functions,
    );
    let expr = TrustVcExpr::CollectionOp {
        op: crate::ir::CollectionOp::Contains,
        receiver: Box::new(TrustVcExpr::IntLit {
            value: 7,
            ty: crate::ir::TrustVcType::Int { width: 32 },
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
                    .contains("contains() requires a receiver with known collection type"),
                "non-collection receiver should hit the typed_collection_meta fallback error, got: {}",
                message
            );
        }
        Ok(_) => panic!(
            "non-collection receiver should fail closed instead of encoding as an anonymous collection"
        ),
    }
}
