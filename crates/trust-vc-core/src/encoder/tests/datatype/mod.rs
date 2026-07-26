// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// Tests for builtin datatype UF encoding (#1942 Slice 2).

use super::*;
use crate::encoder::datatype::ConstructorKind;
use crate::ir::TrustVcType;

mod error_paths;
mod recursive_size_usage;
mod recursive_well_foundedness;
mod registration_axioms;
mod sort_builder;

fn option_u64_components() -> (String, Vec<crate::ir::DatatypeVariant>) {
    let option = TrustVcType::from_str("Option<u64>").expect("Option<u64> should parse");
    let TrustVcType::Datatype { name, variants } = option else {
        panic!("Option<u64> should lower to TrustVcType::Datatype");
    };
    (name, variants)
}

fn result_u64_bool_components() -> (String, Vec<crate::ir::DatatypeVariant>) {
    let result =
        TrustVcType::from_str("Result<u64, bool>").expect("Result<u64, bool> should parse");
    let TrustVcType::Datatype { name, variants } = result else {
        panic!("Result<u64, bool> should lower to TrustVcType::Datatype");
    };
    (name, variants)
}

fn list_i32_components() -> (String, Vec<crate::ir::DatatypeVariant>) {
    let name = "List_i32".to_string();
    let variants = vec![
        crate::ir::DatatypeVariant::new("Nil", vec![]),
        crate::ir::DatatypeVariant::new(
            "Cons",
            vec![
                ("head".into(), TrustVcType::Int { width: 32 }),
                ("tail".into(), TrustVcType::RecursiveRef("List_i32".into())),
            ],
        ),
    ];
    (name, variants)
}

fn tree_i32_components() -> (String, Vec<crate::ir::DatatypeVariant>) {
    let name = "Tree_i32".to_string();
    let variants = vec![
        crate::ir::DatatypeVariant::new(
            "Leaf",
            vec![("val".into(), TrustVcType::Int { width: 32 })],
        ),
        crate::ir::DatatypeVariant::new(
            "Branch",
            vec![
                ("left".into(), TrustVcType::RecursiveRef("Tree_i32".into())),
                ("right".into(), TrustVcType::RecursiveRef("Tree_i32".into())),
            ],
        ),
    ];
    (name, variants)
}

fn ill_founded_recursive_components() -> (String, Vec<crate::ir::DatatypeVariant>) {
    let name = "Bad".to_string();
    let variants = vec![
        crate::ir::DatatypeVariant::new(
            "Node",
            vec![("next".into(), TrustVcType::RecursiveRef("Bad".into()))],
        ),
        crate::ir::DatatypeVariant::new(
            "Alias",
            vec![("rest".into(), TrustVcType::RecursiveRef("Bad".into()))],
        ),
    ];
    (name, variants)
}
