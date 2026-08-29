//! Trait encoding regression tests.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::ir::{TraitBound, TraitDecl, TraitImplDecl, TraitMethodDecl, TrustVcType};
use ay_dpll::api::Sort;

mod impl_linking;
mod negative_and_defaults;
mod registration_and_axioms;

// Shared trait declaration helpers used across submodules.

fn counter_trait_decl() -> TraitDecl {
    TraitDecl {
        name: "CounterSpec".to_string(),
        methods: vec![
            TraitMethodDecl {
                name: "value".to_string(),
                params: vec![],
                return_type: TrustVcType::Bool,
                requires: vec![],
                ensures: vec![],
                has_default: false,
                default_body: None,
                default_ensures: Vec::new(),
            },
            TraitMethodDecl {
                name: "grant".to_string(),
                params: vec![("token".to_string(), TrustVcType::Bool)],
                return_type: TrustVcType::Bool,
                requires: vec!["self.value() && token".to_string()],
                ensures: vec!["result".to_string()],
                has_default: false,
                default_body: None,
                default_ensures: Vec::new(),
            },
        ],
        supertraits: Vec::new(),
        generics: Vec::new(),
    }
}

fn simple_trait_decl() -> TraitDecl {
    TraitDecl {
        name: "Valued".to_string(),
        methods: vec![TraitMethodDecl {
            name: "get_value".to_string(),
            params: vec![],
            return_type: TrustVcType::Bool,
            requires: vec![],
            ensures: vec!["result".to_string()],
            has_default: false,
            default_body: None,
            default_ensures: Vec::new(),
        }],
        supertraits: Vec::new(),
        generics: Vec::new(),
    }
}

fn simple_impl_decl() -> TraitImplDecl {
    TraitImplDecl {
        inherent_shadowed_methods: Default::default(),
        trait_name: "Valued".to_string(),
        concrete_type: TrustVcType::Bool,
        method_bindings: vec![("get_value".to_string(), "BoolImpl__get_value".to_string())],
        assoc_type_bindings: Vec::new(),
        is_external: false,
        trait_type_args: Vec::new(),
    }
}

/// Trait with a required method (with postcondition) and a default method
/// whose body calls the required method.
///
/// `label` has `ensures: ["result"]` so its postcondition axiom operates at
/// the Poly level where ay-dpll E-matching fires. The default body of
/// `is_labeled` is `self.label()`, which also stays at the Poly level.
fn trait_with_default() -> TraitDecl {
    TraitDecl {
        name: "Describable".to_string(),
        methods: vec![
            TraitMethodDecl {
                name: "label".to_string(),
                params: vec![],
                return_type: TrustVcType::Bool,
                requires: vec![],
                ensures: vec!["result".to_string()],
                has_default: false,
                default_body: None,
                default_ensures: Vec::new(),
            },
            TraitMethodDecl {
                name: "is_labeled".to_string(),
                params: vec![],
                return_type: TrustVcType::Bool,
                requires: vec![],
                ensures: vec![],
                has_default: true,
                default_body: Some("self.label()".to_string()),
                default_ensures: Vec::new(),
            },
        ],
        supertraits: Vec::new(),
        generics: Vec::new(),
    }
}
