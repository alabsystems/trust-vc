//! Proof-body mutable-reference rewriting for `#[trust_vc::proof]`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Supports a narrow proof-only `&mut` subset by rewriting `*x` reads on
//! supported `&mut` parameters into SSA-style shadow values. Direct top-level
//! stores `*x = expr;` advance the shadow version while keeping the runtime
//! store in place. General dereference lowering remains fail-closed.

use std::collections::{BTreeMap, BTreeSet};

use proc_macro2::TokenStream;
use syn::{Block, FnArg, Ident, Pat, Signature, Type};

#[path = "mut_ref_proof_helpers.rs"]
mod helpers;

#[path = "mut_ref_proof_rewriter.rs"]
mod rewriter;
use rewriter::MutRefRewriter;

#[cfg(test)]
#[path = "mut_ref_proof_tests.rs"]
mod soundness_tests;

#[cfg(test)]
#[path = "mut_ref_proof_unit_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "mut_ref_proof_rewriter_tests.rs"]
mod rewriter_tests;

pub(crate) struct MutRefProofTransform {
    pub(crate) transformed_block: Block,
    pub(crate) skipped_params: BTreeSet<String>,
    pub(crate) errors: Vec<TokenStream>,
}

#[derive(Clone)]
struct MutRefParam {
    ident: Ident,
    referent_ty: Type,
}

pub(crate) fn transform_proof_body(sig: &Signature, block: &Block) -> MutRefProofTransform {
    let mut params = BTreeMap::new();
    let mut skipped_params = BTreeSet::new();
    let mut errors = Vec::new();

    for input in &sig.inputs {
        let FnArg::Typed(pat_type) = input else {
            continue;
        };
        let Pat::Ident(pat_ident) = pat_type.pat.as_ref() else {
            continue;
        };
        let Type::Reference(type_ref) = pat_type.ty.as_ref() else {
            continue;
        };
        if type_ref.mutability.is_none() {
            continue;
        }

        let param_name = pat_ident.ident.to_string();
        skipped_params.insert(param_name.clone());

        params.insert(
            param_name,
            MutRefParam {
                ident: pat_ident.ident.clone(),
                referent_ty: (*type_ref.elem).clone(),
            },
        );
    }

    if params.is_empty() {
        return MutRefProofTransform {
            transformed_block: block.clone(),
            skipped_params,
            errors,
        };
    }

    let mut rewriter = MutRefRewriter {
        params,
        place_versions: BTreeMap::new(),
        used_places: BTreeMap::new(),
        nested_block_depth: 0,
        control_flow_depth: 0,
        errors: Vec::new(),
    };
    let mut transformed_block = rewriter.rewrite_block(block.clone());
    transformed_block
        .stmts
        .splice(0..0, rewriter.entry_statements());
    errors.extend(
        rewriter
            .errors
            .into_iter()
            .map(|err| err.to_compile_error()),
    );

    MutRefProofTransform {
        transformed_block,
        skipped_params,
        errors,
    }
}
