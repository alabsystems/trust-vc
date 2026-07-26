//! Termination proof support: decreases measures, when/via clauses.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Handles `#[decreases]` attribute expansion including lexicographic measures,
//! conditional (`when`) and delegated (`via`) termination proofs, and
//! `#[via_fn]` proof functions.
//!
//! Submodules:
//! - `clause`: attribute token parsing for when/via clauses
//! - `transform`: recursive-call scan and decrease obligation injection
//! - `expand`: proc-macro expansion entrypoints

mod clause;
mod expand;
mod measure_shape;
mod transform;

pub use expand::{expand_decreases, expand_decreases_with_clauses, expand_via_fn};

/// Parses the measure expression(s) out of a `#[decreases(...)]` attribute's
/// token stream, discarding any `when`/`via`/`mutual_with` clauses.
///
/// Used by the source spec-function catalog's termination gate
/// (`spec_function_catalog`) to recover the declared measure for a recursive
/// spec function so it can prove (not merely assume) that the measure strictly
/// decreases before trusting the function's defining axiom.
pub(crate) fn parse_measure_exprs(tokens: proc_macro2::TokenStream) -> syn::Result<Vec<syn::Expr>> {
    use syn::parse::Parser;
    let clause = clause::parse_decreases_clauses(tokens);
    let parser = syn::punctuated::Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated;
    Ok(parser.parse2(clause.measures)?.into_iter().collect())
}
