//! Scoped quantifier metadata for explicit arithmetic semantics.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{HashMap, HashSet};

use crate::ir::TrustVcType;
use ay_dpll::api::Term;

use super::arith_semantics::ArithSemantics;

/// Explicit quantifier scope metadata keyed by bound variable identity.
///
/// The IR encoder resolves arithmetic semantics from this scope stack
/// via `AstExpressionParser::current_quantifier_wrap_semantics()`.
#[derive(Debug, Clone, Default)]
pub(super) struct QuantifierScope {
    pub(super) bound_int_types: HashMap<String, TrustVcType>,
    /// ay Terms for quantifier-bound variables in this scope.
    /// Used by `add_seq_index_bounds_check` to distinguish bound-variable
    /// indices (skip check — user guards handle OOB) from constant/free
    /// indices (check — no guard protects them). See #2231 Finding 1.
    pub(super) bound_terms: HashSet<Term>,
}

impl QuantifierScope {
    /// Build scope metadata from quantifier bound variables.
    pub(super) fn from_bound_vars(bound_vars: &[(String, TrustVcType)]) -> Self {
        let mut bound_int_types = HashMap::new();
        for (name, ty) in bound_vars {
            if let Some(width) = ty.bit_width() {
                if width > 0 {
                    bound_int_types.insert(name.clone(), ty.clone());
                }
            }
        }
        Self {
            bound_int_types,
            bound_terms: HashSet::new(),
        }
    }

    /// Register a ay Term as a quantifier-bound variable in this scope.
    pub(super) fn add_bound_term(&mut self, term: Term) {
        self.bound_terms.insert(term);
    }

    /// Compute wrapping semantics for this scope.
    ///
    /// Uses widest width across integer vars; signed unless all are unsigned.
    /// The widest width matches Rust's type promotion rules: narrower types
    /// are promoted to wider ones before arithmetic. (#1794)
    pub(super) fn wrap_semantics(&self) -> Option<ArithSemantics> {
        let mut widest_width: Option<u32> = None;
        let mut all_unsigned = true;

        for ty in self.bound_int_types.values() {
            if let Some(width) = ty.bit_width() {
                if width > 0 {
                    widest_width = Some(match widest_width {
                        Some(existing) => existing.max(width),
                        None => width,
                    });
                    if !ty.is_unsigned() {
                        all_unsigned = false;
                    }
                }
            }
        }

        widest_width.map(|width| ArithSemantics {
            width,
            is_unsigned: all_unsigned,
        })
    }
}
