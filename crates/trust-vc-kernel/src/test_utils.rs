// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared test helpers for proof-trace construction.
//!
//! Used by both `tests` and `bench_tests` modules to avoid duplicating
//! the `Clause` / `ResolutionStep` / `ProofTrace` builder shorthands.

use crate::types::{Clause, ProofTrace, ResolutionStep};

/// Shorthand: create a `Clause` with the given id and literal slice.
pub(crate) fn cl(id: u64, lits: &[i64]) -> Clause {
    Clause {
        id,
        literals: lits.to_vec(),
    }
}

/// Shorthand: create a `ResolutionStep` with no declared resolvent.
pub(crate) fn rs(id: u64, pivot: i64, p1: u64, p2: u64) -> ResolutionStep {
    ResolutionStep {
        id,
        pivot,
        parent1: p1,
        parent2: p2,
        result_literals: None,
    }
}

/// Shorthand: create a `ProofTrace` with no theory lemmas.
pub(crate) fn trace(inputs: Vec<Clause>, steps: Vec<ResolutionStep>, empty: u64) -> ProofTrace {
    ProofTrace {
        input_clauses: inputs,
        resolution_steps: steps,
        theory_lemmas: vec![],
        empty_clause_id: empty,
    }
}
