//! Solver side of the one-goal query API (`crate::query`).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! One query is one fresh solver: symbols and functions are declared,
//! hypotheses are asserted under their own names, the negated goal is
//! asserted, and a single check-sat decides the goal. There is no push/pop,
//! so the unsatisfiable core of a proof is read straight off the solve that
//! produced it.
//!
//! Unsat-core production is not free of side effects in ay: with cores on
//! and any named assertion present, ay's own self-check rejects the proof of
//! simple queries over Bool-valued uninterpreted functions and answers
//! `unknown (self-check-rejected)`; the same query with cores off is proved.
//! When the core-producing solve ends in that rejection, the query is solved
//! again on a fresh solver with cores off and nothing named, and the proof
//! carries no core (`used_hypotheses: None`). Both solves are ay's ordinary
//! checked answers, so the retry cannot turn a wrong goal into a proof.
//!
//! The pieces reused from the rest of the engine are the typed IR encoder
//! (`resolve_condition_typed`, `resolve_refutation_condition_typed`), the
//! resource envelope (`AYEncoder::with_limits`), the panic-safe check-sat
//! envelope with its hang watchdog, unknown classification, ay's model-gate
//! attribution, and counterexample rendering. None of the obligation-stream
//! machinery (`VerificationContext`, the prepared plan, name-keyed lanes) is
//! involved.
//!
//! Every path that is not a definite, validated answer fails closed to
//! `Unknown` or `Error`:
//! * `unsat` becomes `Proved` only if encoding recorded no approximation that
//!   demotes a proof;
//! * `sat` becomes `Refuted` only if ay validated the model and definition
//!   unfolding reached a fixpoint.

use std::collections::HashMap;
use std::panic::AssertUnwindSafe;

use ay_dpll::api::Logic;
use ay_dpll::UnknownReason;

use super::assertion_timeout::run_with_timeout_watchdog;
use super::outcome::AssertionOutcome;
use super::panic::extract_panic_reason;
use super::solve::{
    format_solver_observation_error, model_gate_rejection, solver_unknown_outcome,
    try_check_sat_with_details,
};
#[cfg(not(test))]
use super::timeout::reserve_solver_thread_slot;
use super::timeout::{effective_conflict_budget, far_out_watchdog_timeout};
use super::unknown_category::UnknownCategory;
use crate::counterexample_names::CounterexampleVarMeta;
use crate::encoder::types::sort_for_type;
use crate::encoder::{AYEncoder, VERIFY_STACK_RED_ZONE, VERIFY_STACK_SIZE};
use crate::query::{Limits, ModelEntry, UnfoldedQuery, Verdict};
use crate::solver_budget::ConflictBudget;
use crate::vc::VariableDecl;

/// Memory ceiling handed to `with_limits`, in megabytes; the same figure the
/// obligation-stream path uses.
const QUERY_MEMORY_MB: usize = 512;

/// How a solve asserts its facts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SolveMode {
    /// Unsat cores on, every hypothesis asserted under its own name.
    Cores,
    /// Unsat cores off, nothing named.
    Plain,
}

/// A scalar unfolded query or an independently admitted BV question.
/// Both use precisely the same solver verdict/watchdog/model gate envelope.
#[derive(Clone, Copy)]
enum NativeQuestion<'a> {
    Scalar(&'a UnfoldedQuery),
    Bitvector {
        query: &'a trust_vc_bitvector::Query,
        label: &'a str,
    },
}

impl<'a> NativeQuestion<'a> {
    fn label(self) -> &'a str {
        match self {
            Self::Scalar(query) => &query.label,
            Self::Bitvector { label, .. } => label,
        }
    }
    fn complete(self) -> bool {
        match self {
            Self::Scalar(query) => query.complete,
            Self::Bitvector { .. } => true,
        }
    }
}

/// Solver name of the `index`-th hypothesis.
fn hypothesis_assertion_name(index: usize) -> String {
    format!("qh{index}")
}

fn unknown(reason: impl Into<String>, category: UnknownCategory) -> Verdict {
    Verdict::Unknown {
        reason: reason.into(),
        category,
    }
}

/// Answer one admitted, unfolded query.
pub(crate) fn solve_query(query: &UnfoldedQuery, limits: &Limits) -> Verdict {
    // The encoder recurses over expressions; grow the stack the same way the
    // obligation-stream entry does.
    stacker::maybe_grow(
        VERIFY_STACK_RED_ZONE,
        VERIFY_STACK_SIZE,
        || match std::panic::catch_unwind(AssertUnwindSafe(|| {
            solve_query_inner(NativeQuestion::Scalar(query), limits)
        })) {
            Ok(verdict) => verdict,
            Err(panic) => unknown(
                format!(
                    "panic while solving query '{}': {}",
                    query.label,
                    extract_panic_reason(&*panic)
                ),
                UnknownCategory::SolverPanic,
            ),
        },
    )
}

/// Answer one separately admitted isolated BV question. No scalar hypotheses,
/// functions, definitions or enclosing solver can enter this entry point.
pub(crate) fn solve_bitvector_query(
    query: &trust_vc_bitvector::Query,
    label: &str,
    limits: &Limits,
) -> Verdict {
    stacker::maybe_grow(
        VERIFY_STACK_RED_ZONE,
        VERIFY_STACK_SIZE,
        || match std::panic::catch_unwind(AssertUnwindSafe(|| {
            solve_query_inner(NativeQuestion::Bitvector { query, label }, limits)
        })) {
            Ok(verdict) => verdict,
            Err(panic) => unknown(
                format!(
                    "panic while solving isolated BV query '{label}': {}",
                    extract_panic_reason(&*panic)
                ),
                UnknownCategory::SolverPanic,
            ),
        },
    )
}

fn build(
    question: NativeQuestion<'_>,
    limits: &Limits,
    mode: SolveMode,
) -> Result<(AYEncoder, HashMap<String, String>), String> {
    match question {
        NativeQuestion::Scalar(query) => build_scalar(query, limits, mode),
        NativeQuestion::Bitvector { query, .. } => {
            super::bitvector_query::build(query, limits, mode == SolveMode::Cores)
        }
    }
}

/// Build the solver state for a query: declarations, hypotheses and the
/// negated goal. Returns the encoder and the map from hypothesis solver names
/// back to caller labels (empty in [`SolveMode::Plain`]).
fn build_scalar(
    query: &UnfoldedQuery,
    limits: &Limits,
    mode: SolveMode,
) -> Result<(AYEncoder, HashMap<String, String>), String> {
    let budget = effective_conflict_budget(limits.conflicts.map(ConflictBudget::Bounded));
    let mut encoder =
        AYEncoder::with_logic(Logic::All).with_limits(limits.wall_ms, budget, QUERY_MEMORY_MB);
    if mode == SolveMode::Plain {
        encoder.solver.set_produce_unsat_cores(false);
    }

    for symbol in &query.symbols {
        encoder
            .declare_variable(&VariableDecl::new(symbol.name.clone(), symbol.ty.clone()))
            .map_err(|error| error.to_string())?;
        encoder.counterexample_var_meta.insert(
            symbol.name.clone(),
            CounterexampleVarMeta {
                display_name: symbol.display.clone(),
                visible: true,
            },
        );
    }

    for function in &query.functions {
        let domain: Vec<_> = function.params.iter().map(sort_for_type).collect();
        let decl = encoder
            .solver
            .try_declare_fun(&function.name, &domain, sort_for_type(&function.ret))
            .map_err(|error| format!("declaring function `{}`: {error}", function.name))?;
        encoder.fn_ctx.functions.insert(function.name.clone(), decl);
        encoder
            .fn_ctx
            .return_types
            .insert(function.name.clone(), function.ret.clone());
        encoder
            .fn_ctx
            .param_types
            .insert(function.name.clone(), function.params.clone());
    }

    let mut labels = HashMap::with_capacity(query.hypotheses.len());
    encoder.state.in_assumption_context = true;
    for (index, hypothesis) in query.hypotheses.iter().enumerate() {
        let term = encoder
            .resolve_condition_typed(&hypothesis.expr)
            .map_err(|error| format!("encoding hypothesis `{}`: {error}", hypothesis.label))?;
        let asserted = match mode {
            SolveMode::Cores => {
                let name = hypothesis_assertion_name(index);
                let asserted = encoder.solver.try_assert_named(term, &name);
                labels.insert(name, hypothesis.label.clone());
                asserted
            }
            SolveMode::Plain => encoder.solver.try_assert_term(term),
        };
        asserted
            .map_err(|error| format!("asserting hypothesis `{}`: {error}", hypothesis.label))?;
        encoder.state.assumption_count += 1;
    }
    encoder.state.in_assumption_context = false;

    let negated = encoder
        .resolve_refutation_condition_typed(&query.goal)
        .map_err(|error| format!("encoding the goal: {error}"))?;
    // The negated goal is never named: a core only needs to name the
    // hypotheses, and the goal is in every core by construction.
    encoder
        .solver
        .try_assert_term(negated)
        .map_err(|error| format!("asserting the goal: {error}"))?;
    Ok((encoder, labels))
}

fn solve_query_inner(query: NativeQuestion<'_>, limits: &Limits) -> Verdict {
    match solve_once(query, limits, SolveMode::Cores) {
        Attempt::SelfCheckRejected(_) => match solve_once(query, limits, SolveMode::Plain) {
            Attempt::Done(verdict) | Attempt::SelfCheckRejected(verdict) => verdict,
        },
        Attempt::Done(verdict) => verdict,
    }
}

/// The result of one solve.
enum Attempt {
    Done(Verdict),
    /// ay computed an answer and its own self-check rejected it; the verdict
    /// is the resulting `Unknown`.
    SelfCheckRejected(Verdict),
}

fn solve_once(query: NativeQuestion<'_>, limits: &Limits, mode: SolveMode) -> Attempt {
    let (mut encoder, labels) = match build(query, limits, mode) {
        Ok(built) => built,
        Err(message) => {
            return Attempt::Done(Verdict::Error {
                message: format!("query '{}': {message}", query.label()),
            })
        }
    };

    // ay honours its own wall deadline; the watchdog is hang protection on
    // top of it and fires only well past that deadline.
    #[cfg(not(test))]
    let slot = reserve_solver_thread_slot();
    #[cfg(test)]
    let slot = super::timeout::reserve_solver_thread_slot_for_current_work();
    let interrupt = encoder.interrupt_handle();
    let timeout = far_out_watchdog_timeout(Some(limits.wall_ms));
    let watched = run_with_timeout_watchdog(interrupt, timeout, false, || {
        try_check_sat_with_details(&mut encoder.solver, &mut encoder.state.solver_panic)
    });
    drop(slot);

    let details = match watched.result {
        Ok(Ok(details)) => details,
        Ok(Err(error)) => {
            return Attempt::Done(unknown(
                format_solver_observation_error(
                    format!("ay error checking query '{}'", query.label()),
                    error,
                ),
                UnknownCategory::SolverPanic,
            ))
        }
        Err(panic) => {
            return Attempt::Done(unknown(
                format!(
                    "solver panicked on query '{}': {}",
                    query.label(),
                    extract_panic_reason(&*panic)
                ),
                UnknownCategory::SolverPanic,
            ))
        }
    };

    let result = details.result.result();
    if result.is_unsat() {
        if encoder.state.diagnostics.has_demoting() {
            return Attempt::Done(unknown(
                encoder.state.diagnostics.demotion_reason(query.label()),
                UnknownCategory::EncodingDemotion,
            ));
        }
        let core = match mode {
            SolveMode::Cores => encoder.solver.try_get_unsat_core().ok(),
            SolveMode::Plain => None,
        };
        let used_hypotheses = core.map(|core| {
            let mut used: Vec<String> = core
                .iter()
                .filter_map(|name| labels.get(name).cloned())
                .collect();
            used.sort();
            used.dedup();
            used
        });
        return Attempt::Done(Verdict::Proved { used_hypotheses });
    }

    if result.is_sat() {
        if !details.verification.sat_model_validated {
            return Attempt::Done(unknown(
                format!(
                    "ay did not validate the model for query '{}'",
                    query.label()
                ),
                UnknownCategory::ModelNotValidated,
            ));
        }
        if !query.complete() {
            return Attempt::Done(unknown(
                format!(
                    "query '{}' is satisfiable, but definition unfolding stopped before a \
                     fixpoint, so the model may violate a definition",
                    query.label()
                ),
                UnknownCategory::Incompleteness,
            ));
        }
        let model = match encoder.solver.try_get_model() {
            Ok(model) => model,
            Err(error) => {
                return Attempt::Done(unknown(
                    format!(
                        "ay error reading the model of query '{}': {error}",
                        query.label()
                    ),
                    UnknownCategory::SolverUnknown,
                ))
            }
        };
        let bindings = super::model_render::collect_counterexample_bindings(
            &model,
            &encoder.var_types,
            &encoder.counterexample_var_meta,
        );
        return Attempt::Done(Verdict::Refuted {
            model: bindings
                .into_iter()
                .map(|binding| ModelEntry {
                    name: binding.display_name,
                    symbol: binding.raw_name,
                    value: binding.value,
                })
                .collect(),
        });
    }

    if watched.timed_out {
        return Attempt::Done(unknown(
            format!(
                "query '{}' hit the hang watchdog after {} ms",
                query.label(),
                timeout.as_millis()
            ),
            UnknownCategory::Timeout,
        ));
    }
    let gate = model_gate_rejection(&details);
    let verdict =
        match solver_unknown_outcome(query.label(), None, details.unknown_reason, gate.as_ref()) {
            AssertionOutcome::Unknown {
                reason, category, ..
            } => unknown(reason, category.unwrap_or(UnknownCategory::SolverUnknown)),
            other => unknown(
                format!(
                    "unexpected solver outcome for query '{}': {other:?}",
                    query.label()
                ),
                UnknownCategory::SolverUnknown,
            ),
        };
    if details.unknown_reason == Some(UnknownReason::SelfCheckRejected) {
        Attempt::SelfCheckRejected(verdict)
    } else {
        Attempt::Done(verdict)
    }
}
