//! Decreases measure collection and obligation construction.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Extracted from decreases_runtime.rs as part of #2010.
//! Contains the two public collection entrypoints and internal obligation helpers.

use crate::obligation_collection::record_obligation_drop;
use crate::proof_session::try_with_session_mut;
use crate::type_syntax::parse_tuple_expr_components;
use crate::vc::{ProofObligation, VerificationContext};

use super::measure_types::{infer_measure_type, is_valid_measure_component, sanitize_measure_name};

/// Collects a decreases measure for termination verification.
///
/// This is called by the expanded `#[decreases]` macro to record the
/// termination measure expression at function entry. Only adds
/// `MeasureNonNegative` obligations — the decrease check for recursive
/// functions is handled separately by `verify_decreases` or
/// `collect_decrease_obligation`.
///
/// For loop termination with automatic decrease checking, use
/// `collect_loop_decreases_measure` instead.
pub fn collect_decreases_measure(measure: String, _location: Option<String>) {
    // Borrow conflicts must fail closed — otherwise termination measures
    // disappear silently from the verification context. Part of #2360.
    match try_with_session_mut(|s| {
        let context = s.context.get_or_insert_with(VerificationContext::new);

        // Check if this is a lexicographic (tuple) measure
        let trimmed = measure.trim();
        let tuple_components = if trimmed.starts_with('(') && trimmed.ends_with(')') {
            match parse_tuple_expr_components(trimmed) {
                Ok(components) => components,
                Err(_) => return,
            }
        } else {
            None
        };

        if let Some(components) = tuple_components {
            let components: Vec<String> =
                components.into_iter().filter(|s| !s.is_empty()).collect();

            // Validate all components before adding any obligations. Part of #1955.
            if components.is_empty() || components.iter().any(|c| !is_valid_measure_component(c)) {
                return;
            }

            for component in &components {
                context.add_measure_nonneg(component);
            }
        } else {
            // Single measure - validate before adding
            let single = trimmed.to_string();
            // Invalid measure — skip gracefully. Part of #1955.
            if single.is_empty() || !is_valid_measure_component(&single) {
                return;
            }
            context.add_measure_nonneg(&single);
        }
    }) {
        Ok(()) => {}
        Err(_) => record_obligation_drop(),
    }
}

/// Collects a loop decreases measure with automatic decrease checking.
///
/// Unlike `collect_decreases_measure` (for `#[decreases]` on functions),
/// this adds both non-negativity AND decrease obligations. For each measure
/// component, it generates:
///
/// 1. `MeasureNonNegative`: `measure >= 0`
/// 2. Entry variable: `{measure}_entry` (same type as measure variable)
/// 3. Entry assumption: `{measure}_entry >= 0`
/// 4. `MeasureDecreases`: `measure < {measure}_entry` (strict decrease)
///
/// The entry variable represents the measure value at the start of the
/// previous iteration. The decrease obligation ensures the measure
/// strictly decreases each iteration, proving loop termination.
///
/// Called by the `loop_decreases!` macro expansion.
pub fn collect_loop_decreases_measure(measure: String, location: Option<String>) {
    // Borrow conflicts must fail closed — otherwise loop termination
    // obligations disappear silently from the verification context.
    // Part of #2360.
    match try_with_session_mut(|s| {
        let context = s.context.get_or_insert_with(VerificationContext::new);
        // The runtime path DELIBERATELY ignores the returned binding and any
        // `LoopDecreaseBuildError`: an invalid or type-uninferable measure is
        // skipped gracefully here (unchanged pre-#2010 behavior). The
        // file-extraction path (`parse_assertion_obligations`) re-runs the same
        // builder and instead fails CLOSED on `Err`, and consumes the returned
        // `LoopDecreaseBinding` to register the decrease as a loop-inductive
        // obligation (see `body_extract.rs`). Keeping ONE builder prevents the
        // two paths from drifting.
        let _ = build_loop_decreases_obligations(context, measure, location, None);
    }) {
        Ok(()) => {}
        Err(_) => record_obligation_drop(),
    }
}

/// The single-measure loop-decrease binding needed to register the decrease as a
/// loop-inductive obligation on the file-extraction path. The encoder proves the
/// strict-descent obligation `measure < entry_var` (WF2) as a frame-condition
/// inductive step once `entry_var == measure[pre-state]` is injected as a
/// captured body transition (see `body_extract.rs` and
/// `invariants/frame_condition.rs`), and proves the non-negativity floor
/// `measure >= 0` (WF1) as a DIRECT single-state entailment under the loop
/// invariants + guard (see `encoder/verification/typed.rs`).
#[derive(Debug, Clone)]
pub(crate) struct LoopDecreaseBinding {
    /// Name of the emitted `MeasureDecreases` obligation (`{sanitized}_decreases`).
    pub(crate) decrease_obligation_name: String,
    /// Name of the emitted `MeasureNonNegative` obligation
    /// (`{measure_expr}_nonneg`). Registered with the same loop metadata as the
    /// decrease so it lands in the `loop_measures` lane (NOT the flat assertions
    /// lane, which would leave the loop variable typed `MathInt` and clash with
    /// the post-loop normal-exit `Uint` assumption). Verified as the WF1 floor.
    pub(crate) nonneg_obligation_name: String,
    /// Fresh entry variable (`{sanitized}_entry`) standing for the measure at the
    /// start of the previous iteration. Must be added to the loop's modified set
    /// so the entry-binding transition is consulted (`frame_condition.rs`).
    pub(crate) entry_var: String,
    /// The raw measure expression, used verbatim as the transition RHS
    /// `entry_var == measure[vars := pre-state]`.
    pub(crate) measure_expr: String,
}

/// Why `build_loop_decreases_obligations` could not construct a decrease.
///
/// The runtime path treats every variant as "skip gracefully"; the file path
/// maps every variant to a fail-CLOSED encoding error, because a silently
/// dropped decrease under an `#[ensures(true)]` body would be a spurious
/// Verified.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LoopDecreaseBuildError {
    /// A tuple measure `(a, b, …)` failed to parse into components.
    TupleParse,
    /// A measure (or lex component) is empty, a pure numeric literal, or has no
    /// variable reference.
    InvalidMeasure,
    /// No variable in the measure has a declared type, so the entry variable's
    /// sort cannot be inferred.
    UninferableType,
}

/// Builds the loop-decreases obligations on `context` (non-negativity + entry
/// variable + `entry >= 0` assumption + strict decrease) and, for a SINGLE
/// (non-lexicographic) measure, returns the [`LoopDecreaseBinding`] the file
/// path uses to register the decrease as a loop-inductive obligation.
///
/// Returns `Ok(None)` for:
/// - lexicographic (tuple) measures — the multi-entry-var inductive registration
///   is out of scope; the file path leaves the lex decrease with free entry vars
///   (a fail-closed Counterexample), and
/// - the runtime idempotency re-entry (the entry variable already exists from an
///   earlier iteration's collection).
///
/// Returns `Err` when a present measure cannot be constructed, so the file path
/// can fail closed instead of silently dropping the obligation.
#[allow(clippy::indexing_slicing)] // invariant: tuple-component indexing is guarded by `components.is_empty()`, `enumerate()`, and `conjuncts.len() == 1`
pub(crate) fn build_loop_decreases_obligations(
    context: &mut VerificationContext,
    measure: String,
    location: Option<String>,
    type_hint: Option<crate::ir::TrustVcType>,
) -> Result<Option<LoopDecreaseBinding>, LoopDecreaseBuildError> {
    let trimmed = measure.trim();
    let tuple_components = if trimmed.starts_with('(') && trimmed.ends_with(')') {
        match parse_tuple_expr_components(trimmed) {
            Ok(components) => components,
            Err(_) => return Err(LoopDecreaseBuildError::TupleParse),
        }
    } else {
        None
    };

    if let Some(components) = tuple_components {
        let components: Vec<String> = components.into_iter().filter(|s| !s.is_empty()).collect();

        // Invalid loop_decreases! annotation. Part of #1955.
        if components.is_empty() {
            return Err(LoopDecreaseBuildError::InvalidMeasure);
        }

        // Validate all components first. Part of #1955.
        for component in &components {
            if !is_valid_measure_component(component) {
                return Err(LoopDecreaseBuildError::InvalidMeasure);
            }
        }

        // Check if lex obligations already registered (guard against
        // duplicate obligations when loop_decreases! runs multiple
        // iterations at runtime).
        let first_entry = format!("{}_entry", sanitize_measure_name(&components[0]));
        let already_registered = context.has_variable(&first_entry);

        // Always add non-negativity for each component (idempotent check
        // happens at encoding time). Create entry variables on first call.
        let mut entry_vars = Vec::new();
        for component in &components {
            if !already_registered {
                context.add_measure_nonneg(component);
            }

            let sanitized = sanitize_measure_name(component);
            let entry_var = format!("{}_entry", sanitized);
            if !context.has_variable(&entry_var) {
                let measure_type = match infer_measure_type(context, component) {
                    Some(ty) => ty.clone(),
                    None => type_hint
                        .clone()
                        .ok_or(LoopDecreaseBuildError::UninferableType)?,
                };
                context.declare_var_typed(&entry_var, measure_type);
                context.push_obligation(ProofObligation::assume(
                    format!("{}_entry_nonneg", sanitized),
                    format!("{} >= 0", entry_var),
                ));
            }
            entry_vars.push(entry_var);
        }

        // Only generate the lex disjunction once per measure tuple
        if !already_registered {
            // Generate single lexicographic disjunction (#1593):
            // For (a, b, c):
            //   a < a_entry
            //   || (a == a_entry && b < b_entry)
            //   || (a == a_entry && b == b_entry && c < c_entry)
            let mut disjuncts = Vec::with_capacity(components.len());
            for (idx, component) in components.iter().enumerate() {
                let mut conjuncts = Vec::with_capacity(idx + 1);
                // Equality for all previous components
                for prev in 0..idx {
                    conjuncts.push(format!("{} == {}", components[prev], entry_vars[prev]));
                }
                // Strict decrease for this component
                conjuncts.push(format!("{} < {}", component, entry_vars[idx]));

                if conjuncts.len() == 1 {
                    disjuncts.push(conjuncts[0].clone());
                } else {
                    disjuncts.push(format!("({})", conjuncts.join(" && ")));
                }
            }

            let lex_condition = disjuncts.join(" || ");
            let lex_name = components
                .iter()
                .map(|c| sanitize_measure_name(c))
                .collect::<Vec<_>>()
                .join("_");

            let mut obligation = ProofObligation::measure_decreases(
                format!("{}_decreases", lex_name),
                lex_condition,
            );
            if let Some(loc) = location {
                obligation = obligation.with_location(loc.to_string());
            }
            context.obligations.push(obligation);
        }
        // Lexicographic measures are kept fail-closed on the file path (no
        // inductive binding returned): none of the ported corpus cases use them.
        Ok(None)
    } else {
        let single = trimmed.to_string();
        // Invalid loop_decreases! annotation. Part of #1955.
        if single.is_empty() || !is_valid_measure_component(&single) {
            return Err(LoopDecreaseBuildError::InvalidMeasure);
        }
        add_loop_decrease_obligations(context, &single, location.as_deref(), type_hint)
    }
}

/// Adds non-negativity and decrease obligations for a single loop measure.
///
/// On the first call for a given measure, generates:
/// - `MeasureNonNegative`: `measure >= 0`
/// - Variable declaration: `{sanitized}_entry` (same type as measure variable)
/// - Assumption: `{sanitized}_entry >= 0`
/// - `MeasureDecreases`: `measure < {sanitized}_entry` (strict decrease)
///
/// On subsequent calls (same measure, e.g., multiple loop iterations),
/// returns `Ok(None)` since the entry variable and decrease obligation are
/// already registered.
fn add_loop_decrease_obligations(
    context: &mut VerificationContext,
    measure_name: &str,
    location: Option<&str>,
    type_hint: Option<crate::ir::TrustVcType>,
) -> Result<Option<LoopDecreaseBinding>, LoopDecreaseBuildError> {
    // Only add obligations once per measure (guard against duplicate obligations
    // when loop_decreases! runs multiple iterations at runtime).
    let sanitized = sanitize_measure_name(measure_name);
    let entry_var = format!("{}_entry", sanitized);
    if !context.has_variable(&entry_var) {
        // 1. Non-negativity: measure >= 0
        context.add_measure_nonneg(measure_name);
        // Infer the measure type from component variables to avoid sort mismatches.
        // Fail closed if type cannot be inferred. Part of #1955.
        // A measure that rendered to a bare literal (a loop that never modifies
        // its own measure variable — upstream loop_decreases2 test2/test3) has
        // no identifier to infer from; the file path supplies the variable's
        // declared scalar type as `type_hint` so the strict-descent obligation
        // is emitted (and refuted) instead of failing closed.
        let measure_type = match infer_measure_type(context, measure_name) {
            Some(ty) => ty.clone(),
            None => type_hint.ok_or(LoopDecreaseBuildError::UninferableType)?,
        };

        // Declare entry variable with the same type as the measure variable
        context.declare_var_typed(&entry_var, measure_type);

        // NOTE: entry_var is intentionally left unconstrained HERE. On the
        // RUNTIME path the relationship between entry_var and measure_name comes
        // from the loop body model (e.g., "n_entry == n + 1" for a decrement
        // loop). Adding "entry_var == measure_name" would create a contradiction
        // with body models and cause vacuous truth (see #1579 P116 rejection).
        // On the FILE path the binding `entry_var == measure[pre-state]` is
        // injected as a captured single-iteration body transition against THIS
        // measure obligation's name (see `body_extract.rs`) so the decrease
        // verifies as a frame-condition inductive step — never as a free-var
        // constraint here.

        // Assume entry value is non-negative (well-founded ordering base)
        context.push_obligation(ProofObligation::assume(
            format!("{}_entry_nonneg", sanitized),
            format!("{} >= 0", entry_var),
        ));

        // Assert strict decrease: current measure < entry measure
        // For add_measure_decreases(name, old, new): generates "new < old"
        context.add_measure_decreases(&sanitized, &entry_var, measure_name);

        // Record location if provided
        if let Some(loc) = location {
            if let Some(last) = context.obligations.last_mut() {
                last.location = Some(loc.to_string());
            }
        }

        Ok(Some(LoopDecreaseBinding {
            decrease_obligation_name: format!("{}_decreases", sanitized),
            nonneg_obligation_name: format!("{}_nonneg", measure_name),
            entry_var,
            measure_expr: measure_name.to_string(),
        }))
    } else {
        // Runtime idempotency re-entry: obligations already registered from an
        // earlier iteration's collection. No new binding.
        Ok(None)
    }
}
