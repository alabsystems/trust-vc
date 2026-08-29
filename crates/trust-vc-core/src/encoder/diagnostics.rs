//! Encoding diagnostics — tracks approximations during encoding.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! When trust_vc encoding approximates (bounds-check skip, int2bv coercion,
//! skolemization, broadcast cap, auxiliary precheck fallback), these counters
//! record what happened. Demoting categories downgrade `Verified` to `Unknown`.
//!
//! Part of #2224, #2314. Design:
//! designs/2026-03-15-2314-unsoundness-tracking-coverage-expansion.md

use std::{collections::BTreeMap, fmt};

/// Categories of encoding approximations tracked during one verification run.
///
/// Ordering follows declaration order so summaries stay deterministic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum EncodingApproximation {
    /// Recursive function omitted from invariant-step TypeEnv because its
    /// return type is opaque, so lowering ran with a weaker environment.
    FunctionContextReturnTypeOmitted,
    /// Bounds check skipped in a quantifier body for a bound-variable index.
    BoundsCheckSkipped,
    /// Sort::Int to BitVec coercion applied in collection operations.
    IntBvCoercion,
    /// Broadcast instance cap reached; remaining broadcasts were added as
    /// plain assumptions instead of quantified formulas.
    BroadcastCapHit,
    /// Trigger-less forall skolemized into a ground formula.
    ForallSkolemization,
    /// Ground-pool fixpoint did not converge within the round limit.
    GroundFixpointNonConvergence,
    /// A triggerless `exists v. (… forall …)` whose witness-dependent body was
    /// refuted via the exact structural negation `forall v. range ⇒ refute(body)`
    /// — a real alternating `∀∃` over a witness that depends on `v`. ay's
    /// quantifier instantiation decides this shape UNRELIABLY (it can return a
    /// spurious UNSAT for a satisfiable refutation, i.e. report a genuinely-false
    /// existential as Verified — round8 finding 17, dependent case). Demoting, so
    /// an UNSAT/`Verified` on this shape becomes `Unknown` rather than trusting
    /// ay's verdict.
    NestedExistentialAlternation,
    /// A datatype-valued `match` was encoded INSIDE a real solver binder, so its
    /// tester/selector re-binding (`bind_datatype_match_result`) was withheld:
    /// those facts are asserted at the solver top level and would have captured
    /// the enclosing binder's variable. The `ite` tree is used directly instead.
    /// Non-demoting: this withholds ASSUMPTIONS, so the solver context is only
    /// ever weaker — it cannot turn a refutation into a `Verified`.
    ///
    /// This covers the DATATYPE-MATCH instance only. The general case is
    /// `HoistCapturedByPendingBinder` below.
    DatatypeMatchBindingUnderBinder,
    /// An encode-then-close axiom (`add_typed_broadcast`, `encode_fuel_axioms`,
    /// the trait-method axioms) was DECLINED because a fact hoisted to the
    /// solver top level during the body encode mentions a variable the pending
    /// `forall` was about to bind. Emitting the axiom would have captured that
    /// fact and collapsed the function to a constant. See
    /// `encoder::binder_capture`.
    ///
    /// Non-demoting: declining an ASSUMPTION only weakens the context — the
    /// function stays uninterpreted, so a proof can be lost but no refutation
    /// can turn into a `Verified`.
    HoistCapturedByPendingBinder,
}

impl EncodingApproximation {
    /// Whether the category can make a `Verified` result unreliable.
    ///
    /// IMPORTANT: This match is intentionally exhaustive (no wildcard).
    /// When adding a new `EncodingApproximation` variant, you MUST decide
    /// whether it is demoting. A wildcard here would silently default new
    /// variants to non-demoting, which is a fail-open soundness gap.
    #[must_use]
    pub(crate) fn is_demoting(self) -> bool {
        match self {
            Self::FunctionContextReturnTypeOmitted | Self::NestedExistentialAlternation => true,
            Self::BoundsCheckSkipped
            | Self::IntBvCoercion
            | Self::BroadcastCapHit
            | Self::ForallSkolemization
            | Self::DatatypeMatchBindingUnderBinder
            | Self::HoistCapturedByPendingBinder
            | Self::GroundFixpointNonConvergence => false,
        }
    }
}

impl fmt::Display for EncodingApproximation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::FunctionContextReturnTypeOmitted => {
                write!(f, "function_context_return_type_omitted")
            }
            Self::BoundsCheckSkipped => write!(f, "bounds_check_skipped"),
            Self::IntBvCoercion => write!(f, "int_bv_coercion"),
            Self::BroadcastCapHit => write!(f, "broadcast_cap_hit"),
            Self::ForallSkolemization => write!(f, "forall_skolemization"),
            Self::DatatypeMatchBindingUnderBinder => {
                write!(f, "datatype_match_binding_under_binder")
            }
            Self::HoistCapturedByPendingBinder => {
                write!(f, "hoist_captured_by_pending_binder")
            }
            Self::GroundFixpointNonConvergence => {
                write!(f, "ground_fixpoint_non_convergence")
            }
            Self::NestedExistentialAlternation => {
                write!(f, "nested_existential_alternation")
            }
        }
    }
}

/// Tracks encoding approximations during a single verification run.
///
/// Per-encoder instances stay local; callers explicitly merge diagnostics from
/// auxiliary encoders that contribute to the same user-visible result.
#[derive(Debug, Clone, Default)]
pub(crate) struct EncodingDiagnostics {
    counts: BTreeMap<EncodingApproximation, u32>,
}

impl EncodingDiagnostics {
    /// Increment one approximation category.
    pub(crate) fn record(&mut self, category: EncodingApproximation) {
        self.record_n(category, 1);
    }

    /// Read the count for a single category.
    ///
    /// The solve envelope snapshots selected counts around refutation encoding
    /// so a newly observed solver-blocking approximation can fail closed before
    /// entering a solver path known not to honor its deadline.
    #[must_use]
    pub(crate) fn count(&self, category: EncodingApproximation) -> u32 {
        self.counts.get(&category).copied().unwrap_or(0)
    }

    /// Returns true if any demoting category is non-zero.
    #[must_use]
    pub(crate) fn has_demoting(&self) -> bool {
        self.counts
            .iter()
            .any(|(category, count)| *count > 0 && category.is_demoting())
    }

    /// Human-readable summary of all non-zero counters.
    #[cfg(test)]
    #[must_use]
    pub(crate) fn summary(&self) -> String {
        self.format_summary(|_| true)
    }

    /// Human-readable summary of only demoting categories.
    #[must_use]
    pub(crate) fn summary_demoting(&self) -> String {
        self.format_summary(EncodingApproximation::is_demoting)
    }

    /// Standard demotion reason string. The `demoted:` prefix must stay stable
    /// so `UnknownCategory::EncodingDemotion` keeps classifying correctly.
    #[must_use]
    pub(crate) fn demotion_reason(&self, target: &str) -> String {
        format!(
            "demoted: encoding approximations [{}] for '{}'",
            self.summary_demoting(),
            target,
        )
    }

    /// Merge counts from another diagnostics instance.
    pub(crate) fn merge(&mut self, other: &EncodingDiagnostics) {
        for (category, count) in &other.counts {
            self.record_n(*category, *count);
        }
    }

    fn record_n(&mut self, category: EncodingApproximation, count: u32) {
        *self.counts.entry(category).or_insert(0) += count;
    }

    fn format_summary(&self, include: impl Fn(EncodingApproximation) -> bool) -> String {
        self.counts
            .iter()
            .filter(|(category, count)| **count > 0 && include(**category))
            .map(|(category, count)| format!("{category}({count})"))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Exercises every `EncodingApproximation` variant through `is_demoting()`.
    /// If a new variant is added, this test must be updated — the exhaustive
    /// match in `is_demoting()` will already force a compile error, but this
    /// test documents the expected classification.
    #[test]
    fn test_is_demoting_exhaustive_classification() {
        assert!(
            EncodingApproximation::FunctionContextReturnTypeOmitted.is_demoting(),
            "FunctionContextReturnTypeOmitted should be demoting"
        );
        assert!(
            !EncodingApproximation::BoundsCheckSkipped.is_demoting(),
            "BoundsCheckSkipped should not be demoting"
        );
        assert!(
            !EncodingApproximation::IntBvCoercion.is_demoting(),
            "IntBvCoercion should not be demoting"
        );
        assert!(
            !EncodingApproximation::BroadcastCapHit.is_demoting(),
            "BroadcastCapHit should not be demoting"
        );
        assert!(
            !EncodingApproximation::ForallSkolemization.is_demoting(),
            "ForallSkolemization should not be demoting"
        );
        assert!(
            !EncodingApproximation::GroundFixpointNonConvergence.is_demoting(),
            "GroundFixpointNonConvergence should not be demoting"
        );
        assert!(
            EncodingApproximation::NestedExistentialAlternation.is_demoting(),
            "NestedExistentialAlternation should be demoting (ay decides the \
             witness-dependent alternating ∀∃ refutation unreliably)"
        );
    }

    #[test]
    fn test_has_demoting_only_fires_on_demoting_categories() {
        let mut diag = EncodingDiagnostics::default();
        assert!(
            !diag.has_demoting(),
            "empty diagnostics should not be demoting"
        );

        diag.record(EncodingApproximation::BoundsCheckSkipped);
        assert!(
            !diag.has_demoting(),
            "non-demoting category should not trigger"
        );

        diag.record(EncodingApproximation::FunctionContextReturnTypeOmitted);
        assert!(diag.has_demoting(), "demoting category should trigger");
    }

    #[test]
    fn test_demotion_reason_format() {
        let mut diag = EncodingDiagnostics::default();
        diag.record(EncodingApproximation::FunctionContextReturnTypeOmitted);
        let reason = diag.demotion_reason("test_assertion");
        assert!(
            reason.starts_with("demoted:"),
            "demotion reason must start with 'demoted:' for UnknownCategory classification"
        );
        assert!(reason.contains("test_assertion"));
    }

    #[test]
    fn test_merge_combines_counts() {
        let mut a = EncodingDiagnostics::default();
        a.record(EncodingApproximation::BoundsCheckSkipped);
        a.record(EncodingApproximation::BoundsCheckSkipped);

        let mut b = EncodingDiagnostics::default();
        b.record(EncodingApproximation::BoundsCheckSkipped);
        b.record(EncodingApproximation::IntBvCoercion);

        a.merge(&b);
        assert_eq!(a.count(EncodingApproximation::BoundsCheckSkipped), 3);
        assert_eq!(a.count(EncodingApproximation::IntBvCoercion), 1);
    }
}
