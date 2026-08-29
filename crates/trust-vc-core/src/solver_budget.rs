//! Deterministic solver work budgets.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! # Why a work budget and not a wall clock
//!
//! trust-vc used to bound every solve with `Solver::set_timeout` alone — a
//! WALL CLOCK. A wall clock is not a property of the query, it is a property
//! of the machine: the same obligation, the same encoding, the same ay build
//! and the same seed produce `unsat` on an idle box and `unknown` on a loaded
//! one, because the deadline crosses the solve at a different point. Measured
//! on this repo (2026-08-20, see the module docs of
//! `crate::encoder::verification::timeout`): one query, one process, a 1450ms
//! wall deadline — `unknown` at 1466ms and `unsat` at 1386ms with EVERY search
//! counter byte-identical across both runs. Identical work, opposite verdicts,
//! decided by 16ms of scheduling noise.
//!
//! ay exposes a DETERMINISTIC alternative: `(set-option :rlimit N)` bounds a
//! solve by SAT CONFLICTS, and the cutoff is byte-identical on every run while
//! wall time varies freely.
//!
//! # Why conflicts, and not `rlimit_count`
//!
//! ay also REPORTS a Z3-shaped `rlimit_count` statistic (`Statistics::
//! rlimit_count`), and Verus's `rlimit(N)` is denominated in Z3 resource
//! units. Those are a tempting unit to expose, and they are the wrong one:
//!
//! * ay's `rlimit_count` is only a REPORTED statistic. There is no option that
//!   bounds it — `(set-option :rlimit N)` sets `Executor::set_resource_limit`,
//!   which the pipeline reads as a per-SAT-solve CONFLICT allowance. Exposing
//!   `rlimit_count` would name a unit nothing enforces.
//! * `rlimit_count` is not calibrated against Z3's `RLIMIT_PER_SECOND`; it is
//!   a derived sum over conflicts/decisions/propagations
//!   (`docs/ay-solver-inventory-2026-07-13.md` R12). Quoting it as a Z3
//!   resource count would be a fake parity claim, and the scales genuinely
//!   differ: a measured swap_t3 solve took 519 conflicts and 55794
//!   `rlimit_count`.
//!
//! So the unit trust-vc exposes is the unit ay actually enforces: SAT
//! conflicts. `#[verifier::rlimit(N)]` grants `N × RLIMIT_UNIT_CONFLICTS`
//! conflicts of deterministic work.

/// Conflicts granted per unit of `#[verifier::rlimit(N)]`.
///
/// Anchored so that `rlimit(10)` — upstream Verus's own default rlimit —
/// reproduces trust-vc's default budget
/// (`encoder::verification::timeout::DEFAULT_CONFLICT_BUDGET_CONFLICTS`,
/// 400_000) exactly. That anchor is the only defensible one available: ay's
/// `rlimit_count` is NOT calibrated against Z3's `RLIMIT_PER_SECOND`
/// (`docs/ay-solver-inventory-2026-07-13.md` R12), so there is no honest
/// conversion from a Z3 resource unit to an ay conflict. What DOES carry over
/// faithfully is the attribute's MEANING: a monotone multiplier on a
/// deterministic work budget, where `rlimit(2N)` grants exactly twice the work
/// of `rlimit(N)` on every machine and under every load.
pub const RLIMIT_UNIT_CONFLICTS: u64 = 40_000;

/// A deterministic solver work budget, measured in SAT conflicts.
///
/// This is the ONLY machine-independent bound trust-vc can install through
/// ay's public `Solver` API — there is no typed `set_resource_limit` on
/// `ay_dpll::api::Solver`; the route is
/// `set_option("rlimit", …)` → executor `SetOption` handler →
/// `Executor::set_resource_limit`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ConflictBudget {
    /// Stop after this many SAT conflicts with `UnknownReason::ResourceLimit`.
    ///
    /// `NonZeroU64` is load-bearing, not tidiness: ay reads `:rlimit 0` as "NO
    /// limit" AND additionally disables its own default ground budget, so a
    /// zero that leaked in here as "use the default" would silently REMOVE
    /// every deterministic bound. A zero budget is unrepresentable.
    Bounded(std::num::NonZeroU64),
    /// Install NO trust-vc budget: ay's own default ground allowance governs.
    ///
    /// This is what `#[verifier::rlimit(infinity)]` / `rlimit(0)` map to, and
    /// the implementation detail is load-bearing enough to state twice: it
    /// emits NO `:rlimit` option at all. It does NOT emit `:rlimit 0`.
    ///
    /// `:rlimit 0` looks like the faithful translation of upstream's
    /// "unlimited", and it is a trap. In ay, `0` means "no limit" AND
    /// additionally calls `set_ground_budget_enabled(false)`, which switches
    /// off ay's OWN default ground allowance on BOTH axes — the 400k-conflict
    /// and the 24M-decision bound. Combined with the ~1-year wall floor that
    /// `rlimit(infinity)` also installs, that would leave such a function with
    /// no effective termination bound at all: a diverging query would hang the
    /// verifier rather than fail closed. Declining to install a budget keeps
    /// ay's calibrated default in force, which for every workload ever
    /// measured here (worst case 317 conflicts) is indistinguishable from
    /// unlimited while still bounding divergence.
    AyDefault,
}

impl ConflictBudget {
    /// Build a bounded budget, saturating a `0` request up to `1`.
    ///
    /// Callers reach this from user-facing attribute arithmetic (`rlimit(N)`
    /// with a tiny `N`), where rounding to zero must not silently widen into
    /// "no budget" — the two mean opposite things. Genuine "install no
    /// budget" requests name [`Self::AyDefault`] explicitly.
    #[must_use]
    pub fn bounded(conflicts: u64) -> Self {
        Self::Bounded(std::num::NonZeroU64::new(conflicts).unwrap_or(std::num::NonZeroU64::MIN))
    }

    /// The SMT-LIB `:rlimit` option value to emit, or `None` to emit nothing.
    ///
    /// This function is the single place that can produce an `:rlimit`
    /// argument, and it is structurally incapable of producing `"0"`: the
    /// bounded arm holds a `NonZeroU64` and the default arm returns `None`.
    /// That is deliberate — see [`Self::AyDefault`] for what `0` would
    /// actually do.
    #[must_use]
    pub fn option_value(self) -> Option<String> {
        match self {
            Self::Bounded(conflicts) => Some(conflicts.to_string()),
            Self::AyDefault => None,
        }
    }

    /// Conflict count, or `None` when ay's own default governs. Used for
    /// cache keying and diagnostics.
    #[must_use]
    pub fn conflicts(self) -> Option<u64> {
        match self {
            Self::Bounded(conflicts) => Some(conflicts.get()),
            Self::AyDefault => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bounded_zero_saturates_to_one_never_to_a_zero_option() {
        // The whole point of NonZeroU64 here: `0` must never reach ay, where
        // it would mean "no limit AND no default ground budget".
        assert_eq!(
            ConflictBudget::bounded(0).option_value(),
            Some("1".to_string())
        );
        assert_eq!(ConflictBudget::bounded(0).conflicts(), Some(1));
    }

    /// THE CARDINAL PIN. No budget value may ever render as the string "0".
    /// `0` is not "no budget" to ay — it is "no budget AND disable your own
    /// default ground allowance", which removes the 24M-decision divergence
    /// bound as well. Every emitted option string is checked here, including
    /// the one that means "unlimited".
    #[test]
    fn no_budget_can_ever_emit_a_zero_rlimit_option() {
        let budgets = [
            ConflictBudget::AyDefault,
            ConflictBudget::bounded(0),
            ConflictBudget::bounded(1),
            ConflictBudget::bounded(400_000),
            ConflictBudget::bounded(u64::MAX),
        ];
        for budget in budgets {
            assert_ne!(
                budget.option_value(),
                Some("0".to_string()),
                "{budget:?} rendered the forbidden `:rlimit 0`"
            );
        }
    }

    #[test]
    fn ay_default_emits_no_option_at_all() {
        assert_eq!(ConflictBudget::AyDefault.option_value(), None);
        assert_eq!(ConflictBudget::AyDefault.conflicts(), None);
    }

    #[test]
    fn bounded_round_trips_its_conflict_count() {
        assert_eq!(
            ConflictBudget::bounded(400_000).option_value(),
            Some("400000".to_string())
        );
        assert_eq!(ConflictBudget::bounded(400_000).conflicts(), Some(400_000));
    }
}
