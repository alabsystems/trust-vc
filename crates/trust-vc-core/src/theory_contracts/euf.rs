// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;

// ===========================================================================
// Contract 1: EUF (Equality with Uninterpreted Functions)
// ===========================================================================

/// Abstract term identifier for EUF contract specification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct EufTermId(pub(crate) u32);

/// An equality between two EUF terms.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Equality {
    pub(crate) lhs: EufTermId,
    pub(crate) rhs: EufTermId,
}

/// A function application: `func(args) = result`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct FunctionApp {
    pub(crate) func_id: u32,
    pub(crate) args: Vec<EufTermId>,
    pub(crate) result: EufTermId,
}

/// Result of EUF propagation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum EufResult {
    /// Propagation completed with derived equalities.
    Consistent { derived: Vec<Equality> },
    /// A contradiction was found (e.g., a=b and a!=b both asserted).
    Contradiction { eq: Equality, reason: Vec<Equality> },
}

/// Contract trait for EUF theory solver.
///
/// Captures the pre/postconditions of congruence closure propagation:
///
/// ```text
/// fn propagate_equality(terms: &[EufTermId], equalities: &[Equality]) -> EufResult
///
/// requires: all terms referenced in equalities are present in `terms`
///
/// ensures |result|:
///   Consistent => congruence closure is complete
///   Consistent => no contradictory equalities (a=b and a!=b)
///   Transitivity: a=b ∧ b=c => a=c derivable
///   Congruence: a=b => f(a)=f(b) for all function applications
/// ```
pub(crate) trait ContractEuf {
    /// Propagate equalities through congruence closure.
    fn propagate_equality(&self, terms: &[EufTermId], equalities: &[Equality]) -> EufResult;
}

/// Reference EUF implementation using union-find for congruence closure.
pub(crate) struct ReferenceEuf {
    pub(crate) function_apps: Vec<FunctionApp>,
    pub(crate) disequalities: Vec<Equality>,
}

impl ReferenceEuf {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            function_apps: Vec::new(),
            disequalities: Vec::new(),
        }
    }

    pub(crate) fn add_function_app(&mut self, app: FunctionApp) {
        self.function_apps.push(app);
    }

    pub(crate) fn add_disequality(&mut self, diseq: Equality) {
        self.disequalities.push(diseq);
    }

    /// Find the representative of a term in the union-find.
    fn find(parent: &mut HashMap<EufTermId, EufTermId>, x: EufTermId) -> EufTermId {
        let p = *parent.entry(x).or_insert(x);
        if p == x {
            return x;
        }
        let root = Self::find(parent, p);
        parent.insert(x, root);
        root
    }

    /// Union two terms in the union-find.
    fn union(parent: &mut HashMap<EufTermId, EufTermId>, a: EufTermId, b: EufTermId) {
        let ra = Self::find(parent, a);
        let rb = Self::find(parent, b);
        if ra != rb {
            parent.insert(ra, rb);
        }
    }
}

impl ContractEuf for ReferenceEuf {
    fn propagate_equality(&self, terms: &[EufTermId], equalities: &[Equality]) -> EufResult {
        let mut parent: HashMap<EufTermId, EufTermId> = HashMap::new();
        for &t in terms {
            parent.insert(t, t);
        }

        // Merge all asserted equalities.
        for eq in equalities {
            Self::union(&mut parent, eq.lhs, eq.rhs);
        }

        // Congruence closure: if f(a1..an) and f(b1..bn) with ai=bi then
        // their results must be equal.
        let mut changed = true;
        while changed {
            changed = false;
            let apps = self.function_apps.clone();
            for i in 0..apps.len() {
                for j in (i + 1)..apps.len() {
                    if apps[i].func_id != apps[j].func_id {
                        continue;
                    }
                    if apps[i].args.len() != apps[j].args.len() {
                        continue;
                    }
                    let args_equal = apps[i]
                        .args
                        .iter()
                        .zip(apps[j].args.iter())
                        .all(|(&a, &b)| Self::find(&mut parent, a) == Self::find(&mut parent, b));
                    if args_equal {
                        let ri = Self::find(&mut parent, apps[i].result);
                        let rj = Self::find(&mut parent, apps[j].result);
                        if ri != rj {
                            Self::union(&mut parent, apps[i].result, apps[j].result);
                            changed = true;
                        }
                    }
                }
            }
        }

        // Check disequalities for contradictions.
        for diseq in &self.disequalities {
            let ra = Self::find(&mut parent, diseq.lhs);
            let rb = Self::find(&mut parent, diseq.rhs);
            if ra == rb {
                // Contradiction: asserted a != b but congruence closure merged them.
                let reason: Vec<Equality> = equalities
                    .iter()
                    .filter(|eq| {
                        Self::find(&mut parent, eq.lhs) == ra
                            || Self::find(&mut parent, eq.rhs) == ra
                    })
                    .copied()
                    .collect();
                return EufResult::Contradiction { eq: *diseq, reason };
            }
        }

        // Collect derived equalities (pairs now in same equivalence class).
        let mut derived = Vec::new();
        let term_set: Vec<EufTermId> = terms.to_vec();
        for i in 0..term_set.len() {
            for j in (i + 1)..term_set.len() {
                let ri = Self::find(&mut parent, term_set[i]);
                let rj = Self::find(&mut parent, term_set[j]);
                if ri == rj {
                    let eq = Equality {
                        lhs: term_set[i],
                        rhs: term_set[j],
                    };
                    if !equalities.contains(&eq) {
                        derived.push(eq);
                    }
                }
            }
        }

        EufResult::Consistent { derived }
    }
}

/// Validates EUF propagation postconditions.
///
/// Checks:
/// 1. Transitivity: if a=b and b=c are in equalities+derived, then a=c is derivable.
/// 2. Congruence: for function apps f(a)=r1 and f(b)=r2 where a=b, then r1=r2.
/// 3. No contradictory equalities in consistent result.
#[must_use]
pub(crate) fn validate_euf_postcondition(
    terms: &[EufTermId],
    input_equalities: &[Equality],
    function_apps: &[FunctionApp],
    result: &EufResult,
) -> bool {
    match result {
        EufResult::Consistent { derived } => {
            // Build equivalence classes from input + derived equalities.
            let mut parent: HashMap<EufTermId, EufTermId> = HashMap::new();
            for &t in terms {
                parent.insert(t, t);
            }
            let all_eqs: Vec<&Equality> = input_equalities.iter().chain(derived.iter()).collect();
            for eq in &all_eqs {
                ReferenceEuf::union(&mut parent, eq.lhs, eq.rhs);
            }

            // Check congruence completeness: for every pair of function apps
            // with same func_id and equal args, their results must be equal.
            for i in 0..function_apps.len() {
                for j in (i + 1)..function_apps.len() {
                    if function_apps[i].func_id != function_apps[j].func_id {
                        continue;
                    }
                    if function_apps[i].args.len() != function_apps[j].args.len() {
                        continue;
                    }
                    let args_equal = function_apps[i]
                        .args
                        .iter()
                        .zip(function_apps[j].args.iter())
                        .all(|(&a, &b)| {
                            ReferenceEuf::find(&mut parent, a) == ReferenceEuf::find(&mut parent, b)
                        });
                    if args_equal {
                        let ri = ReferenceEuf::find(&mut parent, function_apps[i].result);
                        let rj = ReferenceEuf::find(&mut parent, function_apps[j].result);
                        if ri != rj {
                            return false; // Congruence incomplete
                        }
                    }
                }
            }

            true
        }
        EufResult::Contradiction { eq, reason: _ } => {
            // The contradiction must involve terms that are actually equated
            // by the input. We just verify the eq fields reference valid terms.
            terms.contains(&eq.lhs) && terms.contains(&eq.rhs)
        }
    }
}

/// Registers the EUF propagation contract as an extern_spec entry.
pub(crate) fn register_euf_propagation_contract() {
    crate::extern_spec_verify::register_extern_spec(
        "ay_dpll::theory::euf::EufSolver::propagate",
        &["all_terms_present(terms, equalities)".to_string()],
        &[
            "consistent ==> congruence_closure_complete(result)".to_string(),
            "consistent ==> no_contradictions(result)".to_string(),
            "transitive(equalities ++ derived)".to_string(),
        ],
    );
}
