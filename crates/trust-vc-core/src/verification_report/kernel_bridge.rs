// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! What a proof certificate is evidence FOR, and how much of it the
//! trust-vc-kernel re-checked.
//!
//! An UNSAT proof shows `premises ⊢ ⊥` for whatever its `assume` steps say.
//! AY's strict checker and the trust-vc-kernel both take those premises as
//! given: they check the derivation, not that it starts from the query
//! trust-vc posed. So a certificate is evidence about an obligation only when
//! its premises are clauses of that obligation's own negated query. This
//! module decides that ([`bind_premises`]) and runs the kernel
//! ([`check_proof_with_kernel`]); [`certify_last_refutation`] does both for
//! the solve site.
//!
//! # The posed query
//!
//! [`PosedQuery`] is rebuilt from the solver API's transcript of trust-vc's
//! own calls (`assert`, `push`, `pop`, `reset`, `check-sat-assuming`), which
//! records the term handle the caller passed, before any definitional
//! adoption, preprocessing or proof production touches it. Nothing the
//! solver authored about the problem is consulted: not the proof's own
//! `assume` steps, not the executor's assertion stack (adoption rewrites it),
//! not the proof bundle's obligation list, not the rendered Alethe problem.
//! The negated goal handle trust-vc built for the obligation must be in the
//! live part of that transcript, or the transcript is not this query's.
//!
//! # Binding rule
//!
//! Every `assume` is a term of the posed query, or an exact instance of a
//! posed `forall` (definitional adoption asserts such instances; each is
//! entailed by its `forall`). Binding is a set test: the order of the
//! premises, and premises the proof does not use, do not matter.
//!
//! A query can collapse while it is built. With `ret := x * y`, AY's term
//! builder folds `ret == x * y` to `true`, so the negated goal trust-vc
//! asserts is the constant `false` and the certificate is
//! `(assume t0 false) ... (cl)`. That refutes the posed query like any other
//! certificate. What it shows about the obligation rests on the builder's
//! rewrite, and every certificate already relies on the rewrites the builder
//! made before the solver saw the query. So it binds, and
//! `ProofCertificate::query_collapsed` discloses it. The solver cannot
//! introduce a `false` premise of its own: a `false` that trust-vc did not
//! assert is not a term of the posed query.
//!
//! # What the kernel checks
//!
//! The proof is checked once, in its own order. A step may cite only an
//! earlier step whose conclusion is already settled, meaning checked, or
//! taken on trust and counted. A step's own conclusion is settled only after
//! its rule is decided. A step that cites itself, a later step or a step with
//! no clause is refused, and with it the whole proof. So no claimed conclusion
//! is relied on before it is checked, and no step can justify itself through
//! a cycle. AY's strict checker requires the same order.
//!
//! Every resolution step is re-derived from its parents, first by the bridge
//! and then again by the kernel. The empty clause must be derived by a checked
//! step, never assumed. Literal polarity is read off the proof's own term
//! store. It is never guessed from the resolution steps being checked: that
//! guess made every binary resolution self-certifying. For each generic step
//! the bridge decides whether it is checked:
//!
//! * a `hole` or `trust` step is one the producer says it did not prove. It
//!   is taken on trust and counted, whatever it concludes;
//! * a generic `resolution` / `th_resolution` step is re-derived as a chain of
//!   binary resolutions that the kernel replays;
//! * any other generic step whose conclusion follows from its premises by
//!   propositional reasoning alone is checked by the bridge. Every
//!   non-connective subterm is an opaque atom, decided by truth table under
//!   small caps. This covers the Tseitin family, `and`, `or`, `not_or`,
//!   `contraction`, `false`, and so on;
//! * every other generic step, and every theory lemma, is a clause the kernel
//!   takes on trust. Theory lemmas go through
//!   `trust_vc_kernel::check_proof_with_theory`. Its EUF/LRA checks are
//!   structural (no terms, no coefficients), so each lemma is still counted as
//!   trusted. Only AY's strict checker checks these clauses, and the count is
//!   disclosed with the certificate.

use std::collections::{BTreeSet, HashMap, HashSet};

use ay_core::{AletheRule, Proof, ProofId, ProofStep, TermData, TermId, TermStore};
use ay_dpll::api::{NativeReplayEvent, NativeReplayEventKind};

use trust_vc_kernel::bridge::{
    AYClause, AYProofArtifact, AYResolutionStep, AYTheoryKind, AYTheoryLemma,
};
use trust_vc_kernel::types::CheckResult;

// ---------------------------------------------------------------------------
// TermId -> signed literal mapping
// ---------------------------------------------------------------------------

/// Signed kernel literal of `tid`: `Not(inner)` is `-(inner + 1)`, anything
/// else `tid + 1`.
fn literal(terms: &TermStore, tid: TermId) -> i64 {
    match terms.get(tid) {
        TermData::Not(inner) => -(i64::from(inner.0) + 1),
        _ => i64::from(tid.0) + 1,
    }
}

// ---------------------------------------------------------------------------
// Propositional entailment over opaque atoms
// ---------------------------------------------------------------------------

/// Most distinct atoms an entailment check enumerates (2^12 assignments).
const PROP_MAX_ATOMS: usize = 12;
/// Most connective nodes an entailment check reads, over all its clauses.
const PROP_MAX_NODES: usize = 1024;

/// A Boolean formula over opaque atoms, read off the term store.
enum Prop {
    Const(bool),
    Atom(usize),
    Not(Box<Prop>),
    And(Vec<Prop>),
    Or(Vec<Prop>),
    Xor(Vec<Prop>),
    /// Right-associative: `a => b => c` is `a => (b => c)`.
    Implies(Vec<Prop>),
    /// Chainable `=` over Bool: every argument has the same value.
    Iff(Vec<Prop>),
    Ite(Box<Prop>, Box<Prop>, Box<Prop>),
}

/// Reads terms as [`Prop`]s, sharing one atom table across every clause of a
/// check so the same term is the same atom everywhere.
struct PropReader<'a> {
    terms: &'a TermStore,
    atoms: Vec<TermId>,
    nodes: usize,
}

impl<'a> PropReader<'a> {
    fn new(terms: &'a TermStore) -> Self {
        Self {
            terms,
            atoms: Vec::new(),
            nodes: 0,
        }
    }

    fn read(&mut self, id: TermId) -> Option<Prop> {
        self.nodes += 1;
        if self.nodes > PROP_MAX_NODES {
            return None;
        }
        let terms = self.terms;
        let is_bool = |t: TermId| matches!(terms.sort(t), ay_core::Sort::Bool);
        Some(match terms.get(id) {
            TermData::Const(ay_core::Constant::Bool(b)) => Prop::Const(*b),
            TermData::Not(inner) => Prop::Not(Box::new(self.read(*inner)?)),
            TermData::Ite(c, t, e) if is_bool(id) => Prop::Ite(
                Box::new(self.read(*c)?),
                Box::new(self.read(*t)?),
                Box::new(self.read(*e)?),
            ),
            TermData::App(ay_core::Symbol::Named(name), args) if !args.is_empty() => {
                let name: &str = name;
                let connective = matches!(name, "and" | "or" | "xor" | "=>")
                    || (name == "=" && args.len() >= 2 && args.iter().all(|a| is_bool(*a)));
                if !connective {
                    return self.atom(id);
                }
                let mut parts = Vec::with_capacity(args.len());
                for arg in args {
                    parts.push(self.read(*arg)?);
                }
                match name {
                    "and" => Prop::And(parts),
                    "or" => Prop::Or(parts),
                    "xor" => Prop::Xor(parts),
                    "=>" => Prop::Implies(parts),
                    _ => Prop::Iff(parts),
                }
            }
            _ => return self.atom(id),
        })
    }

    fn atom(&mut self, id: TermId) -> Option<Prop> {
        if let Some(index) = self.atoms.iter().position(|a| *a == id) {
            return Some(Prop::Atom(index));
        }
        if self.atoms.len() >= PROP_MAX_ATOMS {
            return None;
        }
        self.atoms.push(id);
        Some(Prop::Atom(self.atoms.len() - 1))
    }

    /// The clause `lits` (a disjunction) as one formula.
    fn read_clause(&mut self, lits: &[TermId]) -> Option<Prop> {
        let mut parts = Vec::with_capacity(lits.len());
        for lit in lits {
            parts.push(self.read(*lit)?);
        }
        Some(Prop::Or(parts))
    }
}

fn eval_prop(prop: &Prop, assignment: u32) -> bool {
    match prop {
        Prop::Const(b) => *b,
        Prop::Atom(i) => assignment & (1 << i) != 0,
        Prop::Not(p) => !eval_prop(p, assignment),
        Prop::And(ps) => ps.iter().all(|p| eval_prop(p, assignment)),
        Prop::Or(ps) => ps.iter().any(|p| eval_prop(p, assignment)),
        Prop::Xor(ps) => ps
            .iter()
            .fold(false, |acc, p| acc ^ eval_prop(p, assignment)),
        Prop::Implies(ps) => match ps.split_last() {
            None => true,
            Some((last, init)) => init
                .iter()
                .rev()
                .fold(eval_prop(last, assignment), |acc, p| {
                    !eval_prop(p, assignment) || acc
                }),
        },
        Prop::Iff(ps) => {
            let first = ps.first().is_some_and(|p| eval_prop(p, assignment));
            ps.iter().all(|p| eval_prop(p, assignment) == first)
        }
        Prop::Ite(c, t, e) => {
            if eval_prop(c, assignment) {
                eval_prop(t, assignment)
            } else {
                eval_prop(e, assignment)
            }
        }
    }
}

/// True iff the conjunction of the `premises` clauses entails the
/// `conclusion` clause in propositional logic, every subterm that is not a
/// Boolean connective or constant read as an opaque atom. Such an inference
/// is valid in every theory, so the rule that produced it does not matter.
/// With no premises this is "the conclusion is a tautology"; with an empty
/// conclusion it is "the premises are propositionally unsatisfiable".
/// Returns `false` (not shown) past the size caps.
fn propositionally_entailed(
    terms: &TermStore,
    premises: &[&[TermId]],
    conclusion: &[TermId],
) -> bool {
    let mut reader = PropReader::new(terms);
    let mut hypotheses = Vec::with_capacity(premises.len());
    for premise in premises {
        match reader.read_clause(premise) {
            Some(prop) => hypotheses.push(prop),
            None => return false,
        }
    }
    let Some(goal) = reader.read_clause(conclusion) else {
        return false;
    };
    let assignments = 1u32 << reader.atoms.len();
    (0..assignments).all(|a| !hypotheses.iter().all(|h| eval_prop(h, a)) || eval_prop(&goal, a))
}

// ---------------------------------------------------------------------------
// Theory kind mapping
// ---------------------------------------------------------------------------

/// Map a `ay_core::TheoryLemmaKind` to the kernel bridge's `AYTheoryKind`.
fn map_theory_kind(kind: &ay_core::TheoryLemmaKind) -> AYTheoryKind {
    use ay_core::TheoryLemmaKind;
    match kind {
        TheoryLemmaKind::EufTransitive
        | TheoryLemmaKind::EufCongruent
        | TheoryLemmaKind::EufCongruentPred => AYTheoryKind::Euf,
        TheoryLemmaKind::LraFarkas => AYTheoryKind::Lra,
        TheoryLemmaKind::LiaGeneric => AYTheoryKind::Nia,
        TheoryLemmaKind::BvBitBlast
        | TheoryLemmaKind::BvBitBlastGate { .. }
        | TheoryLemmaKind::FpToBv { .. } => AYTheoryKind::BitVector,
        TheoryLemmaKind::ArraySelectStore { .. } | TheoryLemmaKind::ArrayExtensionality => {
            AYTheoryKind::Array
        }
        TheoryLemmaKind::StringLengthAxiom
        | TheoryLemmaKind::StringContentAxiom
        | TheoryLemmaKind::StringNormalForm => AYTheoryKind::Sequence,
        _ => AYTheoryKind::Other,
    }
}

// ---------------------------------------------------------------------------
// Proof -> AYProofArtifact conversion
// ---------------------------------------------------------------------------

/// A converted proof plus what the kernel will take on trust in it.
#[derive(Debug, Clone)]
pub(crate) struct ConvertedProof {
    pub(crate) artifact: AYProofArtifact,
    /// Theory lemmas (and exact SOS theorems) fed to the kernel as axioms.
    pub(crate) trusted_theory_lemmas: u32,
    /// Generic rule steps fed to the kernel as input clauses that neither the
    /// kernel nor the bridge derived (every `hole` and `trust` step among
    /// them), plus step variants the bridge does not know.
    pub(crate) trusted_rule_steps: u32,
}

/// Every term id a proof step names.
fn step_term_ids(step: &ProofStep) -> Vec<TermId> {
    match step {
        ProofStep::Assume(term) => vec![*term],
        ProofStep::Resolution { clause, pivot, .. } => clause
            .iter()
            .copied()
            .chain(std::iter::once(*pivot))
            .collect(),
        ProofStep::TheoryLemma { clause, .. } | ProofStep::NraSos { clause, .. } => clause.clone(),
        ProofStep::Step { clause, args, .. } => clause.iter().chain(args.iter()).copied().collect(),
        _ => Vec::new(),
    }
}

/// The conclusion of one step the bridge has already settled: derived and
/// checked, or taken on trust and counted. As terms (for the propositional
/// check) and as kernel literals (for resolution).
struct Settled<'p> {
    terms: &'p [TermId],
    lits: BTreeSet<i64>,
}

/// The settled conclusions, in proof order. A step's conclusion enters only
/// after its own rule is decided, so every entry is a step before the one
/// being decided.
struct SettledSet<'p> {
    steps: HashMap<u64, Settled<'p>>,
}

impl<'p> SettledSet<'p> {
    /// The conclusion step `step` cites as `premise`, which must be an earlier
    /// step whose conclusion is settled. A citation of the citing step itself
    /// or of a later step (and so any cycle) is refused, as is one of an
    /// earlier step that concludes no clause (an anchor, an unknown variant).
    fn cite(&self, step: usize, premise: ProofId) -> Result<&Settled<'p>, String> {
        let cited = premise.0 as usize;
        if cited >= step {
            return Err(format!(
                "step {step} cites step {cited}, which is not an earlier step: \
                 a proof is checked in its own order, so a step may rely only on \
                 conclusions already checked"
            ));
        }
        self.steps
            .get(&u64::from(premise.0))
            .ok_or_else(|| format!("step {step} cites step {cited}, which concludes no clause"))
    }

    fn settle(&mut self, step: u64, terms: &'p [TermId], lits: BTreeSet<i64>) {
        self.steps.insert(step, Settled { terms, lits });
    }
}

/// The binary resolvent of `a` and `b` on `pivot` (either polarity
/// arrangement, as the kernel reads it), or `None` when `pivot` does not
/// occur in one parent and its complement in the other.
fn resolve(a: &BTreeSet<i64>, b: &BTreeSet<i64>, pivot: i64) -> Option<BTreeSet<i64>> {
    let (pos, neg) = if a.contains(&pivot) && b.contains(&-pivot) {
        (a, b)
    } else if a.contains(&-pivot) && b.contains(&pivot) {
        (b, a)
    } else {
        return None;
    };
    Some(
        pos.iter()
            .copied()
            .filter(|lit| *lit != pivot)
            .chain(neg.iter().copied().filter(|lit| *lit != -pivot))
            .collect(),
    )
}

/// Convert a `ay_core::Proof` into the kernel's input, deciding for every
/// clause whether the kernel derives it, the bridge checks it, or it is
/// trusted (see the module docs).
///
/// The proof is read once, in its own order. A step may cite only earlier
/// steps whose conclusions are already settled, and its own conclusion is
/// settled only after its rule is decided: a resolution is re-derived from its
/// parents, a generic step is re-derived or checked from its premises or else
/// counted as trusted. No claimed conclusion is ever relied on before it is
/// checked or counted, so no step can justify itself, through a cycle or
/// otherwise. The kernel then replays every resolution again on its own.
///
/// `terms` must be the store the proof's `TermId`s index.
///
/// # Errors
///
/// When a step names a term outside `terms`, cites a step that is not an
/// earlier one with a settled conclusion, states a resolvent its parents do
/// not give, or no checked step derives the empty clause.
pub(crate) fn convert_proof_to_artifact(
    proof: &Proof,
    terms: &TermStore,
) -> Result<ConvertedProof, String> {
    if proof.steps.is_empty() {
        return Err("the proof has no steps".to_string());
    }
    let store_len = terms.len();
    if let Some(id) = proof
        .steps
        .iter()
        .flat_map(step_term_ids)
        .find(|id| id.0 as usize >= store_len)
    {
        return Err(format!(
            "the proof names term {} outside its term snapshot ({store_len} entries)",
            id.0
        ));
    }

    let mut input_clauses = Vec::new();
    let mut resolution_steps = Vec::new();
    let mut theory_lemmas = Vec::new();
    let mut trusted_theory_lemmas = 0u32;
    let mut trusted_rule_steps = 0u32;
    let mut last_empty_candidate: Option<u64> = None;
    let mut settled = SettledSet {
        steps: HashMap::new(),
    };
    // Intermediate resolvents of a re-derived chain sit above every real
    // step id, so they cannot collide with one.
    let mut next_synthetic_id = proof.steps.len() as u64;
    let lits_of =
        |clause: &[TermId]| -> Vec<i64> { clause.iter().map(|t| literal(terms, *t)).collect() };

    for (idx, step) in proof.steps.iter().enumerate() {
        let step_id = idx as u64;
        match step {
            ProofStep::Assume(term_id) => {
                let lit = literal(terms, *term_id);
                input_clauses.push(AYClause {
                    id: step_id,
                    literals: vec![lit],
                });
                settled.settle(
                    step_id,
                    std::slice::from_ref(term_id),
                    std::iter::once(lit).collect(),
                );
            }
            ProofStep::Resolution {
                clause,
                pivot,
                clause1,
                clause2,
            } => {
                let pivot_lit = literal(terms, *pivot);
                let stated: BTreeSet<i64> = lits_of(clause).into_iter().collect();
                let resolvent = resolve(
                    &settled.cite(idx, *clause1)?.lits,
                    &settled.cite(idx, *clause2)?.lits,
                    pivot_lit,
                )
                .ok_or_else(|| {
                    format!(
                        "resolution step {idx}: the pivot does not occur with opposite \
                         polarities in its parents"
                    )
                })?;
                if resolvent != stated {
                    return Err(format!(
                        "resolution step {idx} states a clause its parents do not resolve to"
                    ));
                }
                resolution_steps.push(AYResolutionStep {
                    result_id: step_id,
                    pivot: pivot_lit,
                    antecedent_a: u64::from(clause1.0),
                    antecedent_b: u64::from(clause2.0),
                    result_literals: Some(stated.iter().copied().collect()),
                });
                if clause.is_empty() {
                    last_empty_candidate = Some(step_id);
                }
                settled.settle(step_id, clause, stated);
            }
            ProofStep::TheoryLemma { clause, kind, .. } => {
                let literals = lits_of(clause);
                trusted_theory_lemmas = trusted_theory_lemmas.saturating_add(1);
                theory_lemmas.push(AYTheoryLemma {
                    id: step_id,
                    kind: map_theory_kind(kind),
                    literals: literals.clone(),
                });
                settled.settle(step_id, clause, literals.into_iter().collect());
            }
            ProofStep::NraSos { clause, .. } => {
                let literals = lits_of(clause);
                trusted_theory_lemmas = trusted_theory_lemmas.saturating_add(1);
                theory_lemmas.push(AYTheoryLemma {
                    id: step_id,
                    kind: AYTheoryKind::Other,
                    literals: literals.clone(),
                });
                settled.settle(step_id, clause, literals.into_iter().collect());
            }
            ProofStep::Step {
                rule,
                clause,
                premises,
                ..
            } => {
                let cited = premises
                    .iter()
                    .map(|premise| settled.cite(idx, *premise))
                    .collect::<Result<Vec<_>, _>>()?;
                let literals = lits_of(clause);
                let conclusion: BTreeSet<i64> = literals.iter().copied().collect();
                let checked = if matches!(rule, AletheRule::Hole | AletheRule::Trust) {
                    // The producer says it did not prove this step. It is
                    // taken as given and counted, whatever it concludes.
                    trusted_rule_steps = trusted_rule_steps.saturating_add(1);
                    input_clauses.push(AYClause {
                        id: step_id,
                        literals,
                    });
                    false
                } else {
                    let chain = if matches!(rule, AletheRule::Resolution | AletheRule::ThResolution)
                    {
                        rederive_resolution_chain(
                            premises,
                            &cited,
                            &conclusion,
                            step_id,
                            &mut next_synthetic_id,
                        )
                    } else {
                        None
                    };
                    if let Some(chain) = chain {
                        resolution_steps.extend(chain);
                        true
                    } else {
                        let premise_clauses: Vec<&[TermId]> =
                            cited.iter().map(|premise| premise.terms).collect();
                        let entailed = propositionally_entailed(terms, &premise_clauses, clause);
                        if !entailed {
                            trusted_rule_steps = trusted_rule_steps.saturating_add(1);
                        }
                        input_clauses.push(AYClause {
                            id: step_id,
                            literals,
                        });
                        entailed
                    }
                };
                // Only a CHECKED step may stand as the empty clause: an
                // unchecked input clause that is already empty would make the
                // whole derivation vacuous.
                if checked && clause.is_empty() {
                    last_empty_candidate = Some(step_id);
                }
                settled.settle(step_id, clause, conclusion);
            }
            ProofStep::Anchor { .. } => {
                // Subproof anchors do not produce clauses.
            }
            // `ProofStep` is non-exhaustive. An unknown variant settles no
            // clause, so a step citing it is refused; it is still counted,
            // because nobody looked at it.
            _ => {
                trusted_rule_steps = trusted_rule_steps.saturating_add(1);
            }
        }
    }

    let empty_clause_id = last_empty_candidate
        .ok_or_else(|| "no checked step derives the empty clause".to_string())?;

    Ok(ConvertedProof {
        artifact: AYProofArtifact {
            input_clauses,
            resolution_steps,
            theory_lemmas,
            empty_clause_id,
        },
        trusted_theory_lemmas,
        trusted_rule_steps,
    })
}

/// Re-derive a generic n-ary Alethe `resolution` step as binary resolutions.
///
/// `cited` are the settled conclusions of `premises`, in order. Resolves them
/// left to right, each time on the first literal of the running resolvent
/// whose complement occurs in the next premise. Returns the binary steps (the
/// last one carries `final_id` and the step's stated `conclusion`, so the
/// kernel checks the conclusion), or `None` when the chain cannot be
/// re-derived this way.
fn rederive_resolution_chain(
    premises: &[ProofId],
    cited: &[&Settled<'_>],
    conclusion: &BTreeSet<i64>,
    final_id: u64,
    next_synthetic_id: &mut u64,
) -> Option<Vec<AYResolutionStep>> {
    if premises.len() < 2 || premises.len() != cited.len() {
        return None;
    }
    let mut acc_id = u64::from(premises[0].0);
    let mut acc = cited[0].lits.clone();
    let mut steps = Vec::with_capacity(premises.len() - 1);
    for (pos, (premise, other)) in premises.iter().zip(cited).enumerate().skip(1) {
        let other = &other.lits;
        let pivot = acc.iter().copied().find(|lit| other.contains(&-lit))?;
        let resolvent = resolve(&acc, other, pivot)?;
        let result_id = if pos + 1 == premises.len() {
            if &resolvent != conclusion {
                return None;
            }
            final_id
        } else {
            let id = *next_synthetic_id;
            *next_synthetic_id += 1;
            id
        };
        steps.push(AYResolutionStep {
            result_id,
            pivot,
            antecedent_a: acc_id,
            antecedent_b: u64::from(premise.0),
            result_literals: Some(resolvent.iter().copied().collect()),
        });
        acc_id = result_id;
        acc = resolvent;
    }
    Some(steps)
}

// ---------------------------------------------------------------------------
// Kernel check
// ---------------------------------------------------------------------------

/// The trust-vc-kernel's verdict on one proof, with what it took on trust.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct KernelCheck {
    /// The kernel replayed the refutation: every resolution re-derived, every
    /// theory lemma structurally well formed, the empty clause derived by a
    /// checked step.
    pub(crate) skeleton_accepted: bool,
    /// Theory lemmas the kernel took as axioms (see [`ConvertedProof`]).
    pub(crate) trusted_theory_lemmas: u32,
    /// Generic rule steps the kernel took as inputs (see [`ConvertedProof`]).
    pub(crate) trusted_rule_steps: u32,
    /// Why the kernel did not accept the proof, when it did not.
    pub(crate) refusal: Option<String>,
}

impl KernelCheck {
    pub(crate) fn refused(reason: impl Into<String>) -> Self {
        Self {
            skeleton_accepted: false,
            trusted_theory_lemmas: 0,
            trusted_rule_steps: 0,
            refusal: Some(reason.into()),
        }
    }

    /// Every clause the kernel took on trust, theory lemmas and rule steps.
    /// (`ProofCertificate::kernel_trusted_steps` is the public reading.)
    #[cfg(test)]
    pub(crate) const fn trusted_steps(&self) -> u32 {
        self.trusted_theory_lemmas
            .saturating_add(self.trusted_rule_steps)
    }
}

/// Run a ay proof through the trust-vc-kernel independent checker.
///
/// `terms` must be the store the proof's `TermId`s index (a positional
/// snapshot of the solver's store is fine).
#[must_use]
pub(crate) fn check_proof_with_kernel(proof: &Proof, terms: &TermStore) -> KernelCheck {
    let converted = match convert_proof_to_artifact(proof, terms) {
        Ok(converted) => converted,
        Err(reason) => {
            tracing::debug!(%reason, "kernel bridge: proof not converted");
            return KernelCheck::refused(reason);
        }
    };
    let trace = trust_vc_kernel::bridge::convert_ay_artifact(&converted.artifact);
    let checked = trust_vc_kernel::check_proof_with_theory(&trace);
    match &checked.result {
        CheckResult::Valid => KernelCheck {
            skeleton_accepted: true,
            trusted_theory_lemmas: converted.trusted_theory_lemmas,
            trusted_rule_steps: converted.trusted_rule_steps,
            refusal: None,
        },
        CheckResult::Invalid { step, reason } => {
            tracing::debug!(
                step,
                reason = reason.as_str(),
                "kernel bridge: proof rejected"
            );
            KernelCheck::refused(format!("kernel rejected step {step}: {reason}"))
        }
        _ => KernelCheck::refused("unknown kernel check result"),
    }
}

// ---------------------------------------------------------------------------
// Premise binding
// ---------------------------------------------------------------------------

/// The query trust-vc posed for the last check, rebuilt from the solver API's
/// transcript of trust-vc's own calls (see the module docs).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct PosedQuery {
    terms: HashSet<TermId>,
}

impl PosedQuery {
    /// Replay `events` into the live assertion stack, plus the assumptions of
    /// the final check when it was a `check-sat-assuming`.
    ///
    /// # Errors
    ///
    /// When the transcript pops a scope it never pushed.
    pub(crate) fn from_transcript(events: &[NativeReplayEvent]) -> Result<Self, String> {
        let mut frames: Vec<Vec<TermId>> = vec![Vec::new()];
        let mut final_assumptions: Vec<TermId> = Vec::new();
        for event in events {
            match &event.kind {
                NativeReplayEventKind::Assert { term, .. } => {
                    if let Some(frame) = frames.last_mut() {
                        frame.push(*term);
                    }
                }
                NativeReplayEventKind::Push => frames.push(Vec::new()),
                NativeReplayEventKind::Pop => {
                    if frames.len() < 2 {
                        return Err(format!(
                            "the solver transcript pops an unpushed scope at event {}",
                            event.index
                        ));
                    }
                    frames.pop();
                }
                NativeReplayEventKind::Reset | NativeReplayEventKind::ResetAssertions => {
                    frames = vec![Vec::new()];
                    final_assumptions.clear();
                }
                NativeReplayEventKind::CheckSat => final_assumptions.clear(),
                NativeReplayEventKind::CheckSatAssuming { assumptions } => {
                    final_assumptions.clone_from(assumptions);
                }
                _ => {}
            }
        }
        Ok(Self {
            terms: frames
                .into_iter()
                .flatten()
                .chain(final_assumptions)
                .collect(),
        })
    }

    #[cfg(test)]
    pub(crate) fn from_terms(terms: impl IntoIterator<Item = TermId>) -> Self {
        Self {
            terms: terms.into_iter().collect(),
        }
    }

    pub(crate) fn contains(&self, term: TermId) -> bool {
        self.terms.contains(&term)
    }
}

/// Check that every `assume` premise of `proof` is a term of `posed`, or an
/// exact instance of a universally quantified term of `posed`.
///
/// The instance case is definitional adoption: AY may answer an asserted
/// `forall x. f(x) = x + 1` by asserting `f(1) = 1 + 1` for an application
/// `f(1)` it already holds, and the proof then assumes that instance. An
/// instance is entailed by its `forall`, so a refutation that assumes it is
/// still a refutation of the posed query. `terms`, when given, is the store
/// the proof's ids index; without it only posed terms themselves bind.
///
/// # Errors
///
/// The first reason the premises cannot be read as the posed query.
pub(crate) fn bind_premises(
    proof: &Proof,
    terms: Option<&TermStore>,
    posed: &PosedQuery,
) -> Result<(), String> {
    let mut assumes = 0usize;
    for (index, step) in proof.steps.iter().enumerate() {
        let ProofStep::Assume(term) = step else {
            continue;
        };
        assumes += 1;
        let bound = posed.contains(*term)
            || terms.is_some_and(|store| posed.has_forall_instantiating_to(store, *term));
        if !bound {
            return Err(format!(
                "assume step {index} (term {}) is not a term trust-vc asserted for this query",
                term.0
            ));
        }
    }
    if assumes == 0 {
        return Err("the proof assumes no clause of the query".to_string());
    }
    Ok(())
}

/// Most term nodes one instance match visits.
const INSTANCE_MAX_NODES: usize = 4096;

/// Matches a `forall` body against a candidate instance, binding each binder
/// to the term at its occurrences. The body must be free of nested binders
/// and `let`, so no instantiation can capture a variable.
struct InstanceMatcher<'a> {
    terms: &'a TermStore,
    binders: &'a [(String, ay_core::Sort)],
    bound: Vec<Option<TermId>>,
    nodes: usize,
}

impl<'a> InstanceMatcher<'a> {
    /// The binder `pattern` names, if it is a variable named like one. A
    /// variable that shares a binder's name at another sort is no match at
    /// all (`Err`), never a free symbol.
    fn binder_of(&self, pattern: TermId) -> Result<Option<usize>, ()> {
        let TermData::Var(name, _) = self.terms.get(pattern) else {
            return Ok(None);
        };
        match self.binders.iter().position(|(binder, _)| binder == name) {
            Some(index) if self.binders[index].1 == *self.terms.sort(pattern) => Ok(Some(index)),
            Some(_) => Err(()),
            None => Ok(None),
        }
    }

    /// True iff `pattern` under the binding is exactly `term`.
    fn matches(&mut self, pattern: TermId, term: TermId) -> bool {
        self.nodes += 1;
        if self.nodes > INSTANCE_MAX_NODES || self.terms.sort(pattern) != self.terms.sort(term) {
            return false;
        }
        match self.binder_of(pattern) {
            Err(()) => return false,
            Ok(Some(index)) => {
                if let Some(previous) = self.bound[index] {
                    return previous == term;
                }
                if !self.binder_free(term) {
                    return false;
                }
                self.bound[index] = Some(term);
                return true;
            }
            Ok(None) => {}
        }
        let terms = self.terms;
        match (terms.get(pattern), terms.get(term)) {
            (TermData::Const(a), TermData::Const(b)) => a == b,
            (TermData::Var(..), _) => pattern == term,
            (TermData::Not(p), TermData::Not(t)) => self.matches(*p, *t),
            (TermData::Ite(pc, pt, pe), TermData::Ite(tc, tt, te)) => {
                self.matches(*pc, *tc) && self.matches(*pt, *tt) && self.matches(*pe, *te)
            }
            (TermData::App(ps, pargs), TermData::App(ts, targs)) => {
                ps == ts
                    && pargs.len() == targs.len()
                    && pargs.iter().zip(targs).all(|(p, t)| self.matches(*p, *t))
            }
            _ => false,
        }
    }

    /// True iff `term` holds no binder and no `let` (within the node cap).
    fn binder_free(&mut self, term: TermId) -> bool {
        self.nodes += 1;
        if self.nodes > INSTANCE_MAX_NODES {
            return false;
        }
        let terms = self.terms;
        match terms.get(term) {
            TermData::Const(_) | TermData::Var(..) => true,
            TermData::Not(t) => self.binder_free(*t),
            TermData::Ite(c, t, e) => {
                self.binder_free(*c) && self.binder_free(*t) && self.binder_free(*e)
            }
            TermData::App(_, args) => args.iter().all(|arg| self.binder_free(*arg)),
            _ => false,
        }
    }
}

impl PosedQuery {
    /// True iff `term` is the exact simultaneous instance of the body of some
    /// posed `forall` whose body has no nested binder or `let`, with every
    /// binder sort kept and every instantiating term binder-free.
    fn has_forall_instantiating_to(&self, terms: &TermStore, term: TermId) -> bool {
        let store_len = terms.len();
        if term.0 as usize >= store_len {
            return false;
        }
        self.terms.iter().any(|posed| {
            if posed.0 as usize >= store_len {
                return false;
            }
            let TermData::Forall(binders, body, _) = terms.get(*posed) else {
                return false;
            };
            let distinct: HashSet<&str> = binders.iter().map(|(name, _)| name.as_str()).collect();
            if binders.is_empty() || distinct.len() != binders.len() {
                return false;
            }
            let mut matcher = InstanceMatcher {
                terms,
                binders,
                bound: vec![None; binders.len()],
                nodes: 0,
            };
            matcher.binder_free(*body) && {
                matcher.nodes = 0;
                matcher.matches(*body, term)
            }
        })
    }
}

/// True iff some `assume` premise of `proof` is the constant `false`
/// (`false_term`, or `not true`): the query had collapsed to `false` when it
/// was built (see the module docs).
///
/// `terms`, when given, is the store the proof's ids index; without it the
/// `false` constant is recognized by its preallocated id alone.
pub(crate) fn assumes_false(proof: &Proof, terms: Option<&TermStore>) -> bool {
    let is_false = |t: TermId| match terms {
        Some(store) if (t.0 as usize) < store.len() => {
            store.is_false(t)
                || matches!(store.get(t), TermData::Not(inner) if store.is_true(*inner))
        }
        _ => t == TermStore::PREALLOCATED_FALSE,
    };
    proof
        .steps
        .iter()
        .any(|step| matches!(step, ProofStep::Assume(term) if is_false(*term)))
}

// ---------------------------------------------------------------------------
// Solve-site entry point
// ---------------------------------------------------------------------------

/// What one refutation is evidence for, and how much of it the kernel checked.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CertificateEvidence {
    /// `Ok` iff the proof's premises are clauses of the posed query.
    pub(crate) binding: Result<(), String>,
    /// The kernel's verdict on the derivation.
    pub(crate) kernel: KernelCheck,
    /// A premise is the constant `false` (see [`assumes_false`]).
    pub(crate) query_collapsed: bool,
    /// Premises that are predicates trust-vc proved by a separate solve and
    /// then assumed (see [`certify_last_refutation`]).
    pub(crate) assumed_lemma_premises: u32,
}

impl CertificateEvidence {
    pub(crate) fn unchecked(reason: &str) -> Self {
        Self {
            binding: Err(reason.to_string()),
            kernel: KernelCheck::refused(reason),
            query_collapsed: false,
            assumed_lemma_premises: 0,
        }
    }
}

/// Bind the solver's last UNSAT proof to the query trust-vc posed, whose
/// negated goal is `negated_goal`, and run the kernel on it.
///
/// `assumed_lemmas` are the terms of the posed query that trust-vc proved by a
/// separate solve before assuming them (the no-overflow and
/// collection-precondition predicates of the Assert+Assume pattern). That
/// solve records no certificate, so the premises among them are counted and
/// disclosed: the certificate refutes the posed query, and its evidence for
/// the obligation also rests on those solves' verdicts.
pub(crate) fn certify_last_refutation(
    solver: &ay_dpll::api::Solver,
    negated_goal: ay_dpll::api::Term,
    assumed_lemmas: &[TermId],
) -> CertificateEvidence {
    let Some(proof) = solver.last_proof() else {
        return CertificateEvidence::unchecked("the solver kept no proof for this refutation");
    };
    let posed = match PosedQuery::from_transcript(solver.native_replay_events()) {
        Ok(posed) => posed,
        Err(reason) => return CertificateEvidence::unchecked(&reason),
    };
    if !posed.contains(negated_goal.id()) {
        return CertificateEvidence::unchecked(
            "the solver transcript does not hold the negated goal trust-vc asserted",
        );
    }
    // The proof's term ids index the solver's store; the bundle carries a
    // positional snapshot of it. It must carry exactly this proof.
    let store = solver
        .export_last_unsat_bundle()
        .filter(|bundle| bundle.steps == proof.steps)
        .map(|bundle| {
            TermStore::from_entries(
                bundle.term_entries,
                bundle.true_term,
                bundle.false_term,
                bundle.var_counter,
            )
        });
    let binding = bind_premises(proof, store.as_ref(), &posed);
    if let Err(reason) = &binding {
        tracing::debug!(%reason, "proof certificate premises are not the posed query");
    }
    let kernel = match &store {
        Some(store) => check_proof_with_kernel(proof, store),
        None => KernelCheck::refused("no term snapshot of this proof is available"),
    };
    let assumed_lemma_premises = proof
        .steps
        .iter()
        .filter(|step| matches!(step, ProofStep::Assume(term) if assumed_lemmas.contains(term)))
        .count();
    CertificateEvidence {
        binding,
        kernel,
        query_collapsed: assumes_false(proof, store.as_ref()),
        assumed_lemma_premises: u32::try_from(assumed_lemma_premises).unwrap_or(u32::MAX),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests;
