// trust-vc-core — Specification stubs for ay-dpll self-verification
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// This module contains specification stubs (as doc comments) for key ay-dpll
// functions that trust_vc could verify. These are documentation-only contracts
// that describe the pre/postconditions of ay-dpll's core algorithms.
//
// These stubs do NOT compile against ay types. They serve as:
// 1. Formal documentation of ay-dpll's expected invariants
// 2. Templates for future `#[contract]` annotations on ay-dpll functions
// 3. Input for the trust_vc `extern_spec!` mechanism when cross-crate
//    verification is ready
//
// Historical source snapshot: ay-dpll rev
// 288ef6dd8f9dbfe973a21c584456bebe501b3256. Current TrustVc ay pin is the
// workspace dependency revision in Cargo.toml.
// Reference: designs/2026-03-28-self-verifying-solver.md

// ---------------------------------------------------------------------------
// 1. register_theory_atom (ay-dpll/src/lib.rs:360-380)
// ---------------------------------------------------------------------------
//
// Registers a bidirectional mapping between a theory term and a SAT variable.
// Called during formula preprocessing to inform the DPLL(T) layer which SAT
// variables correspond to theory-relevant atoms.
//
// fn register_theory_atom(&mut self, term: TermId, var: u32)
//
// ## Preconditions
//
// requires! {
//     // The SAT variable must be valid (within solver's variable range)
//     var < self.sat.num_vars() as u32,
// }
//
// ## Postconditions
//
// ensures! {
//     // Bidirectional mapping is established
//     self.var_to_term.get(&var) == Some(&term),
//     self.term_to_var.get(&term) == Some(&var),
//
//     // Theory atom is recorded exactly once (idempotent for duplicates)
//     self.theory_atom_set.contains(&term),
//     self.theory_atoms.contains(&term),
//
//     // No duplicates in the ordered atom list
//     self.theory_atoms.len() == self.theory_atom_set.len(),
//
//     // Variable is frozen in SAT solver (excluded from elimination)
//     self.sat.is_frozen(Variable::new(var)),
//
//     // Theory solver has been notified of the atom
//     // (cannot be expressed as a postcondition on self alone;
//     //  the theory solver's internalize_atom was called)
// }

// ---------------------------------------------------------------------------
// 2. term_to_literal (ay-dpll/src/lib.rs:393-401)
// ---------------------------------------------------------------------------
//
// Converts a theory term + polarity to a SAT literal. Returns None if the
// term is not registered.
//
// fn term_to_literal(&self, term: TermId, value: bool) -> Option<Literal>
//
// ## Preconditions
//
// requires! {
//     // No preconditions beyond valid self reference
//     true,
// }
//
// ## Postconditions
//
// ensures! { |result: Option<Literal>|
//     // If term is registered, we get a literal
//     (self.term_to_var.contains_key(&term)) ==>
//         result.is_some(),
//
//     // If term is not registered, we get None
//     (!self.term_to_var.contains_key(&term)) ==>
//         result.is_none(),
//
//     // When Some, the literal's variable matches the registered mapping
//     result.is_some() ==> {
//         let lit = result.unwrap();
//         let expected_var = self.term_to_var[&term];
//         lit.variable().id() == expected_var
//     },
//
//     // When Some, the literal's polarity matches the requested value
//     result.is_some() ==> {
//         let lit = result.unwrap();
//         lit.is_positive() == value
//     },
// }

// ---------------------------------------------------------------------------
// 3. term_to_literal_or_register (ay-dpll/src/lib.rs:412-425)
// ---------------------------------------------------------------------------
//
// Like term_to_literal, but dynamically registers unknown terms by creating
// a new SAT variable. Used during theory checking where array axiom terms
// may not have been registered during preprocessing.
//
// fn term_to_literal_or_register(&mut self, term: TermId, value: bool) -> Literal
//
// ## Preconditions
//
// requires! {
//     // No preconditions — the function handles both registered and
//     // unregistered terms gracefully
//     true,
// }
//
// ## Postconditions
//
// ensures! { |result: Literal|
//     // The term is always registered after this call
//     self.term_to_var.contains_key(&term),
//     self.var_to_term.contains_key(&result.variable().id()),
//
//     // The returned literal's polarity matches the requested value
//     result.is_positive() == value,
//
//     // The literal's variable maps back to the original term
//     self.var_to_term[&result.variable().id()] == term,
//
//     // Bidirectional consistency
//     self.term_to_var[&term] == result.variable().id(),
// }

// ---------------------------------------------------------------------------
// 4. sync_theory (ay-dpll/src/lib.rs:450-479)
// ---------------------------------------------------------------------------
//
// Communicates a SAT model to the theory solver. For each registered theory
// atom, asserts the atom's value (from the model) to the theory solver.
// Uses push/pop scoping to preserve learned theory state across rounds.
//
// fn sync_theory(&mut self, model: &[bool])
//
// ## Preconditions
//
// requires! {
//     // Model must cover all variables used by theory atoms
//     forall!(|atom: TermId| self.theory_atom_set.contains(&atom) ==> {
//         let var = self.term_to_var[&atom];
//         (var as usize) < model.len()
//     }),
// }
//
// ## Postconditions
//
// ensures! {
//     // Model scope is active after sync (will be popped before next sync)
//     self.model_scope_active == true,
//
//     // Every theory atom has been asserted with its model value
//     // (This is a semantic postcondition — the theory solver received
//     //  assert_literal(term, model[var_idx]) for each theory atom.
//     //  Cannot be directly checked on self, but the coverage invariant
//     //  is: every atom in theory_atoms was visited.)
//
//     // Theory solver had push() called exactly once more than pop()
//     // relative to the pre-call state (one new scope level)
// }

// ---------------------------------------------------------------------------
// 5. solve_loop (ay-dpll/src/lib.rs:756-915)
// ---------------------------------------------------------------------------
//
// The main DPLL(T) refinement loop. Alternates between SAT solving and
// theory consistency checking until a final result is reached.
//
// fn solve_loop(
//     &mut self,
//     assumptions: Option<&[Literal]>,
//     tracking: Option<(&mut ProofTracker, &HashMap<TermId, TermId>)>,
// ) -> Result<AssumeResult, DpllError>
//
// ## Preconditions
//
// requires! {
//     // Theory solver has been reset before entering the loop
//     // (caller responsibility — solve_impl calls theory.reset() before this)
//
//     // Model scope is not active on entry
//     !self.model_scope_active,
// }
//
// ## Postconditions
//
// ensures! { |result: Result<AssumeResult, DpllError>|
//     // Model scope is always cleaned up on return
//     !self.model_scope_active,
//
//     // SAT result soundness:
//     // If Sat(model) is returned, the theory solver accepted the model
//     // (the final check passed)
//     result.is_ok() && matches!(result.unwrap(), AssumeResult::Sat(_)) ==> {
//         // Theory dispatch was Accept, AND the final N-O check (if needed)
//         // also returned Accept. The model is theory-consistent.
//         true // expressed as: theory.check() returned Sat on the final model
//     },
//
//     // UNSAT soundness:
//     // If Unsat is returned, the SAT solver itself reported UNSAT
//     // (theory conflicts added clauses that made the formula unsatisfiable)
//     result.is_ok() && matches!(result.unwrap(), AssumeResult::Unsat(_)) ==> {
//         // The SAT solver exhausted all branches. Theory conflict clauses
//         // are logical consequences of the original formula, so UNSAT is sound.
//         true
//     },
//
//     // Termination guarantee:
//     // The loop executed at most MAX_THEORY_REFINEMENTS (10,000) iterations.
//     // If the limit is reached, Unknown is returned (not an infinite loop).
//     self.timings.round_trips <= old(self.timings.round_trips) + 10_000,
// }

// ---------------------------------------------------------------------------
// 6. check_theory_core — propagation clause shape (theory_check.rs:47-639)
// ---------------------------------------------------------------------------
//
// Checks theory consistency. Drains propagations from the theory solver,
// converts them to SAT clauses, and handles conflicts.
//
// fn check_theory_core(
//     &mut self,
//     tracking: Option<(&mut ProofTracker, &HashMap<TermId, TermId>)>,
// ) -> TheoryCheck
//
// ## Key invariant: Propagation clause correctness
//
// For each theory propagation { literal: (term, value), reason: [(r1, v1), ...] },
// the clause added to the SAT solver has the form:
//
//   (NOT(r1, v1) OR NOT(r2, v2) OR ... OR (term, value))
//
// Which encodes: "if all reasons hold, then the propagated literal holds."
//
// requires! {
//     // Theory atoms are registered and have SAT variable mappings
//     // (or will be dynamically registered via term_to_literal_or_register)
//     true,
// }
//
// ensures! { |result: TheoryCheck|
//     // Propagation clause shape:
//     // Every clause added to SAT has the form: negated reasons + propagated literal
//     // This is checked structurally in the implementation:
//     //   clause = [neg(r1), neg(r2), ..., lit]
//     //   where lit = term_to_literal_or_register(prop.literal.term, prop.literal.value)
//     //   and neg(ri) = term_to_literal_or_register(ri.term, !ri.value)
//
//     // Conflict clause shape:
//     // Every conflict clause negates all conflict literals:
//     //   clause = [neg(c1), neg(c2), ...]
//     //   where neg(ci) = term_to_literal_or_register(ci.term, !ci.value)
//
//     // Partial clause safety:
//     // If any term cannot be mapped to a SAT literal and dynamic registration
//     // fails, the function returns TheoryCheck::Unknown (fail-safe)
//     // rather than adding a truncated clause (which would be unsound).
//
//     // Propagation count accuracy:
//     matches!(result, TheoryCheck::Propagated(n)) ==> {
//         // n equals the number of clauses actually added to the SAT solver
//         n > 0
//     },
//
//     // Conflict means a clause was added:
//     matches!(result, TheoryCheck::Conflict(ref clause)) ==> {
//         // clause is non-empty
//         !clause.is_empty()
//         // All literals in clause are valid SAT literals
//         // (registered in var_to_term / term_to_var)
//     },
//
//     // Sat means no propagations or conflicts found:
//     matches!(result, TheoryCheck::Sat) ==> {
//         // Theory's check_during_propagate() returned Sat
//         // AND no pending propagations exist
//         true
//     },
// }

// ---------------------------------------------------------------------------
// 7. BCP — propagate_bcp (ay-sat/solver/propagation_bcp.rs:87)
// ---------------------------------------------------------------------------
//
// Boolean Constraint Propagation using the two-watched literal scheme.
// This is the hottest loop in the solver — all clauses are scanned via
// watch lists when a literal is assigned.
//
// fn propagate_bcp<const MODE: u8>(&mut self) -> Option<ClauseRef>
//
// ## Preconditions
//
// requires! {
//     // Queue head is within trail bounds
//     self.qhead <= self.trail.len(),
//
//     // Watch lists are initialized and connected
//     !self.watches_disconnected,
//
//     // No pre-existing empty clause
//     !self.has_empty_clause,
//
//     // Two-watched literal invariant holds for all clauses:
//     // For every clause C with >= 2 literals:
//     //   C.lits[0] and C.lits[1] are the watched literals
//     //   C appears in the watch list of NOT(C.lits[0]) and NOT(C.lits[1])
// }
//
// ## Postconditions
//
// ensures! { |result: Option<ClauseRef>|
//     // No conflict case:
//     result.is_none() ==> {
//         // All unit implications have been propagated
//         self.qhead == self.trail.len()
//
//         // Watch invariant maintained: for every non-satisfied clause C,
//         // at least one of C's watched literals is unassigned
//     },
//
//     // Conflict case:
//     result.is_some() ==> {
//         let cref = result.unwrap();
//         // All literals in the conflict clause are false under current assignment
//         // forall!(|i: usize| i < clause_len(cref) ==>
//         //     self.lit_value(clause_lit(cref, i)) == Some(false))
//
//         // The conflict clause exists in the clause database
//         // (it is either an original clause or a learned clause)
//     },
//
//     // Trail monotonicity: literals are only added, never removed during BCP
//     self.trail.len() >= old(self.trail.len()),
//
//     // Assignment consistency: every literal on the trail has a consistent
//     // value in the vals[] array
// }

// ---------------------------------------------------------------------------
// 8. 1UIP Conflict Analysis (ay-sat/solver/conflict_analysis.rs:102)
// ---------------------------------------------------------------------------
//
// Analyzes a conflict to learn a new clause using the First Unique
// Implication Point scheme. The learned clause enables non-chronological
// backtracking (backjumping).
//
// fn analyze_conflict(&mut self, conflict_ref: ClauseRef) -> ConflictResult
//
// ## Preconditions
//
// requires! {
//     // Decision level must be > 0 (conflicts at level 0 are handled separately)
//     self.decision_level > 0,
//
//     // The conflict clause must have all literals false under current assignment
//     // forall!(|i: usize| i < clause_len(conflict_ref) ==>
//     //     self.lit_value(clause_lit(conflict_ref, i)) == Some(false))
// }
//
// ## Postconditions
//
// ensures! { |result: ConflictResult|
//     // The learned clause is an asserting clause:
//     // Exactly one literal is at the highest (conflict) decision level.
//     // This literal becomes the UIP — after backjumping, it will be
//     // unit-propagated by the learned clause.
//     //
//     // count(learned_lits, |l| level(l) == conflict_level) == 1
//
//     // Backjump level correctness:
//     // The backjump level is the second-highest level among learned literals.
//     // After backtracking to this level, the learned clause becomes unit
//     // (the UIP literal is the only unassigned literal).
//     //
//     // result.backjump_level == max(levels of learned_lits EXCEPT the UIP)
//
//     // Implication soundness:
//     // The learned clause is a logical consequence of the original clause
//     // database. It is derived by resolution from the conflict clause and
//     // reason clauses along the trail.
//     //
//     // This is the fundamental soundness property — if this is wrong,
//     // the solver can report UNSAT for satisfiable formulas.
//
//     // Minimality (weak):
//     // The learned clause has been minimized — no literal is subsumed
//     // by the remaining literals' reasons (recursive minimization).
// }
