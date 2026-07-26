// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Proof compaction: eliminates redundant steps from proof certificates.
//!
//! Proofs produced by ay-dpll may contain dead branches — resolution steps
//! and clauses that were explored during search but are not part of the
//! final derivation of the empty clause. This module removes such steps,
//! producing a minimal proof that is easier to check and export.

use std::collections::{HashMap, HashSet, VecDeque};

use crate::bridge::{AYClause, AYProofArtifact, AYResolutionStep, AYTheoryLemma};

/// Statistics about a proof compaction operation.
#[derive(Debug, Clone, Copy, PartialEq)]
#[non_exhaustive]
pub struct ProofStats {
    /// Number of steps (resolution + theory lemmas) in the original proof.
    pub original_steps: usize,
    /// Number of steps remaining after compaction.
    pub compacted_steps: usize,
    /// Number of steps removed.
    pub removed_steps: usize,
    /// Number of input clauses in the original proof.
    pub original_assumptions: usize,
    /// Number of input clauses actually referenced by the compacted proof.
    pub used_assumptions: usize,
    /// Ratio of compacted to original steps (0.0..=1.0).
    pub compression_ratio: f64,
    /// Number of disconnected subgraphs removed during compaction.
    pub dead_branch_count: usize,
}

/// Compact a proof artifact by removing steps unreachable from the final
/// empty clause derivation.
///
/// The algorithm:
/// 1. Builds a dependency graph from resolution steps to their antecedents.
/// 2. Walks backward from the `empty_clause_id` to mark all reachable steps.
/// 3. Strips unreachable resolution steps, theory lemmas, and input clauses.
/// 4. Renumbers all clause IDs to form a dense, contiguous sequence.
#[must_use]
pub fn compact_proof(artifact: &AYProofArtifact) -> AYProofArtifact {
    compact_with_stats(artifact).0
}

/// Compact a proof artifact and return statistics about the compaction.
#[must_use]
pub fn compact_with_stats(artifact: &AYProofArtifact) -> (AYProofArtifact, ProofStats) {
    let all_step_ids = collect_all_ids(artifact);

    // Edge case: empty proof or proof with no resolution steps.
    if artifact.resolution_steps.is_empty() {
        let used_assumptions = artifact
            .input_clauses
            .iter()
            .filter(|c| c.id == artifact.empty_clause_id)
            .count()
            + artifact
                .theory_lemmas
                .iter()
                .filter(|tl| tl.id == artifact.empty_clause_id)
                .count();

        let original_steps = artifact.resolution_steps.len() + artifact.theory_lemmas.len();

        let stats = ProofStats {
            original_steps,
            compacted_steps: original_steps,
            removed_steps: 0,
            original_assumptions: artifact.input_clauses.len(),
            used_assumptions: if used_assumptions > 0 {
                used_assumptions
            } else {
                artifact.input_clauses.len()
            },
            compression_ratio: 1.0,
            dead_branch_count: 0,
        };

        return (artifact.clone(), stats);
    }

    // Build dependency graph: step_id -> set of clause IDs it depends on.
    let step_deps = build_dependency_map(artifact);

    // Walk backward from the empty clause to find all reachable IDs.
    let reachable = find_reachable_ids(artifact.empty_clause_id, &step_deps);

    // Collect reachable elements.
    let kept_inputs: Vec<AYClause> = artifact
        .input_clauses
        .iter()
        .filter(|c| reachable.contains(&c.id))
        .cloned()
        .collect();

    let kept_lemmas: Vec<AYTheoryLemma> = artifact
        .theory_lemmas
        .iter()
        .filter(|tl| reachable.contains(&tl.id))
        .cloned()
        .collect();

    let kept_steps: Vec<AYResolutionStep> = artifact
        .resolution_steps
        .iter()
        .filter(|s| reachable.contains(&s.result_id))
        .cloned()
        .collect();

    // Build dense renumbering map. Preserve order: inputs, lemmas, steps.
    let mut renumber: HashMap<u64, u64> = HashMap::new();
    let mut next_id: u64 = 1;

    for c in &kept_inputs {
        renumber.entry(c.id).or_insert_with(|| {
            let id = next_id;
            next_id += 1;
            id
        });
    }
    for tl in &kept_lemmas {
        renumber.entry(tl.id).or_insert_with(|| {
            let id = next_id;
            next_id += 1;
            id
        });
    }
    for s in &kept_steps {
        renumber.entry(s.result_id).or_insert_with(|| {
            let id = next_id;
            next_id += 1;
            id
        });
    }

    // Apply renumbering.
    let new_inputs: Vec<AYClause> = kept_inputs
        .iter()
        .map(|c| AYClause {
            id: renumber[&c.id],
            literals: c.literals.clone(),
        })
        .collect();

    let new_lemmas: Vec<AYTheoryLemma> = kept_lemmas
        .iter()
        .map(|tl| AYTheoryLemma {
            id: renumber[&tl.id],
            kind: tl.kind,
            literals: tl.literals.clone(),
        })
        .collect();

    let new_steps: Vec<AYResolutionStep> = kept_steps
        .iter()
        .map(|s| AYResolutionStep {
            result_id: renumber[&s.result_id],
            pivot: s.pivot,
            antecedent_a: renumber[&s.antecedent_a],
            antecedent_b: renumber[&s.antecedent_b],
            result_literals: s.result_literals.clone(),
        })
        .collect();

    let new_empty_id = renumber
        .get(&artifact.empty_clause_id)
        .copied()
        .unwrap_or(artifact.empty_clause_id);

    let compacted = AYProofArtifact {
        input_clauses: new_inputs,
        resolution_steps: new_steps,
        theory_lemmas: new_lemmas,
        empty_clause_id: new_empty_id,
    };

    // Compute statistics.
    let original_steps = artifact.resolution_steps.len() + artifact.theory_lemmas.len();
    let compacted_steps = compacted.resolution_steps.len() + compacted.theory_lemmas.len();
    let removed_steps = original_steps.saturating_sub(compacted_steps);

    let dead_branch_count = count_dead_branches(artifact, &reachable, &all_step_ids);

    let compression_ratio = if original_steps == 0 {
        1.0
    } else {
        compacted_steps as f64 / original_steps as f64
    };

    let stats = ProofStats {
        original_steps,
        compacted_steps,
        removed_steps,
        original_assumptions: artifact.input_clauses.len(),
        used_assumptions: compacted.input_clauses.len(),
        compression_ratio,
        dead_branch_count,
    };

    (compacted, stats)
}

/// Find groups of steps forming disconnected subgraphs that are not
/// reachable from the final empty clause derivation.
///
/// Each returned `Vec<u64>` is a connected component of unreachable steps,
/// sorted by clause ID. The outer vector is sorted by the minimum ID in
/// each component.
#[must_use]
pub fn find_dead_branches(artifact: &AYProofArtifact) -> Vec<Vec<u64>> {
    let all_ids = collect_all_ids(artifact);
    let step_deps = build_dependency_map(artifact);
    let reachable = find_reachable_ids(artifact.empty_clause_id, &step_deps);

    let unreachable: HashSet<u64> = all_ids.difference(&reachable).copied().collect();

    if unreachable.is_empty() {
        return Vec::new();
    }

    // Build an undirected adjacency list over unreachable IDs.
    let mut adj: HashMap<u64, HashSet<u64>> = HashMap::new();
    for &id in &unreachable {
        adj.entry(id).or_default();
    }

    for step in &artifact.resolution_steps {
        if !unreachable.contains(&step.result_id) {
            continue;
        }
        for &dep in &[step.antecedent_a, step.antecedent_b] {
            if unreachable.contains(&dep) {
                adj.entry(step.result_id).or_default().insert(dep);
                adj.entry(dep).or_default().insert(step.result_id);
            }
        }
    }

    // BFS to find connected components.
    let mut visited: HashSet<u64> = HashSet::new();
    let mut components: Vec<Vec<u64>> = Vec::new();

    // Process in sorted order for deterministic output.
    let mut sorted_unreachable: Vec<u64> = unreachable.into_iter().collect();
    sorted_unreachable.sort_unstable();

    for &start in &sorted_unreachable {
        if visited.contains(&start) {
            continue;
        }

        let mut component = Vec::new();
        let mut queue = VecDeque::new();
        queue.push_back(start);
        visited.insert(start);

        while let Some(node) = queue.pop_front() {
            component.push(node);
            if let Some(neighbors) = adj.get(&node) {
                let mut sorted_neighbors: Vec<u64> = neighbors.iter().copied().collect();
                sorted_neighbors.sort_unstable();
                for neighbor in sorted_neighbors {
                    if visited.insert(neighbor) {
                        queue.push_back(neighbor);
                    }
                }
            }
        }

        component.sort_unstable();
        components.push(component);
    }

    // Sort components by their minimum ID.
    components.sort_by_key(|c| c.first().copied().unwrap_or(0));
    components
}

// ---------------------------------------------------------------------------
// Internal helpers
// ---------------------------------------------------------------------------

/// Collect all clause IDs present in the artifact (inputs, lemmas, steps).
fn collect_all_ids(artifact: &AYProofArtifact) -> HashSet<u64> {
    let mut ids = HashSet::new();
    for c in &artifact.input_clauses {
        ids.insert(c.id);
    }
    for tl in &artifact.theory_lemmas {
        ids.insert(tl.id);
    }
    for s in &artifact.resolution_steps {
        ids.insert(s.result_id);
    }
    ids
}

/// Build a map from each step's result ID to the set of clause IDs it
/// directly depends on (its antecedents).
fn build_dependency_map(artifact: &AYProofArtifact) -> HashMap<u64, Vec<u64>> {
    let mut deps: HashMap<u64, Vec<u64>> = HashMap::new();
    for step in &artifact.resolution_steps {
        deps.insert(step.result_id, vec![step.antecedent_a, step.antecedent_b]);
    }
    deps
}

/// Walk backward from `start_id` through the dependency map, collecting
/// all transitively reachable clause IDs.
fn find_reachable_ids(start_id: u64, deps: &HashMap<u64, Vec<u64>>) -> HashSet<u64> {
    let mut reachable = HashSet::new();
    let mut queue = VecDeque::new();
    queue.push_back(start_id);
    reachable.insert(start_id);

    while let Some(id) = queue.pop_front() {
        if let Some(parents) = deps.get(&id) {
            for &parent_id in parents {
                if reachable.insert(parent_id) {
                    queue.push_back(parent_id);
                }
            }
        }
    }

    reachable
}

/// Count the number of disconnected dead-branch components among
/// unreachable steps (resolution steps and theory lemmas only, not
/// input clauses — those are assumptions, not proof steps).
fn count_dead_branches(
    artifact: &AYProofArtifact,
    reachable: &HashSet<u64>,
    _all_ids: &HashSet<u64>,
) -> usize {
    // Collect unreachable step IDs (resolution + theory, not inputs).
    let unreachable_steps: HashSet<u64> = artifact
        .resolution_steps
        .iter()
        .map(|s| s.result_id)
        .chain(artifact.theory_lemmas.iter().map(|tl| tl.id))
        .filter(|id| !reachable.contains(id))
        .collect();

    if unreachable_steps.is_empty() {
        return 0;
    }

    // Build undirected adjacency among unreachable steps.
    let mut adj: HashMap<u64, HashSet<u64>> = HashMap::new();
    for &id in &unreachable_steps {
        adj.entry(id).or_default();
    }

    for step in &artifact.resolution_steps {
        if !unreachable_steps.contains(&step.result_id) {
            continue;
        }
        for &dep in &[step.antecedent_a, step.antecedent_b] {
            if unreachable_steps.contains(&dep) {
                adj.entry(step.result_id).or_default().insert(dep);
                adj.entry(dep).or_default().insert(step.result_id);
            }
        }
    }

    // Count connected components via BFS.
    let mut visited = HashSet::new();
    let mut count = 0;

    for &id in &unreachable_steps {
        if visited.contains(&id) {
            continue;
        }
        count += 1;
        let mut queue = VecDeque::new();
        queue.push_back(id);
        visited.insert(id);
        while let Some(node) = queue.pop_front() {
            if let Some(neighbors) = adj.get(&node) {
                for &n in neighbors {
                    if visited.insert(n) {
                        queue.push_back(n);
                    }
                }
            }
        }
    }

    count
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bridge::convert_ay_artifact;
    use crate::bridge::{AYClause, AYProofArtifact, AYResolutionStep, AYTheoryKind, AYTheoryLemma};
    use crate::checker::check_proof;
    use crate::types::CheckResult;

    /// Helper: create a AYClause.
    fn zc(id: u64, lits: &[i64]) -> AYClause {
        AYClause {
            id,
            literals: lits.to_vec(),
        }
    }

    /// Helper: create a AYResolutionStep.
    fn zr(result_id: u64, pivot: i64, a: u64, b: u64) -> AYResolutionStep {
        AYResolutionStep {
            result_id,
            pivot,
            antecedent_a: a,
            antecedent_b: b,
            result_literals: None,
        }
    }

    /// Helper: create a AYTheoryLemma.
    fn ztl(id: u64, kind: AYTheoryKind, lits: &[i64]) -> AYTheoryLemma {
        AYTheoryLemma {
            id,
            kind,
            literals: lits.to_vec(),
        }
    }

    /// Helper: verify the compacted artifact still produces a valid proof.
    fn assert_compacted_valid(artifact: &AYProofArtifact) {
        let compacted = compact_proof(artifact);
        let trace = convert_ay_artifact(&compacted);
        assert_eq!(
            check_proof(&trace),
            CheckResult::Valid,
            "compacted proof should remain valid"
        );
    }

    // -- Edge cases -----------------------------------------------------------

    #[test]
    fn test_compact_empty_proof_returns_as_is() {
        let artifact = AYProofArtifact {
            input_clauses: vec![zc(1, &[])],
            resolution_steps: vec![],
            theory_lemmas: vec![],
            empty_clause_id: 1,
        };
        let (compacted, stats) = compact_with_stats(&artifact);
        assert_eq!(compacted.input_clauses.len(), 1);
        assert_eq!(stats.removed_steps, 0);
        assert_eq!(stats.compression_ratio, 1.0);
    }

    #[test]
    fn test_compact_no_resolution_steps_only_assumptions() {
        let artifact = AYProofArtifact {
            input_clauses: vec![zc(1, &[1]), zc(2, &[-1]), zc(3, &[])],
            resolution_steps: vec![],
            theory_lemmas: vec![],
            empty_clause_id: 3,
        };
        let (compacted, stats) = compact_with_stats(&artifact);
        assert_eq!(compacted.input_clauses.len(), 3);
        assert_eq!(stats.original_assumptions, 3);
        assert_eq!(stats.removed_steps, 0);
    }

    #[test]
    fn test_compact_single_resolution_step() {
        let artifact = AYProofArtifact {
            input_clauses: vec![zc(1, &[1]), zc(2, &[-1])],
            resolution_steps: vec![zr(3, 1, 1, 2)],
            theory_lemmas: vec![],
            empty_clause_id: 3,
        };
        let (compacted, stats) = compact_with_stats(&artifact);
        assert_eq!(compacted.resolution_steps.len(), 1);
        assert_eq!(compacted.input_clauses.len(), 2);
        assert_eq!(stats.removed_steps, 0);
        assert_eq!(stats.dead_branch_count, 0);
        assert_compacted_valid(&artifact);
    }

    #[test]
    fn test_compact_fully_connected_no_compaction() {
        // All steps are on the critical path.
        let artifact = AYProofArtifact {
            input_clauses: vec![zc(1, &[1]), zc(2, &[-1, 2]), zc(3, &[-2])],
            resolution_steps: vec![zr(4, 1, 1, 2), zr(5, 2, 4, 3)],
            theory_lemmas: vec![],
            empty_clause_id: 5,
        };
        let (compacted, stats) = compact_with_stats(&artifact);
        assert_eq!(stats.removed_steps, 0);
        assert_eq!(stats.compacted_steps, 2);
        assert_eq!(stats.dead_branch_count, 0);
        assert_compacted_valid(&artifact);
        assert_eq!(compacted.resolution_steps.len(), 2);
    }

    // -- Dead branch removal --------------------------------------------------

    #[test]
    fn test_compact_removes_single_dead_step() {
        // Steps 3 (dead) and 4 (live). Only step 4 reaches empty clause.
        let artifact = AYProofArtifact {
            input_clauses: vec![zc(1, &[1]), zc(2, &[-1]), zc(5, &[2]), zc(6, &[-2])],
            resolution_steps: vec![
                zr(3, 2, 5, 6), // dead: resolves clauses 5,6 on pivot 2
                zr(4, 1, 1, 2), // live: resolves clauses 1,2 on pivot 1
            ],
            theory_lemmas: vec![],
            empty_clause_id: 4,
        };
        let (compacted, stats) = compact_with_stats(&artifact);
        assert_eq!(stats.original_steps, 2);
        assert_eq!(stats.compacted_steps, 1);
        assert_eq!(stats.removed_steps, 1);
        assert_eq!(stats.dead_branch_count, 1);
        assert_eq!(compacted.resolution_steps.len(), 1);
        // Dead input clauses 5 and 6 should also be removed.
        assert_eq!(compacted.input_clauses.len(), 2);
        assert_compacted_valid(&artifact);
    }

    #[test]
    fn test_compact_removes_dead_chain() {
        // Main proof: 1(1), 2(-1) -> 10(empty)
        // Dead chain: 3(2), 4(-2,3), 5(-3) -> 6 -> 7
        let artifact = AYProofArtifact {
            input_clauses: vec![
                zc(1, &[1]),
                zc(2, &[-1]),
                zc(3, &[2]),
                zc(4, &[-2, 3]),
                zc(5, &[-3]),
            ],
            resolution_steps: vec![
                zr(6, 2, 3, 4),  // dead: {3}
                zr(7, 3, 6, 5),  // dead: {}  (also derives empty, but not designated)
                zr(10, 1, 1, 2), // live
            ],
            theory_lemmas: vec![],
            empty_clause_id: 10,
        };
        let (compacted, stats) = compact_with_stats(&artifact);
        assert_eq!(stats.removed_steps, 2);
        assert_eq!(stats.dead_branch_count, 1); // Steps 6,7 form one connected component
        assert_eq!(compacted.resolution_steps.len(), 1);
        assert_compacted_valid(&artifact);
    }

    #[test]
    fn test_compact_removes_multiple_dead_branches() {
        // Main: 1(1), 2(-1) -> 100(empty)
        // Dead branch A: 3(2), 4(-2) -> 50
        // Dead branch B: 5(3), 6(-3) -> 60
        let artifact = AYProofArtifact {
            input_clauses: vec![
                zc(1, &[1]),
                zc(2, &[-1]),
                zc(3, &[2]),
                zc(4, &[-2]),
                zc(5, &[3]),
                zc(6, &[-3]),
            ],
            resolution_steps: vec![
                zr(50, 2, 3, 4),  // dead branch A
                zr(60, 3, 5, 6),  // dead branch B
                zr(100, 1, 1, 2), // live
            ],
            theory_lemmas: vec![],
            empty_clause_id: 100,
        };
        let (compacted, stats) = compact_with_stats(&artifact);
        assert_eq!(stats.removed_steps, 2);
        assert_eq!(stats.dead_branch_count, 2);
        assert_eq!(compacted.resolution_steps.len(), 1);
        assert_eq!(compacted.input_clauses.len(), 2);
        assert_compacted_valid(&artifact);
    }

    // -- Renumbering ----------------------------------------------------------

    #[test]
    fn test_compact_renumbers_densely() {
        // IDs: 10, 20, 30 (sparse) -> should become 1, 2, 3 (dense).
        let artifact = AYProofArtifact {
            input_clauses: vec![zc(10, &[1]), zc(20, &[-1])],
            resolution_steps: vec![zr(30, 1, 10, 20)],
            theory_lemmas: vec![],
            empty_clause_id: 30,
        };
        let (compacted, stats) = compact_with_stats(&artifact);
        assert_eq!(compacted.input_clauses[0].id, 1);
        assert_eq!(compacted.input_clauses[1].id, 2);
        assert_eq!(compacted.resolution_steps[0].result_id, 3);
        assert_eq!(compacted.resolution_steps[0].antecedent_a, 1);
        assert_eq!(compacted.resolution_steps[0].antecedent_b, 2);
        assert_eq!(compacted.empty_clause_id, 3);
        assert_eq!(stats.compression_ratio, 1.0); // No steps removed
        assert_compacted_valid(&artifact);
    }

    #[test]
    fn test_compact_renumbers_after_dead_removal() {
        // After removing dead step, remaining IDs should be dense.
        let artifact = AYProofArtifact {
            input_clauses: vec![zc(100, &[1]), zc(200, &[-1]), zc(300, &[5]), zc(400, &[-5])],
            resolution_steps: vec![
                zr(500, 5, 300, 400), // dead
                zr(600, 1, 100, 200), // live
            ],
            theory_lemmas: vec![],
            empty_clause_id: 600,
        };
        let (compacted, _stats) = compact_with_stats(&artifact);
        // Should have 2 input clauses (100, 200) + 1 step
        assert_eq!(compacted.input_clauses.len(), 2);
        assert_eq!(compacted.resolution_steps.len(), 1);
        // Dense IDs: inputs 1,2; step 3
        assert_eq!(compacted.input_clauses[0].id, 1);
        assert_eq!(compacted.input_clauses[1].id, 2);
        assert_eq!(compacted.resolution_steps[0].result_id, 3);
        assert_eq!(compacted.empty_clause_id, 3);
        assert_compacted_valid(&artifact);
    }

    // -- Theory lemma handling ------------------------------------------------

    #[test]
    fn test_compact_keeps_used_theory_lemma() {
        // Theory lemma 2 is used in the final derivation.
        let artifact = AYProofArtifact {
            input_clauses: vec![zc(1, &[1])],
            resolution_steps: vec![zr(3, 1, 1, 2)],
            theory_lemmas: vec![ztl(2, AYTheoryKind::Euf, &[-1])],
            empty_clause_id: 3,
        };
        let (compacted, stats) = compact_with_stats(&artifact);
        assert_eq!(compacted.theory_lemmas.len(), 1);
        assert_eq!(stats.compacted_steps, 2); // 1 resolution + 1 theory
        assert_compacted_valid(&artifact);
    }

    #[test]
    fn test_compact_removes_unused_theory_lemma() {
        // Theory lemma 10 is not used by any reachable step.
        let artifact = AYProofArtifact {
            input_clauses: vec![zc(1, &[1]), zc(2, &[-1])],
            resolution_steps: vec![zr(3, 1, 1, 2)],
            theory_lemmas: vec![ztl(10, AYTheoryKind::Lra, &[5, -6])],
            empty_clause_id: 3,
        };
        let (compacted, stats) = compact_with_stats(&artifact);
        assert_eq!(compacted.theory_lemmas.len(), 0);
        assert_eq!(stats.removed_steps, 1);
        assert_eq!(stats.original_steps, 2); // 1 resolution + 1 theory
        assert_eq!(stats.compacted_steps, 1);
        assert_compacted_valid(&artifact);
    }

    #[test]
    fn test_compact_theory_lemma_in_chain() {
        // Input(1: [1]), Theory(2: [-1, 2]), Input(3: [-2])
        // Step 4: resolve 1 and 2 on pivot 1 -> {2}
        // Step 5: resolve 4 and 3 on pivot 2 -> {}
        let artifact = AYProofArtifact {
            input_clauses: vec![zc(1, &[1]), zc(3, &[-2])],
            resolution_steps: vec![zr(4, 1, 1, 2), zr(5, 2, 4, 3)],
            theory_lemmas: vec![ztl(2, AYTheoryKind::Euf, &[-1, 2])],
            empty_clause_id: 5,
        };
        let (compacted, stats) = compact_with_stats(&artifact);
        assert_eq!(compacted.theory_lemmas.len(), 1);
        assert_eq!(compacted.resolution_steps.len(), 2);
        assert_eq!(stats.removed_steps, 0);
        assert_compacted_valid(&artifact);
    }

    // -- find_dead_branches ---------------------------------------------------

    #[test]
    fn test_find_dead_branches_none() {
        let artifact = AYProofArtifact {
            input_clauses: vec![zc(1, &[1]), zc(2, &[-1])],
            resolution_steps: vec![zr(3, 1, 1, 2)],
            theory_lemmas: vec![],
            empty_clause_id: 3,
        };
        let branches = find_dead_branches(&artifact);
        assert!(branches.is_empty());
    }

    #[test]
    fn test_find_dead_branches_single() {
        let artifact = AYProofArtifact {
            input_clauses: vec![zc(1, &[1]), zc(2, &[-1]), zc(3, &[2]), zc(4, &[-2])],
            resolution_steps: vec![
                zr(5, 2, 3, 4), // dead
                zr(6, 1, 1, 2), // live
            ],
            theory_lemmas: vec![],
            empty_clause_id: 6,
        };
        let branches = find_dead_branches(&artifact);
        // Dead branch includes step 5 and its unreachable inputs 3, 4.
        assert_eq!(branches.len(), 1);
        // The dead branch component should include at least step 5.
        let all_dead: Vec<u64> = branches.into_iter().flatten().collect();
        assert!(all_dead.contains(&5));
    }

    #[test]
    fn test_find_dead_branches_multiple_disconnected() {
        let artifact = AYProofArtifact {
            input_clauses: vec![
                zc(1, &[1]),
                zc(2, &[-1]),
                zc(10, &[2]),
                zc(11, &[-2]),
                zc(20, &[3]),
                zc(21, &[-3]),
            ],
            resolution_steps: vec![
                zr(12, 2, 10, 11), // dead branch A
                zr(22, 3, 20, 21), // dead branch B
                zr(30, 1, 1, 2),   // live
            ],
            theory_lemmas: vec![],
            empty_clause_id: 30,
        };
        let branches = find_dead_branches(&artifact);
        // At least 2 disconnected dead components.
        assert!(branches.len() >= 2);
    }

    // -- Compression ratio ----------------------------------------------------

    #[test]
    fn test_compact_compression_ratio_full_removal() {
        // 3 dead steps, 1 live step -> ratio = 1/4 = 0.25
        let artifact = AYProofArtifact {
            input_clauses: vec![
                zc(1, &[1]),
                zc(2, &[-1]),
                zc(10, &[2]),
                zc(11, &[-2]),
                zc(20, &[3]),
                zc(21, &[-3]),
                zc(30, &[4]),
                zc(31, &[-4]),
            ],
            resolution_steps: vec![
                zr(12, 2, 10, 11), // dead
                zr(22, 3, 20, 21), // dead
                zr(32, 4, 30, 31), // dead
                zr(40, 1, 1, 2),   // live
            ],
            theory_lemmas: vec![],
            empty_clause_id: 40,
        };
        let (_compacted, stats) = compact_with_stats(&artifact);
        assert_eq!(stats.original_steps, 4);
        assert_eq!(stats.compacted_steps, 1);
        assert!((stats.compression_ratio - 0.25).abs() < f64::EPSILON);
        assert_compacted_valid(&artifact);
    }

    #[test]
    fn test_compact_compression_ratio_no_removal() {
        let artifact = AYProofArtifact {
            input_clauses: vec![zc(1, &[1]), zc(2, &[-1])],
            resolution_steps: vec![zr(3, 1, 1, 2)],
            theory_lemmas: vec![],
            empty_clause_id: 3,
        };
        let (_compacted, stats) = compact_with_stats(&artifact);
        assert!((stats.compression_ratio - 1.0).abs() < f64::EPSILON);
    }

    // -- Used assumptions tracking --------------------------------------------

    #[test]
    fn test_compact_tracks_used_assumptions() {
        let artifact = AYProofArtifact {
            input_clauses: vec![
                zc(1, &[1]),
                zc(2, &[-1]),
                zc(3, &[99]), // unused input
            ],
            resolution_steps: vec![zr(4, 1, 1, 2)],
            theory_lemmas: vec![],
            empty_clause_id: 4,
        };
        let (_compacted, stats) = compact_with_stats(&artifact);
        assert_eq!(stats.original_assumptions, 3);
        assert_eq!(stats.used_assumptions, 2);
    }

    // -- Large proof compaction -----------------------------------------------

    #[test]
    fn test_compact_large_proof_with_dead_branches() {
        // Build a valid chain: c1(1), c2(-1,2), c3(-2,3), ..., cn(-n)
        // Plus dead branches at each step.
        let n: i64 = 20;
        let mut inputs = vec![zc(1, &[1])];
        for i in 1..n {
            inputs.push(zc((i + 1) as u64, &[-i, i + 1]));
        }
        inputs.push(zc((n + 1) as u64, &[-n]));

        // Main chain resolution steps.
        let base = 1000u64;
        let mut steps = vec![zr(base, 1, 1, 2)];
        for i in 2..n {
            steps.push(zr(
                base + (i - 1) as u64,
                i,
                base + (i - 2) as u64,
                (i + 1) as u64,
            ));
        }
        let final_step = base + (n - 1) as u64;
        steps.push(zr(final_step, n, final_step - 1, (n + 1) as u64));

        // Add 10 dead branches.
        let dead_base = 5000u64;
        for i in 0..10u64 {
            let a = dead_base + i * 3;
            let b = a + 1;
            let c = a + 2;
            inputs.push(zc(a, &[(100 + i as i64)]));
            inputs.push(zc(b, &[-(100 + i as i64)]));
            steps.push(zr(c, 100 + i as i64, a, b));
        }

        let artifact = AYProofArtifact {
            input_clauses: inputs,
            resolution_steps: steps,
            theory_lemmas: vec![],
            empty_clause_id: final_step,
        };

        let (compacted, stats) = compact_with_stats(&artifact);
        assert_eq!(stats.removed_steps, 10);
        assert_eq!(stats.dead_branch_count, 10);
        // All dead input clauses removed too.
        assert_eq!(compacted.input_clauses.len(), (n + 1) as usize);
        assert_compacted_valid(&artifact);
    }

    // -- Idempotence ----------------------------------------------------------

    #[test]
    fn test_compact_idempotent() {
        let artifact = AYProofArtifact {
            input_clauses: vec![zc(1, &[1]), zc(2, &[-1]), zc(3, &[5]), zc(4, &[-5])],
            resolution_steps: vec![
                zr(5, 5, 3, 4), // dead
                zr(6, 1, 1, 2), // live
            ],
            theory_lemmas: vec![],
            empty_clause_id: 6,
        };
        let first = compact_proof(&artifact);
        let second = compact_proof(&first);
        assert_eq!(first, second, "compaction should be idempotent");
    }

    // -- Proof validity preservation ------------------------------------------

    #[test]
    fn test_compact_preserves_validity_three_step_chain() {
        let artifact = AYProofArtifact {
            input_clauses: vec![zc(1, &[1]), zc(2, &[-1, 2]), zc(3, &[-2])],
            resolution_steps: vec![zr(4, 1, 1, 2), zr(5, 2, 4, 3)],
            theory_lemmas: vec![],
            empty_clause_id: 5,
        };
        assert_compacted_valid(&artifact);
    }

    #[test]
    fn test_compact_preserves_validity_with_theory_lemma() {
        let artifact = AYProofArtifact {
            input_clauses: vec![zc(1, &[1])],
            resolution_steps: vec![zr(3, 1, 1, 2)],
            theory_lemmas: vec![ztl(2, AYTheoryKind::Euf, &[-1])],
            empty_clause_id: 3,
        };
        assert_compacted_valid(&artifact);
    }

    // -- Diamond dependency ---------------------------------------------------

    #[test]
    fn test_compact_diamond_dependency_preserved() {
        // Clause 1 is used by both step 3 and step 4.
        // Step 5 depends on both 3 and 4.
        // Input: 1(a), 2(-a,b), 3(-a,-b), 4(-b,c), with appropriate structure.
        //
        // Actually build: step3 = resolve(1, 2) on a; step4 = resolve(1, 3) on a
        // step5 = resolve(step3, step4) on b
        // 1: {a, b}, 2: {-a}, 3: {-a, -b}
        // step3 = resolve(1, 2, pivot=a) -> {b}
        // step4 = resolve(1, 3, pivot=a) -> {b, -b} -> hmm that's not right
        //
        // Let's do: 1:{a}, 2:{-a,b}, 3:{-b}
        // step4 = resolve(1,2, pivot=a) -> {b}
        // step5 = resolve(4,3, pivot=b) -> {}
        // Both steps are needed. No diamond here. Let's just do shared input:
        // 1:{a}, 2:{-a,b}, 3:{-a,-b}
        // step4 = resolve(1,2,a) -> {b}
        // step5 = resolve(1,3,a) -> {-b}
        // step6 = resolve(4,5,b) -> {}
        let artifact = AYProofArtifact {
            input_clauses: vec![
                zc(1, &[1]),      // {a}
                zc(2, &[-1, 2]),  // {-a, b}
                zc(3, &[-1, -2]), // {-a, -b}
            ],
            resolution_steps: vec![
                zr(4, 1, 1, 2), // resolve on a -> {b}
                zr(5, 1, 1, 3), // resolve on a -> {-b}
                zr(6, 2, 4, 5), // resolve on b -> {}
            ],
            theory_lemmas: vec![],
            empty_clause_id: 6,
        };
        let (compacted, stats) = compact_with_stats(&artifact);
        assert_eq!(stats.removed_steps, 0);
        assert_eq!(compacted.resolution_steps.len(), 3);
        assert_eq!(compacted.input_clauses.len(), 3);
        assert_compacted_valid(&artifact);
    }

    // -- Mixed theory kinds ---------------------------------------------------

    #[test]
    fn test_compact_mixed_theory_kinds() {
        let artifact = AYProofArtifact {
            input_clauses: vec![zc(1, &[1])],
            resolution_steps: vec![
                zr(4, 1, 1, 2), // uses EUF lemma
                zr(5, 2, 4, 3), // uses LRA lemma -> empty
                zr(7, 3, 6, 1), // dead: uses unused theory lemma
            ],
            theory_lemmas: vec![
                ztl(2, AYTheoryKind::Euf, &[-1, 2]), // used
                ztl(3, AYTheoryKind::Lra, &[-2]),    // used
                ztl(6, AYTheoryKind::Nia, &[-3, 4]), // unused
            ],
            empty_clause_id: 5,
        };
        let (compacted, stats) = compact_with_stats(&artifact);
        assert_eq!(compacted.theory_lemmas.len(), 2);
        assert_eq!(stats.removed_steps, 2); // 1 dead resolution + 1 unused theory lemma
        assert_compacted_valid(&artifact);
    }

    // -- Empty clause is an input ---------------------------------------------

    #[test]
    fn test_compact_empty_clause_is_input() {
        // The empty clause is directly an input clause — no resolution needed.
        let artifact = AYProofArtifact {
            input_clauses: vec![
                zc(1, &[]),   // empty clause as input
                zc(2, &[1]),  // unused
                zc(3, &[-1]), // unused
            ],
            resolution_steps: vec![
                zr(4, 1, 2, 3), // dead: resolves unused clauses
            ],
            theory_lemmas: vec![],
            empty_clause_id: 1,
        };
        let (compacted, stats) = compact_with_stats(&artifact);
        // Empty clause is the only needed input.
        // No resolution steps needed since empty_clause_id is an input.
        assert_eq!(compacted.input_clauses.len(), 1);
        assert_eq!(stats.removed_steps, 1);
    }

    // -- Empty clause is a theory lemma ---------------------------------------

    #[test]
    fn test_compact_empty_clause_is_theory_lemma() {
        let artifact = AYProofArtifact {
            input_clauses: vec![zc(1, &[1]), zc(2, &[-1])],
            resolution_steps: vec![
                zr(4, 1, 1, 2), // dead: not the empty clause
            ],
            theory_lemmas: vec![
                ztl(3, AYTheoryKind::Euf, &[]), // empty theory lemma
            ],
            empty_clause_id: 3,
        };
        let (compacted, stats) = compact_with_stats(&artifact);
        assert_eq!(compacted.theory_lemmas.len(), 1);
        assert_eq!(compacted.input_clauses.len(), 0);
        assert_eq!(compacted.resolution_steps.len(), 0);
        assert_eq!(stats.removed_steps, 1); // dead resolution step removed
    }

    // -- Stress: deeply nested chain ------------------------------------------

    #[test]
    fn test_compact_deep_chain_100_steps() {
        let n: i64 = 100;
        let mut inputs = vec![zc(1, &[1])];
        for i in 1..n {
            inputs.push(zc((i + 1) as u64, &[-i, i + 1]));
        }
        inputs.push(zc((n + 1) as u64, &[-n]));

        let base = 500u64;
        let mut steps = vec![zr(base, 1, 1, 2)];
        for i in 2..n {
            steps.push(zr(
                base + (i - 1) as u64,
                i,
                base + (i - 2) as u64,
                (i + 1) as u64,
            ));
        }
        let final_id = base + (n - 1) as u64;
        steps.push(zr(final_id, n, final_id - 1, (n + 1) as u64));

        let artifact = AYProofArtifact {
            input_clauses: inputs,
            resolution_steps: steps,
            theory_lemmas: vec![],
            empty_clause_id: final_id,
        };

        let (compacted, stats) = compact_with_stats(&artifact);
        assert_eq!(stats.removed_steps, 0);
        assert_eq!(compacted.resolution_steps.len(), n as usize);
        assert_compacted_valid(&artifact);
    }

    // -- Shared antecedent across live and dead branches ----------------------

    #[test]
    fn test_compact_shared_antecedent_live_and_dead() {
        // Input clause 1 is used by both a live path and a dead path.
        // It should be retained because the live path needs it.
        let artifact = AYProofArtifact {
            input_clauses: vec![
                zc(1, &[1, 2]), // shared
                zc(2, &[-1]),   // live path
                zc(3, &[-2]),   // dead path
            ],
            resolution_steps: vec![
                zr(4, 1, 1, 2), // live: resolves on pivot 1 -> {2}
                zr(5, 2, 1, 3), // dead: resolves on pivot 2 -> {1}
            ],
            theory_lemmas: vec![],
            empty_clause_id: 4,
        };
        let (compacted, stats) = compact_with_stats(&artifact);
        // Input clause 1 and 2 should be kept.
        assert_eq!(compacted.input_clauses.len(), 2);
        assert_eq!(compacted.resolution_steps.len(), 1);
        assert_eq!(stats.removed_steps, 1);
    }

    // -- Fully dead proof (all resolution steps unreachable) ------------------

    #[test]
    fn test_compact_fully_dead_proof_empty_clause_is_input() {
        // The empty clause is a direct input. All resolution steps form dead
        // branches and should be completely removed.
        let artifact = AYProofArtifact {
            input_clauses: vec![
                zc(1, &[]),    // empty clause as input (the UNSAT witness)
                zc(10, &[2]),  // dead input A
                zc(11, &[-2]), // dead input A
                zc(20, &[3]),  // dead input B
                zc(21, &[-3]), // dead input B
                zc(30, &[4]),  // dead input C
                zc(31, &[-4]), // dead input C
            ],
            resolution_steps: vec![
                zr(50, 2, 10, 11), // dead branch A
                zr(60, 3, 20, 21), // dead branch B
                zr(70, 4, 30, 31), // dead branch C
            ],
            theory_lemmas: vec![],
            empty_clause_id: 1,
        };
        let (compacted, stats) = compact_with_stats(&artifact);
        // Only the empty input clause survives.
        assert_eq!(compacted.input_clauses.len(), 1);
        assert!(compacted.input_clauses[0].literals.is_empty());
        assert_eq!(compacted.resolution_steps.len(), 0);
        assert_eq!(stats.original_steps, 3);
        assert_eq!(stats.removed_steps, 3);
        assert_eq!(stats.dead_branch_count, 3);
        assert_eq!(stats.used_assumptions, 1);
        assert_eq!(stats.original_assumptions, 7);
    }

    // -- Result literals preservation through compaction ----------------------

    #[test]
    fn test_compact_preserves_result_literals() {
        // Resolution steps carry optional result_literals. Compaction must
        // preserve them through renumbering, not drop them.
        let step = AYResolutionStep {
            result_id: 100,
            pivot: 1,
            antecedent_a: 10,
            antecedent_b: 20,
            result_literals: Some(vec![2, -3]),
        };
        let artifact = AYProofArtifact {
            input_clauses: vec![zc(10, &[1, 2]), zc(20, &[-1, -3])],
            resolution_steps: vec![step],
            theory_lemmas: vec![],
            empty_clause_id: 100,
        };
        let (compacted, stats) = compact_with_stats(&artifact);
        assert_eq!(stats.removed_steps, 0);
        assert_eq!(compacted.resolution_steps.len(), 1);
        let kept = &compacted.resolution_steps[0];
        // result_literals must survive, not be set to None.
        assert_eq!(kept.result_literals, Some(vec![2, -3]));
        // IDs are renumbered (10->1, 20->2, 100->3).
        assert_eq!(kept.result_id, 3);
        assert_eq!(kept.antecedent_a, 1);
        assert_eq!(kept.antecedent_b, 2);
    }

    // -- Theory lemma kind preservation after compaction ----------------------

    #[test]
    fn test_compact_preserves_theory_lemma_kind() {
        // Each theory lemma has a `kind` field (Euf, Lra, etc.).
        // Compaction must preserve the kind, not just the literals.
        let artifact = AYProofArtifact {
            input_clauses: vec![zc(1, &[1])],
            resolution_steps: vec![
                zr(10, 1, 1, 2),  // resolve input 1 with EUF lemma 2 -> {2}
                zr(11, 2, 10, 3), // resolve intermediate with LRA lemma 3 -> {}
            ],
            theory_lemmas: vec![
                ztl(2, AYTheoryKind::Euf, &[-1, 2]),
                ztl(3, AYTheoryKind::Lra, &[-2]),
            ],
            empty_clause_id: 11,
        };
        let (compacted, stats) = compact_with_stats(&artifact);
        assert_eq!(stats.removed_steps, 0);
        assert_eq!(compacted.theory_lemmas.len(), 2);
        // Verify kinds are preserved through renumbering.
        let euf_lemma = compacted
            .theory_lemmas
            .iter()
            .find(|tl| tl.kind == AYTheoryKind::Euf)
            .expect("EUF lemma should survive compaction");
        assert_eq!(euf_lemma.literals, vec![-1, 2]);
        let lra_lemma = compacted
            .theory_lemmas
            .iter()
            .find(|tl| tl.kind == AYTheoryKind::Lra)
            .expect("LRA lemma should survive compaction");
        assert_eq!(lra_lemma.literals, vec![-2]);
        assert_compacted_valid(&artifact);
    }

    // -- Stats invariant: original = compacted + removed ----------------------

    #[test]
    fn test_compact_stats_invariant_holds() {
        // Construct a proof with a mix of live and dead steps and theory
        // lemmas, then verify the accounting invariant.
        let artifact = AYProofArtifact {
            input_clauses: vec![zc(1, &[1]), zc(2, &[-1]), zc(3, &[5]), zc(4, &[-5])],
            resolution_steps: vec![
                zr(10, 5, 3, 4), // dead
                zr(20, 1, 1, 2), // live
            ],
            theory_lemmas: vec![
                ztl(30, AYTheoryKind::Array, &[7, -8]), // dead (unreachable)
                ztl(40, AYTheoryKind::Nia, &[9]),       // dead (unreachable)
            ],
            empty_clause_id: 20,
        };
        let (_compacted, stats) = compact_with_stats(&artifact);
        // Invariant: original_steps == compacted_steps + removed_steps
        assert_eq!(
            stats.original_steps,
            stats.compacted_steps + stats.removed_steps,
            "stats accounting invariant violated"
        );
        // Verify the actual values.
        assert_eq!(stats.original_steps, 4); // 2 resolution + 2 theory
        assert_eq!(stats.compacted_steps, 1); // 1 live resolution
        assert_eq!(stats.removed_steps, 3); // 1 dead resolution + 2 dead theory
                                            // Compression ratio should match.
        let expected_ratio = 1.0 / 4.0;
        assert!(
            (stats.compression_ratio - expected_ratio).abs() < f64::EPSILON,
            "compression ratio mismatch: got {}, expected {}",
            stats.compression_ratio,
            expected_ratio,
        );
    }

    // -- Complex chain renumbering preserves cross-references -----------------

    #[test]
    fn test_compact_chain_renumbering_cross_references() {
        // Build a 4-step live chain with sparse IDs (gaps between each).
        // After compaction + renumbering, every antecedent reference must
        // still point to the correct (renumbered) clause.
        //
        // Inputs: 100:{a}, 200:{-a,b}, 300:{-b,c}, 400:{-c}
        // Step 500: resolve(100, 200, pivot=a) -> {b}
        // Step 600: resolve(500, 300, pivot=b) -> {c}
        // Step 700: resolve(600, 400, pivot=c) -> {} (empty clause)
        let artifact = AYProofArtifact {
            input_clauses: vec![
                zc(100, &[1]),
                zc(200, &[-1, 2]),
                zc(300, &[-2, 3]),
                zc(400, &[-3]),
            ],
            resolution_steps: vec![
                zr(500, 1, 100, 200),
                zr(600, 2, 500, 300),
                zr(700, 3, 600, 400),
            ],
            theory_lemmas: vec![],
            empty_clause_id: 700,
        };
        let (compacted, stats) = compact_with_stats(&artifact);
        assert_eq!(stats.removed_steps, 0);
        // After renumbering: inputs -> 1,2,3,4; steps -> 5,6,7
        assert_eq!(compacted.input_clauses.len(), 4);
        assert_eq!(compacted.resolution_steps.len(), 3);

        let s0 = &compacted.resolution_steps[0]; // was 500
        let s1 = &compacted.resolution_steps[1]; // was 600
        let s2 = &compacted.resolution_steps[2]; // was 700

        // Step 0: resolve(input 1, input 2) -> result 5
        assert_eq!(s0.result_id, 5);
        assert_eq!(s0.antecedent_a, 1); // was 100
        assert_eq!(s0.antecedent_b, 2); // was 200

        // Step 1: resolve(step 5, input 3) -> result 6
        assert_eq!(s1.result_id, 6);
        assert_eq!(s1.antecedent_a, 5); // was 500
        assert_eq!(s1.antecedent_b, 3); // was 300

        // Step 2: resolve(step 6, input 4) -> result 7
        assert_eq!(s2.result_id, 7);
        assert_eq!(s2.antecedent_a, 6); // was 600
        assert_eq!(s2.antecedent_b, 4); // was 400

        assert_eq!(compacted.empty_clause_id, 7);
        assert_compacted_valid(&artifact);
    }

    // -- Mixed reachable/unreachable theory lemmas of same kind ---------------

    #[test]
    fn test_compact_mixed_reachability_same_theory_kind() {
        // Two EUF theory lemmas: one reachable, one dead. Only the reachable
        // one should survive compaction.
        let artifact = AYProofArtifact {
            input_clauses: vec![zc(1, &[1])],
            resolution_steps: vec![
                zr(10, 1, 1, 2),   // live: uses EUF lemma 2
                zr(20, 5, 3, 100), // dead: uses EUF lemma 3 and dead input 100
            ],
            theory_lemmas: vec![
                ztl(2, AYTheoryKind::Euf, &[-1]),    // reachable
                ztl(3, AYTheoryKind::Euf, &[-5, 6]), // unreachable
            ],
            empty_clause_id: 10,
        };
        let (compacted, stats) = compact_with_stats(&artifact);
        assert_eq!(compacted.theory_lemmas.len(), 1);
        assert_eq!(compacted.theory_lemmas[0].kind, AYTheoryKind::Euf);
        assert_eq!(compacted.theory_lemmas[0].literals, vec![-1]);
        assert_eq!(stats.removed_steps, 2); // 1 dead resolution + 1 dead theory
        assert_compacted_valid(&artifact);
    }

    // -- Compaction of proof where all steps are reachable (no-op) -----------

    #[test]
    fn test_compact_fully_reachable_multi_step_chain() {
        // Every step and input is on the path to the empty clause.
        // Compaction should be a no-op (except renumbering, which is still
        // identity when IDs are already dense starting at 1).
        let artifact = AYProofArtifact {
            input_clauses: vec![
                zc(1, &[1]),     // {a}
                zc(2, &[-1, 2]), // {-a, b}
                zc(3, &[-2, 3]), // {-b, c}
                zc(4, &[-3]),    // {-c}
            ],
            resolution_steps: vec![
                zr(5, 1, 1, 2), // {b}
                zr(6, 2, 5, 3), // {c}
                zr(7, 3, 6, 4), // {} (empty)
            ],
            theory_lemmas: vec![],
            empty_clause_id: 7,
        };
        let (compacted, stats) = compact_with_stats(&artifact);
        assert_eq!(stats.removed_steps, 0);
        assert_eq!(stats.dead_branch_count, 0);
        assert_eq!(stats.compacted_steps, stats.original_steps);
        assert!((stats.compression_ratio - 1.0).abs() < f64::EPSILON);
        assert_eq!(stats.used_assumptions, stats.original_assumptions);
        // Since IDs are already dense 1..7, renumbering is identity.
        assert_eq!(compacted.input_clauses, artifact.input_clauses);
        assert_eq!(compacted.resolution_steps, artifact.resolution_steps);
        assert_eq!(compacted.empty_clause_id, 7);
        assert_compacted_valid(&artifact);
    }
}
