// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Proof differencing for incremental proof checking and evolution tracking.
//!
//! Compares two proof certificates to identify structural differences, enabling:
//!
//! 1. **Incremental proof checking** — only re-check parts that changed.
//! 2. **Proof evolution tracking** — track how a proof changes over time.
//! 3. **Shared subproof identification** — find common proof fragments.
//!
//! This module is self-contained: all types are defined locally and only `std`
//! is used.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};

// ---------------------------------------------------------------------------
// Node identifiers and basic types
// ---------------------------------------------------------------------------

/// Unique identifier for a node within a proof tree.
pub type NodeId = u64;

/// Literal identifier (positive = original, negative = negation).
pub type LiteralId = i64;

// ---------------------------------------------------------------------------
// ProofFingerprint
// ---------------------------------------------------------------------------

/// Compact hash-based representation of a proof subtree.
///
/// Fingerprints are computed bottom-up: leaf nodes hash their content, and
/// internal nodes hash the combination of their children's fingerprints plus
/// the local operation (pivot, theory kind, etc.). Two subtrees with the same
/// fingerprint are structurally identical.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ProofFingerprint {
    /// The 64-bit hash summarising the subtree rooted at this node.
    hash: u64,
}

impl ProofFingerprint {
    /// Compute the fingerprint of the subtree rooted at `node_id` within
    /// `tree`. Returns `None` if `node_id` is not present in the tree.
    #[must_use]
    pub fn compute(tree: &ProofTree, node_id: NodeId) -> Option<Self> {
        Self::compute_inner(tree, node_id, &mut HashMap::new())
    }

    fn compute_inner(
        tree: &ProofTree,
        node_id: NodeId,
        cache: &mut HashMap<NodeId, u64>,
    ) -> Option<Self> {
        if let Some(&h) = cache.get(&node_id) {
            return Some(ProofFingerprint { hash: h });
        }

        let node = tree.nodes.get(&node_id)?;

        let mut hasher = FnvHasher::new();
        // Hash the node kind discriminant.
        std::mem::discriminant(&node.kind).hash(&mut hasher);

        match &node.kind {
            ProofNodeKind::InputClause { literals } => {
                let mut sorted = literals.clone();
                sorted.sort();
                for lit in &sorted {
                    lit.hash(&mut hasher);
                }
            }
            ProofNodeKind::Resolution { pivot } => {
                pivot.hash(&mut hasher);
                // Hash children fingerprints in order.
                if let Some(children) = tree.edges.get(&node_id) {
                    for &child_id in children {
                        let child_fp = Self::compute_inner(tree, child_id, cache)?;
                        child_fp.hash.hash(&mut hasher);
                    }
                }
            }
            ProofNodeKind::TheoryLemma { theory, literals } => {
                theory.hash(&mut hasher);
                let mut sorted = literals.clone();
                sorted.sort();
                for lit in &sorted {
                    lit.hash(&mut hasher);
                }
            }
        }

        let h = hasher.finish();
        cache.insert(node_id, h);
        Some(ProofFingerprint { hash: h })
    }

    /// Return the raw 64-bit hash value.
    #[must_use]
    pub const fn value(&self) -> u64 {
        self.hash
    }
}

impl fmt::Display for ProofFingerprint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:016x}", self.hash)
    }
}

// ---------------------------------------------------------------------------
// FNV-1a hasher (self-contained, no external deps)
// ---------------------------------------------------------------------------

struct FnvHasher(u64);

impl FnvHasher {
    fn new() -> Self {
        Self(0xcbf29ce484222325)
    }
}

impl Hasher for FnvHasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 ^= u64::from(b);
            self.0 = self.0.wrapping_mul(0x100000001b3);
        }
    }
}

// ---------------------------------------------------------------------------
// ProofNode
// ---------------------------------------------------------------------------

/// The kind of operation a proof node represents.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProofNodeKind {
    /// An input clause (axiom or assertion).
    InputClause { literals: Vec<LiteralId> },
    /// A resolution step combining two parent clauses on a pivot.
    Resolution { pivot: LiteralId },
    /// A theory lemma introduced by a decision procedure.
    TheoryLemma {
        theory: String,
        literals: Vec<LiteralId>,
    },
}

/// A node in a proof tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofNode {
    pub id: NodeId,
    pub kind: ProofNodeKind,
}

// ---------------------------------------------------------------------------
// ProofTree
// ---------------------------------------------------------------------------

/// A tree (or DAG) structure representing a resolution proof.
///
/// Nodes are stored in a map keyed by [`NodeId`]. Edges map each node to its
/// children (the clauses it was derived from).
#[derive(Debug, Clone)]
pub struct ProofTree {
    pub nodes: BTreeMap<NodeId, ProofNode>,
    pub edges: BTreeMap<NodeId, Vec<NodeId>>,
    /// The root node (typically the empty clause).
    pub root: Option<NodeId>,
}

impl ProofTree {
    /// Create an empty proof tree.
    #[must_use]
    pub fn new() -> Self {
        Self {
            nodes: BTreeMap::new(),
            edges: BTreeMap::new(),
            root: None,
        }
    }

    /// Build a proof tree from input clauses and resolution steps.
    ///
    /// Each input clause is `(id, literals)`. Each resolution step is
    /// `(result_id, parent1, parent2, pivot)`. The last resolution step's
    /// result becomes the root.
    #[must_use]
    pub fn from_steps(
        input_clauses: &[(NodeId, &[LiteralId])],
        resolution_steps: &[(NodeId, NodeId, NodeId, LiteralId)],
    ) -> Self {
        let mut tree = Self::new();

        for &(id, lits) in input_clauses {
            tree.nodes.insert(
                id,
                ProofNode {
                    id,
                    kind: ProofNodeKind::InputClause {
                        literals: lits.to_vec(),
                    },
                },
            );
        }

        for &(result_id, parent1, parent2, pivot) in resolution_steps {
            tree.nodes.insert(
                result_id,
                ProofNode {
                    id: result_id,
                    kind: ProofNodeKind::Resolution { pivot },
                },
            );
            tree.edges.insert(result_id, vec![parent1, parent2]);
        }

        if let Some(&(last_id, _, _, _)) = resolution_steps.last() {
            tree.root = Some(last_id);
        } else if let Some(&(first_id, _)) = input_clauses.first() {
            tree.root = Some(first_id);
        }

        tree
    }

    /// Add a theory lemma node.
    pub fn add_theory_lemma(&mut self, id: NodeId, theory: &str, literals: &[LiteralId]) {
        self.nodes.insert(
            id,
            ProofNode {
                id,
                kind: ProofNodeKind::TheoryLemma {
                    theory: theory.to_string(),
                    literals: literals.to_vec(),
                },
            },
        );
    }

    /// Extract the subtree rooted at `node_id`.
    ///
    /// Returns a new `ProofTree` containing only the nodes reachable from
    /// `node_id`. Returns an empty tree if `node_id` is absent.
    #[must_use]
    pub fn subtree(&self, node_id: NodeId) -> ProofTree {
        let mut sub = ProofTree::new();
        self.collect_subtree(node_id, &mut sub);
        sub.root = Some(node_id);
        sub
    }

    fn collect_subtree(&self, node_id: NodeId, sub: &mut ProofTree) {
        if sub.nodes.contains_key(&node_id) {
            return;
        }
        if let Some(node) = self.nodes.get(&node_id) {
            sub.nodes.insert(node_id, node.clone());
            if let Some(children) = self.edges.get(&node_id) {
                sub.edges.insert(node_id, children.clone());
                for &child_id in children {
                    self.collect_subtree(child_id, sub);
                }
            }
        }
    }

    /// Number of nodes in the tree.
    #[must_use]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Whether the tree has no nodes.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Iterate over all node IDs.
    pub fn node_ids(&self) -> impl Iterator<Item = NodeId> + '_ {
        self.nodes.keys().copied()
    }
}

impl Default for ProofTree {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// DiffKind / DiffEntry / DiffResult
// ---------------------------------------------------------------------------

/// The kind of difference found between two proof nodes.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum DiffKind {
    /// A node exists in the new proof but not the old.
    NodeAdded,
    /// A node exists in the old proof but not the new.
    NodeRemoved,
    /// The pivot variable changed between corresponding resolution steps.
    PivotChanged {
        old_pivot: LiteralId,
        new_pivot: LiteralId,
    },
    /// An input clause's literal set changed.
    InputClauseChanged {
        old_literals: Vec<LiteralId>,
        new_literals: Vec<LiteralId>,
    },
    /// The overall proof structure changed (different children, different
    /// node kind, etc.).
    StructureChanged,
}

impl fmt::Display for DiffKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NodeAdded => write!(f, "node added"),
            Self::NodeRemoved => write!(f, "node removed"),
            Self::PivotChanged {
                old_pivot,
                new_pivot,
            } => write!(f, "pivot changed: {old_pivot} -> {new_pivot}"),
            Self::InputClauseChanged { .. } => write!(f, "input clause changed"),
            Self::StructureChanged => write!(f, "structure changed"),
        }
    }
}

/// An individual difference between two proofs.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum DiffEntry {
    /// A node that was added in the new proof.
    Added { node_id: NodeId },
    /// A node that was removed from the old proof.
    Removed { node_id: NodeId },
    /// A node that changed between old and new.
    Modified {
        old_node_id: NodeId,
        new_node_id: NodeId,
        kind: DiffKind,
    },
    /// A node that is identical in both proofs.
    Unchanged {
        old_node_id: NodeId,
        new_node_id: NodeId,
    },
}

/// The result of comparing two proof trees.
#[derive(Debug, Clone)]
pub struct DiffResult {
    pub entries: Vec<DiffEntry>,
    /// Fingerprint-based mapping: old node -> new node for matched nodes.
    /// Populated during diff for potential future queries; suppress warning
    /// until a consumer is added.
    #[allow(dead_code)]
    pub(crate) matched_nodes: HashMap<NodeId, NodeId>,
}

impl DiffResult {
    /// Compute high-level statistics from the diff.
    #[must_use]
    pub fn summary(&self) -> DiffSummary {
        let mut added = 0usize;
        let mut removed = 0usize;
        let mut modified = 0usize;
        let mut unchanged = 0usize;

        for entry in &self.entries {
            match entry {
                DiffEntry::Added { .. } => added += 1,
                DiffEntry::Removed { .. } => removed += 1,
                DiffEntry::Modified { .. } => modified += 1,
                DiffEntry::Unchanged { .. } => unchanged += 1,
            }
        }

        let total = added + removed + modified + unchanged;
        DiffSummary {
            added,
            removed,
            modified,
            unchanged,
            total,
        }
    }

    /// Build an incremental check plan from this diff.
    ///
    /// Nodes that are unchanged can be skipped; added and modified nodes
    /// need re-checking.
    #[must_use]
    pub fn incremental_plan(&self) -> IncrementalCheckPlan {
        let mut nodes_to_check = Vec::new();
        let mut nodes_to_skip = Vec::new();

        for entry in &self.entries {
            match entry {
                DiffEntry::Added { node_id } => {
                    nodes_to_check.push(*node_id);
                }
                DiffEntry::Modified { new_node_id, .. } => {
                    nodes_to_check.push(*new_node_id);
                }
                DiffEntry::Unchanged { new_node_id, .. } => {
                    nodes_to_skip.push(*new_node_id);
                }
                DiffEntry::Removed { .. } => {
                    // Nothing to check in the new proof for removed nodes.
                }
            }
        }

        let estimated_savings = if nodes_to_check.is_empty() && nodes_to_skip.is_empty() {
            0.0
        } else {
            let total = (nodes_to_check.len() + nodes_to_skip.len()) as f64;
            nodes_to_skip.len() as f64 / total
        };

        IncrementalCheckPlan {
            nodes_to_check,
            nodes_to_skip,
            estimated_savings,
        }
    }

    /// Identify proof fragments shared between old and new proofs.
    #[must_use]
    pub fn shared_subproofs(&self) -> Vec<SharedSubproof> {
        let mut subproofs = Vec::new();
        let mut seen = HashSet::new();

        for entry in &self.entries {
            if let DiffEntry::Unchanged {
                old_node_id,
                new_node_id,
            } = entry
            {
                if seen.insert((*old_node_id, *new_node_id)) {
                    subproofs.push(SharedSubproof {
                        old_root: *old_node_id,
                        new_root: *new_node_id,
                    });
                }
            }
        }

        subproofs
    }
}

// ---------------------------------------------------------------------------
// DiffSummary
// ---------------------------------------------------------------------------

/// High-level statistics from a proof diff.
#[derive(Debug, Clone, PartialEq)]
pub struct DiffSummary {
    pub added: usize,
    pub removed: usize,
    pub modified: usize,
    pub unchanged: usize,
    pub total: usize,
}

impl DiffSummary {
    /// Fraction of nodes that are structurally identical (0.0 to 1.0).
    #[must_use]
    pub fn structural_similarity(&self) -> f64 {
        if self.total == 0 {
            return 1.0;
        }
        self.unchanged as f64 / self.total as f64
    }

    /// Fraction of nodes that were added (0.0 to 1.0).
    #[must_use]
    pub fn added_fraction(&self) -> f64 {
        if self.total == 0 {
            return 0.0;
        }
        self.added as f64 / self.total as f64
    }

    /// Fraction of nodes that were removed (0.0 to 1.0).
    #[must_use]
    pub fn removed_fraction(&self) -> f64 {
        if self.total == 0 {
            return 0.0;
        }
        self.removed as f64 / self.total as f64
    }
}

impl fmt::Display for DiffSummary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "similarity={:.1}% added={} removed={} modified={} unchanged={}",
            self.structural_similarity() * 100.0,
            self.added,
            self.removed,
            self.modified,
            self.unchanged,
        )
    }
}

// ---------------------------------------------------------------------------
// IncrementalCheckPlan
// ---------------------------------------------------------------------------

/// Plan for which parts of a new proof need re-checking based on a diff.
#[derive(Debug, Clone)]
pub struct IncrementalCheckPlan {
    /// Nodes in the new proof that must be checked (added or modified).
    pub nodes_to_check: Vec<NodeId>,
    /// Nodes in the new proof that can be skipped (unchanged).
    pub nodes_to_skip: Vec<NodeId>,
    /// Estimated fraction of work saved (0.0 to 1.0).
    pub estimated_savings: f64,
}

impl IncrementalCheckPlan {
    /// Whether the plan indicates a full re-check is needed.
    #[must_use]
    pub fn is_full_recheck(&self) -> bool {
        self.nodes_to_skip.is_empty()
    }

    /// Whether the plan indicates no re-checking is needed.
    #[must_use]
    pub fn is_no_op(&self) -> bool {
        self.nodes_to_check.is_empty()
    }
}

// ---------------------------------------------------------------------------
// SharedSubproof
// ---------------------------------------------------------------------------

/// Identifies a proof fragment shared between old and new proofs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SharedSubproof {
    /// Root node in the old proof tree.
    pub old_root: NodeId,
    /// Corresponding root node in the new proof tree.
    pub new_root: NodeId,
}

// ---------------------------------------------------------------------------
// DiffConfig
// ---------------------------------------------------------------------------

/// Configuration for the proof differ.
#[derive(Debug, Clone)]
pub struct DiffConfig {
    /// If true, ignore the ordering of literals within clauses.
    pub ignore_literal_order: bool,
    /// If true, only compare structure (node kinds and edges), ignoring
    /// literal content.
    pub structural_only: bool,
    /// Maximum depth to descend when comparing. `None` means unlimited.
    pub max_depth: Option<usize>,
}

impl Default for DiffConfig {
    fn default() -> Self {
        Self {
            ignore_literal_order: true,
            structural_only: false,
            max_depth: None,
        }
    }
}

// ---------------------------------------------------------------------------
// ProofDiffer
// ---------------------------------------------------------------------------

/// Main differ: compares two proof trees and produces a [`DiffResult`].
pub struct ProofDiffer {
    config: DiffConfig,
}

impl ProofDiffer {
    /// Create a differ with the given configuration.
    #[must_use]
    pub fn new(config: DiffConfig) -> Self {
        Self { config }
    }

    /// Create a differ with default configuration.
    #[must_use]
    pub fn with_defaults() -> Self {
        Self::new(DiffConfig::default())
    }

    /// Compare two proof trees and return a diff result.
    ///
    /// The algorithm proceeds in two passes:
    ///
    /// 1. **Fingerprint matching** — compute bottom-up fingerprints for all
    ///    nodes in both trees and match nodes with identical fingerprints.
    /// 2. **Structural comparison** — for unmatched nodes, compare by position
    ///    and node kind to classify differences.
    #[must_use]
    pub fn diff(&self, old: &ProofTree, new: &ProofTree) -> DiffResult {
        // Phase 1: compute fingerprints for all nodes in both trees.
        let old_fps: HashMap<NodeId, ProofFingerprint> = old
            .node_ids()
            .filter_map(|id| ProofFingerprint::compute(old, id).map(|fp| (id, fp)))
            .collect();

        let new_fps: HashMap<NodeId, ProofFingerprint> = new
            .node_ids()
            .filter_map(|id| ProofFingerprint::compute(new, id).map(|fp| (id, fp)))
            .collect();

        // Phase 2: match by fingerprint.
        // Build reverse index: fingerprint -> list of old node IDs.
        let mut old_by_fp: HashMap<u64, Vec<NodeId>> = HashMap::new();
        for (&id, fp) in &old_fps {
            old_by_fp.entry(fp.value()).or_default().push(id);
        }

        let mut matched_old: HashSet<NodeId> = HashSet::new();
        let mut matched_new: HashSet<NodeId> = HashSet::new();
        let mut matched_nodes: HashMap<NodeId, NodeId> = HashMap::new();
        let mut entries = Vec::new();

        // Match new nodes to old nodes by fingerprint.
        for (&new_id, new_fp) in &new_fps {
            if let Some(old_ids) = old_by_fp.get(&new_fp.value()) {
                // Find the first unmatched old node with this fingerprint.
                if let Some(&old_id) = old_ids.iter().find(|id| !matched_old.contains(id)) {
                    matched_old.insert(old_id);
                    matched_new.insert(new_id);
                    matched_nodes.insert(old_id, new_id);
                    entries.push(DiffEntry::Unchanged {
                        old_node_id: old_id,
                        new_node_id: new_id,
                    });
                    continue;
                }
            }
        }

        // Phase 3: structural comparison for unmatched nodes.
        // Try to pair unmatched nodes by kind and position.
        let unmatched_old: Vec<NodeId> = old
            .node_ids()
            .filter(|id| !matched_old.contains(id))
            .collect();
        let unmatched_new: Vec<NodeId> = new
            .node_ids()
            .filter(|id| !matched_new.contains(id))
            .collect();

        let mut new_paired: HashSet<NodeId> = HashSet::new();

        for &old_id in &unmatched_old {
            if let Some(old_node) = old.nodes.get(&old_id) {
                // Look for an unmatched new node with the same kind.
                let paired = unmatched_new.iter().find(|&&nid| {
                    if new_paired.contains(&nid) {
                        return false;
                    }
                    if let Some(new_node) = new.nodes.get(&nid) {
                        self.same_kind(&old_node.kind, &new_node.kind)
                    } else {
                        false
                    }
                });

                if let Some(&new_id) = paired {
                    new_paired.insert(new_id);
                    let new_node = &new.nodes[&new_id];
                    let kind = self.classify_change(&old_node.kind, &new_node.kind);
                    matched_nodes.insert(old_id, new_id);
                    entries.push(DiffEntry::Modified {
                        old_node_id: old_id,
                        new_node_id: new_id,
                        kind,
                    });
                } else {
                    entries.push(DiffEntry::Removed { node_id: old_id });
                }
            }
        }

        // Any unmatched new nodes that weren't paired are additions.
        for &new_id in &unmatched_new {
            if !new_paired.contains(&new_id) {
                entries.push(DiffEntry::Added { node_id: new_id });
            }
        }

        // Respect max_depth: truncate entries referencing nodes deeper than
        // the configured limit.
        if let Some(max_depth) = self.config.max_depth {
            let old_depths = Self::compute_depths(old);
            let new_depths = Self::compute_depths(new);

            entries.retain(|entry| match entry {
                DiffEntry::Added { node_id } => {
                    new_depths.get(node_id).copied().unwrap_or(0) <= max_depth
                }
                DiffEntry::Removed { node_id } => {
                    old_depths.get(node_id).copied().unwrap_or(0) <= max_depth
                }
                DiffEntry::Modified { new_node_id, .. } => {
                    new_depths.get(new_node_id).copied().unwrap_or(0) <= max_depth
                }
                DiffEntry::Unchanged { new_node_id, .. } => {
                    new_depths.get(new_node_id).copied().unwrap_or(0) <= max_depth
                }
            });
        }

        DiffResult {
            entries,
            matched_nodes,
        }
    }

    /// Whether two node kinds have the same discriminant.
    fn same_kind(&self, a: &ProofNodeKind, b: &ProofNodeKind) -> bool {
        std::mem::discriminant(a) == std::mem::discriminant(b)
    }

    /// Classify the change between two nodes of the same kind.
    fn classify_change(&self, old: &ProofNodeKind, new: &ProofNodeKind) -> DiffKind {
        if self.config.structural_only {
            return DiffKind::StructureChanged;
        }

        match (old, new) {
            (
                ProofNodeKind::Resolution { pivot: old_p },
                ProofNodeKind::Resolution { pivot: new_p },
            ) => {
                if old_p != new_p {
                    DiffKind::PivotChanged {
                        old_pivot: *old_p,
                        new_pivot: *new_p,
                    }
                } else {
                    DiffKind::StructureChanged
                }
            }
            (
                ProofNodeKind::InputClause { literals: old_lits },
                ProofNodeKind::InputClause { literals: new_lits },
            ) => {
                let (mut old_sorted, mut new_sorted) = if self.config.ignore_literal_order {
                    let mut a = old_lits.clone();
                    let mut b = new_lits.clone();
                    a.sort();
                    b.sort();
                    (a, b)
                } else {
                    (old_lits.clone(), new_lits.clone())
                };
                // Dedup for comparison.
                old_sorted.dedup();
                new_sorted.dedup();

                if old_sorted != new_sorted {
                    DiffKind::InputClauseChanged {
                        old_literals: old_lits.clone(),
                        new_literals: new_lits.clone(),
                    }
                } else {
                    DiffKind::StructureChanged
                }
            }
            _ => DiffKind::StructureChanged,
        }
    }

    /// Compute the depth of each node from the root via BFS.
    fn compute_depths(tree: &ProofTree) -> HashMap<NodeId, usize> {
        let mut depths = HashMap::new();
        if let Some(root) = tree.root {
            let mut stack = vec![(root, 0usize)];
            while let Some((node_id, depth)) = stack.pop() {
                if depths.contains_key(&node_id) {
                    continue;
                }
                depths.insert(node_id, depth);
                if let Some(children) = tree.edges.get(&node_id) {
                    for &child_id in children {
                        stack.push((child_id, depth + 1));
                    }
                }
            }
        }
        depths
    }
}

// ---------------------------------------------------------------------------
// ProofEvolution
// ---------------------------------------------------------------------------

/// Tracks how a proof changes over time across multiple versions.
///
/// Each version is a snapshot of a proof tree. The evolution tracker stores
/// all versions and can compute diffs between any two.
#[derive(Debug, Clone)]
pub struct ProofEvolution {
    versions: Vec<(String, ProofTree)>,
}

impl ProofEvolution {
    /// Create a new, empty evolution tracker.
    #[must_use]
    pub fn new() -> Self {
        Self {
            versions: Vec::new(),
        }
    }

    /// Add a new version with the given label.
    pub fn add_version(&mut self, label: &str, proof: ProofTree) {
        self.versions.push((label.to_string(), proof));
    }

    /// Number of versions tracked.
    #[must_use]
    pub fn version_count(&self) -> usize {
        self.versions.len()
    }

    /// Get a version by index.
    #[must_use]
    pub fn version(&self, index: usize) -> Option<(&str, &ProofTree)> {
        self.versions
            .get(index)
            .map(|(label, tree)| (label.as_str(), tree))
    }

    /// Compute the diff between two versions (by index).
    ///
    /// Returns `None` if either index is out of bounds.
    #[must_use]
    pub fn changes_between(&self, v1: usize, v2: usize) -> Option<DiffResult> {
        let (_, old) = self.versions.get(v1)?;
        let (_, new) = self.versions.get(v2)?;
        let differ = ProofDiffer::with_defaults();
        Some(differ.diff(old, new))
    }

    /// Compute the similarity trend across consecutive versions.
    ///
    /// Returns a vector of `(version_label, similarity_to_previous)`.
    /// The first version has similarity 1.0 (identical to itself).
    #[must_use]
    pub fn similarity_trend(&self) -> Vec<(String, f64)> {
        if self.versions.is_empty() {
            return Vec::new();
        }

        let differ = ProofDiffer::with_defaults();
        let mut trend = vec![(self.versions[0].0.clone(), 1.0)];

        for i in 1..self.versions.len() {
            let diff = differ.diff(&self.versions[i - 1].1, &self.versions[i].1);
            let sim = diff.summary().structural_similarity();
            trend.push((self.versions[i].0.clone(), sim));
        }

        trend
    }
}

impl Default for ProofEvolution {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- Helpers --------------------------------------------------------------

    fn simple_tree() -> ProofTree {
        // Two input clauses resolved together.
        // Clause 1: {1, 2}
        // Clause 2: {-1, 3}
        // Resolution on pivot 1 -> clause 3: {2, 3}
        ProofTree::from_steps(&[(1, &[1, 2]), (2, &[-1, 3])], &[(3, 1, 2, 1)])
    }

    fn two_step_tree() -> ProofTree {
        // Clause 1: {1, 2}
        // Clause 2: {-1, 3}
        // Clause 3: {-2}
        // Step 4: resolve 1 & 2 on pivot 1 -> {2, 3}
        // Step 5: resolve 4 & 3 on pivot 2 -> {3}
        ProofTree::from_steps(
            &[(1, &[1, 2]), (2, &[-1, 3]), (3, &[-2])],
            &[(4, 1, 2, 1), (5, 4, 3, 2)],
        )
    }

    // -- ProofTree construction -----------------------------------------------

    #[test]
    fn test_proof_tree_from_steps_creates_nodes() {
        let tree = simple_tree();
        assert_eq!(tree.len(), 3);
        assert_eq!(tree.root, Some(3));
    }

    #[test]
    fn test_proof_tree_from_steps_creates_edges() {
        let tree = simple_tree();
        let edges = tree.edges.get(&3).expect("should have edges for node 3");
        assert_eq!(edges, &[1, 2]);
    }

    #[test]
    fn test_proof_tree_empty() {
        let tree = ProofTree::new();
        assert!(tree.is_empty());
        assert_eq!(tree.len(), 0);
        assert_eq!(tree.root, None);
    }

    #[test]
    fn test_proof_tree_from_input_clauses_only() {
        let tree = ProofTree::from_steps(&[(1, &[1, 2]), (2, &[-1])], &[]);
        assert_eq!(tree.len(), 2);
        assert_eq!(tree.root, Some(1));
    }

    #[test]
    fn test_proof_tree_subtree_full() {
        let tree = two_step_tree();
        let sub = tree.subtree(5);
        // Should include: 5, 4, 1, 2, 3
        assert_eq!(sub.len(), 5);
        assert_eq!(sub.root, Some(5));
    }

    #[test]
    fn test_proof_tree_subtree_partial() {
        let tree = two_step_tree();
        let sub = tree.subtree(4);
        // Should include: 4, 1, 2
        assert_eq!(sub.len(), 3);
        assert_eq!(sub.root, Some(4));
    }

    #[test]
    fn test_proof_tree_subtree_leaf() {
        let tree = two_step_tree();
        let sub = tree.subtree(1);
        assert_eq!(sub.len(), 1);
        assert_eq!(sub.root, Some(1));
    }

    #[test]
    fn test_proof_tree_subtree_missing_node() {
        let tree = simple_tree();
        let sub = tree.subtree(999);
        assert!(sub.is_empty());
    }

    #[test]
    fn test_proof_tree_add_theory_lemma() {
        let mut tree = simple_tree();
        tree.add_theory_lemma(10, "EUF", &[5, -6]);
        assert_eq!(tree.len(), 4);
        let node = &tree.nodes[&10];
        assert!(matches!(
            &node.kind,
            ProofNodeKind::TheoryLemma { theory, .. } if theory == "EUF"
        ));
    }

    #[test]
    fn test_proof_tree_node_ids() {
        let tree = simple_tree();
        let ids: Vec<NodeId> = tree.node_ids().collect();
        assert_eq!(ids, vec![1, 2, 3]);
    }

    // -- ProofFingerprint -----------------------------------------------------

    #[test]
    fn test_fingerprint_same_tree_same_node() {
        let tree = simple_tree();
        let fp1 = ProofFingerprint::compute(&tree, 3).unwrap();
        let fp2 = ProofFingerprint::compute(&tree, 3).unwrap();
        assert_eq!(fp1, fp2);
    }

    #[test]
    fn test_fingerprint_different_nodes_differ() {
        let tree = simple_tree();
        let fp1 = ProofFingerprint::compute(&tree, 1).unwrap();
        let fp2 = ProofFingerprint::compute(&tree, 2).unwrap();
        assert_ne!(fp1, fp2);
    }

    #[test]
    fn test_fingerprint_identical_trees_match() {
        let tree1 = simple_tree();
        let tree2 = simple_tree();
        let fp1 = ProofFingerprint::compute(&tree1, 3).unwrap();
        let fp2 = ProofFingerprint::compute(&tree2, 3).unwrap();
        assert_eq!(fp1, fp2);
    }

    #[test]
    fn test_fingerprint_missing_node_returns_none() {
        let tree = simple_tree();
        assert!(ProofFingerprint::compute(&tree, 999).is_none());
    }

    #[test]
    fn test_fingerprint_display_hex() {
        let tree = simple_tree();
        let fp = ProofFingerprint::compute(&tree, 1).unwrap();
        let s = format!("{fp}");
        assert_eq!(s.len(), 16);
        assert!(s.chars().all(|c| c.is_ascii_hexdigit()));
    }

    #[test]
    fn test_fingerprint_theory_lemma() {
        let mut tree = ProofTree::new();
        tree.add_theory_lemma(1, "LRA", &[10, -20]);
        let fp = ProofFingerprint::compute(&tree, 1).unwrap();
        assert_ne!(fp.value(), 0);
    }

    #[test]
    fn test_fingerprint_literal_order_irrelevant_for_input() {
        let tree1 = ProofTree::from_steps(&[(1, &[1, 2, 3])], &[]);
        let tree2 = ProofTree::from_steps(&[(1, &[3, 1, 2])], &[]);
        let fp1 = ProofFingerprint::compute(&tree1, 1).unwrap();
        let fp2 = ProofFingerprint::compute(&tree2, 1).unwrap();
        assert_eq!(
            fp1, fp2,
            "fingerprint should be order-independent for input clauses"
        );
    }

    // -- ProofDiffer ----------------------------------------------------------

    #[test]
    fn test_diff_identical_trees_all_unchanged() {
        let tree = simple_tree();
        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&tree, &tree);
        let summary = result.summary();
        assert_eq!(summary.unchanged, 3);
        assert_eq!(summary.added, 0);
        assert_eq!(summary.removed, 0);
        assert_eq!(summary.modified, 0);
    }

    #[test]
    fn test_diff_empty_to_nonempty_all_added() {
        let old = ProofTree::new();
        let new = simple_tree();
        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let summary = result.summary();
        assert_eq!(summary.added, 3);
        assert_eq!(summary.removed, 0);
    }

    #[test]
    fn test_diff_nonempty_to_empty_all_removed() {
        let old = simple_tree();
        let new = ProofTree::new();
        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let summary = result.summary();
        assert_eq!(summary.removed, 3);
        assert_eq!(summary.added, 0);
    }

    #[test]
    fn test_diff_both_empty_no_entries() {
        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&ProofTree::new(), &ProofTree::new());
        assert!(result.entries.is_empty());
    }

    #[test]
    fn test_diff_detects_pivot_change() {
        let old = ProofTree::from_steps(&[(1, &[1, 2]), (2, &[-1, 3])], &[(3, 1, 2, 1)]);
        let new = ProofTree::from_steps(
            &[(1, &[1, 2]), (2, &[-1, 3])],
            &[(3, 1, 2, 2)], // pivot changed from 1 to 2
        );
        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let has_pivot_change = result.entries.iter().any(|e| {
            matches!(
                e,
                DiffEntry::Modified {
                    kind: DiffKind::PivotChanged { .. },
                    ..
                }
            )
        });
        assert!(has_pivot_change, "should detect pivot change");
    }

    #[test]
    fn test_diff_detects_input_clause_change() {
        let old = ProofTree::from_steps(&[(1, &[1, 2])], &[]);
        let new = ProofTree::from_steps(&[(1, &[1, 3])], &[]); // literal 2 -> 3
        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let has_clause_change = result.entries.iter().any(|e| {
            matches!(
                e,
                DiffEntry::Modified {
                    kind: DiffKind::InputClauseChanged { .. },
                    ..
                }
            )
        });
        assert!(has_clause_change, "should detect input clause change");
    }

    #[test]
    fn test_diff_detects_added_node() {
        let old = ProofTree::from_steps(&[(1, &[1])], &[]);
        let new = ProofTree::from_steps(&[(1, &[1]), (2, &[-1])], &[]);
        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let summary = result.summary();
        assert_eq!(summary.added, 1);
        assert_eq!(summary.unchanged, 1);
    }

    #[test]
    fn test_diff_detects_removed_node() {
        let old = ProofTree::from_steps(&[(1, &[1]), (2, &[-1])], &[]);
        let new = ProofTree::from_steps(&[(1, &[1])], &[]);
        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let summary = result.summary();
        assert_eq!(summary.removed, 1);
        assert_eq!(summary.unchanged, 1);
    }

    #[test]
    fn test_diff_structural_only_mode() {
        let old = ProofTree::from_steps(&[(1, &[1, 2]), (2, &[-1, 3])], &[(3, 1, 2, 1)]);
        let new = ProofTree::from_steps(
            &[(1, &[1, 2]), (2, &[-1, 3])],
            &[(3, 1, 2, 5)], // different pivot
        );
        let config = DiffConfig {
            structural_only: true,
            ..DiffConfig::default()
        };
        let differ = ProofDiffer::new(config);
        let result = differ.diff(&old, &new);
        // In structural_only mode, modified nodes get StructureChanged.
        let has_structure = result.entries.iter().any(|e| {
            matches!(
                e,
                DiffEntry::Modified {
                    kind: DiffKind::StructureChanged,
                    ..
                }
            )
        });
        assert!(has_structure);
    }

    #[test]
    fn test_diff_max_depth_limits_entries() {
        let tree = two_step_tree();
        let mut modified = two_step_tree();
        // Change a deep leaf node.
        modified.nodes.get_mut(&1).unwrap().kind =
            ProofNodeKind::InputClause { literals: vec![99] };

        let config = DiffConfig {
            max_depth: Some(0),
            ..DiffConfig::default()
        };
        let differ = ProofDiffer::new(config);
        let result = differ.diff(&tree, &modified);
        // Only the root (depth 0) should appear.
        for entry in &result.entries {
            match entry {
                DiffEntry::Added { node_id }
                | DiffEntry::Removed { node_id }
                | DiffEntry::Modified {
                    new_node_id: node_id,
                    ..
                }
                | DiffEntry::Unchanged {
                    new_node_id: node_id,
                    ..
                } => {
                    // Node should be at depth 0 in the new tree.
                    let depths = ProofDiffer::compute_depths(&modified);
                    let d = depths.get(node_id).copied().unwrap_or(usize::MAX);
                    assert!(d == 0, "node {node_id} at depth {d} exceeds max_depth 0");
                }
            }
        }
    }

    // -- DiffSummary ----------------------------------------------------------

    #[test]
    fn test_summary_structural_similarity_identical() {
        let tree = simple_tree();
        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&tree, &tree);
        let sim = result.summary().structural_similarity();
        assert!((sim - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_summary_structural_similarity_disjoint() {
        let old = ProofTree::from_steps(&[(1, &[1])], &[]);
        let new = ProofTree::from_steps(&[(2, &[-2])], &[]);
        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let sim = result.summary().structural_similarity();
        assert!(sim < 1.0, "disjoint trees should have similarity < 1.0");
    }

    #[test]
    fn test_summary_empty_diff_similarity_one() {
        let summary = DiffSummary {
            added: 0,
            removed: 0,
            modified: 0,
            unchanged: 0,
            total: 0,
        };
        assert!((summary.structural_similarity() - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_summary_added_fraction() {
        let summary = DiffSummary {
            added: 3,
            removed: 0,
            modified: 0,
            unchanged: 7,
            total: 10,
        };
        assert!((summary.added_fraction() - 0.3).abs() < f64::EPSILON);
    }

    #[test]
    fn test_summary_removed_fraction() {
        let summary = DiffSummary {
            added: 0,
            removed: 2,
            modified: 0,
            unchanged: 8,
            total: 10,
        };
        assert!((summary.removed_fraction() - 0.2).abs() < f64::EPSILON);
    }

    #[test]
    fn test_summary_display_format() {
        let summary = DiffSummary {
            added: 1,
            removed: 2,
            modified: 3,
            unchanged: 4,
            total: 10,
        };
        let s = format!("{summary}");
        assert!(s.contains("similarity="));
        assert!(s.contains("added=1"));
        assert!(s.contains("removed=2"));
        assert!(s.contains("modified=3"));
        assert!(s.contains("unchanged=4"));
    }

    // -- IncrementalCheckPlan -------------------------------------------------

    #[test]
    fn test_incremental_plan_identical_is_no_op() {
        let tree = simple_tree();
        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&tree, &tree);
        let plan = result.incremental_plan();
        assert!(plan.is_no_op());
        assert!(!plan.is_full_recheck());
        assert!((plan.estimated_savings - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_incremental_plan_all_new_is_full_recheck() {
        let old = ProofTree::new();
        let new = simple_tree();
        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let plan = result.incremental_plan();
        assert!(plan.is_full_recheck());
        assert!(!plan.is_no_op());
        assert!((plan.estimated_savings - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_incremental_plan_partial_savings() {
        let old = ProofTree::from_steps(&[(1, &[1, 2]), (2, &[-1, 3])], &[(3, 1, 2, 1)]);
        let mut new = ProofTree::from_steps(&[(1, &[1, 2]), (2, &[-1, 3])], &[(3, 1, 2, 1)]);
        // Add a new node to the new tree.
        new.nodes.insert(
            4,
            ProofNode {
                id: 4,
                kind: ProofNodeKind::InputClause {
                    literals: vec![5, 6],
                },
            },
        );
        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let plan = result.incremental_plan();
        assert!(!plan.is_no_op());
        assert!(!plan.is_full_recheck());
        assert!(plan.estimated_savings > 0.0);
        assert!(plan.estimated_savings < 1.0);
    }

    // -- SharedSubproof -------------------------------------------------------

    #[test]
    fn test_shared_subproofs_identical_trees() {
        let tree = simple_tree();
        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&tree, &tree);
        let shared = result.shared_subproofs();
        assert_eq!(shared.len(), 3, "all 3 nodes should be shared");
    }

    #[test]
    fn test_shared_subproofs_empty_when_disjoint() {
        let old = ProofTree::from_steps(&[(1, &[1])], &[]);
        let new = ProofTree::from_steps(&[(2, &[-2])], &[]);
        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let shared = result.shared_subproofs();
        assert!(shared.is_empty());
    }

    // -- ProofEvolution -------------------------------------------------------

    #[test]
    fn test_evolution_empty() {
        let evo = ProofEvolution::new();
        assert_eq!(evo.version_count(), 0);
        assert!(evo.version(0).is_none());
    }

    #[test]
    fn test_evolution_add_versions() {
        let mut evo = ProofEvolution::new();
        evo.add_version("v1", simple_tree());
        evo.add_version("v2", two_step_tree());
        assert_eq!(evo.version_count(), 2);
        assert_eq!(evo.version(0).unwrap().0, "v1");
        assert_eq!(evo.version(1).unwrap().0, "v2");
    }

    #[test]
    fn test_evolution_changes_between_same_version() {
        let mut evo = ProofEvolution::new();
        evo.add_version("v1", simple_tree());
        let diff = evo.changes_between(0, 0).expect("should return diff");
        let summary = diff.summary();
        assert_eq!(summary.unchanged, 3);
        assert_eq!(summary.added, 0);
    }

    #[test]
    fn test_evolution_changes_between_different_versions() {
        let mut evo = ProofEvolution::new();
        evo.add_version("v1", simple_tree());
        evo.add_version("v2", two_step_tree());
        let diff = evo.changes_between(0, 1).expect("should return diff");
        let summary = diff.summary();
        assert!(summary.total > 0);
    }

    #[test]
    fn test_evolution_changes_between_out_of_bounds() {
        let mut evo = ProofEvolution::new();
        evo.add_version("v1", simple_tree());
        assert!(evo.changes_between(0, 5).is_none());
        assert!(evo.changes_between(5, 0).is_none());
    }

    #[test]
    fn test_evolution_similarity_trend_single_version() {
        let mut evo = ProofEvolution::new();
        evo.add_version("v1", simple_tree());
        let trend = evo.similarity_trend();
        assert_eq!(trend.len(), 1);
        assert!((trend[0].1 - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_evolution_similarity_trend_identical_versions() {
        let mut evo = ProofEvolution::new();
        evo.add_version("v1", simple_tree());
        evo.add_version("v2", simple_tree());
        evo.add_version("v3", simple_tree());
        let trend = evo.similarity_trend();
        assert_eq!(trend.len(), 3);
        for (_, sim) in &trend {
            assert!((*sim - 1.0).abs() < f64::EPSILON);
        }
    }

    #[test]
    fn test_evolution_similarity_trend_diverging() {
        let mut evo = ProofEvolution::new();
        evo.add_version("v1", simple_tree());
        evo.add_version("v2", two_step_tree());
        let trend = evo.similarity_trend();
        assert_eq!(trend.len(), 2);
        // First is always 1.0.
        assert!((trend[0].1 - 1.0).abs() < f64::EPSILON);
        // Second should be < 1.0 since the trees differ.
        assert!(trend[1].1 < 1.0);
    }

    #[test]
    fn test_evolution_similarity_trend_empty() {
        let evo = ProofEvolution::new();
        assert!(evo.similarity_trend().is_empty());
    }

    // -- DiffKind Display -----------------------------------------------------

    #[test]
    fn test_diff_kind_display_node_added() {
        assert_eq!(format!("{}", DiffKind::NodeAdded), "node added");
    }

    #[test]
    fn test_diff_kind_display_pivot_changed() {
        let kind = DiffKind::PivotChanged {
            old_pivot: 1,
            new_pivot: 2,
        };
        assert_eq!(format!("{kind}"), "pivot changed: 1 -> 2");
    }

    // -- Edge cases -----------------------------------------------------------

    #[test]
    fn test_diff_single_node_trees_identical() {
        let old = ProofTree::from_steps(&[(1, &[42])], &[]);
        let new = ProofTree::from_steps(&[(1, &[42])], &[]);
        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        assert_eq!(result.summary().unchanged, 1);
    }

    #[test]
    fn test_diff_large_tree_performance() {
        // Build a chain of 100 resolution steps.
        let mut inputs: Vec<(NodeId, Vec<LiteralId>)> = Vec::new();
        for i in 1..=100 {
            inputs.push((i, vec![i as LiteralId, -(i as LiteralId + 100)]));
        }
        let input_refs: Vec<(NodeId, &[LiteralId])> = inputs
            .iter()
            .map(|(id, lits)| (*id, lits.as_slice()))
            .collect();

        let mut steps = Vec::new();
        // Chain: resolve input 1 & input 2 -> step, then step & input 3, etc.
        let mut current = 1;
        for (next_id, i) in (101u64..).zip(2..=100u64) {
            steps.push((next_id, current, i, i as LiteralId));
            current = next_id;
        }
        let step_refs: Vec<(NodeId, NodeId, NodeId, LiteralId)> = steps;

        let tree = ProofTree::from_steps(&input_refs, &step_refs);
        assert_eq!(tree.len(), 199); // 100 inputs + 99 steps

        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&tree, &tree);
        assert_eq!(result.summary().unchanged, 199);
    }

    #[test]
    fn test_fingerprint_resolution_node_includes_children() {
        // Two trees with same pivot but different children should differ.
        let tree1 = ProofTree::from_steps(&[(1, &[1, 2]), (2, &[-1, 3])], &[(3, 1, 2, 1)]);
        let tree2 = ProofTree::from_steps(&[(1, &[1, 5]), (2, &[-1, 6])], &[(3, 1, 2, 1)]);
        let fp1 = ProofFingerprint::compute(&tree1, 3).unwrap();
        let fp2 = ProofFingerprint::compute(&tree2, 3).unwrap();
        assert_ne!(
            fp1, fp2,
            "different children should produce different fingerprints"
        );
    }

    #[test]
    fn test_default_config_ignore_order_true() {
        let config = DiffConfig::default();
        assert!(config.ignore_literal_order);
        assert!(!config.structural_only);
        assert!(config.max_depth.is_none());
    }

    #[test]
    fn test_proof_tree_default_is_empty() {
        let tree = ProofTree::default();
        assert!(tree.is_empty());
    }

    #[test]
    fn test_evolution_default_is_empty() {
        let evo = ProofEvolution::default();
        assert_eq!(evo.version_count(), 0);
    }

    // -- Added: diff behavior with theory lemma nodes -------------------------

    #[test]
    fn test_diff_theory_lemma_added_to_proof() {
        // Old proof: two input clauses, one resolution.
        let old = simple_tree();
        // New proof: same structure plus a theory lemma node.
        let mut new = simple_tree();
        new.add_theory_lemma(10, "EUF", &[5, -6]);

        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let summary = result.summary();

        assert_eq!(summary.unchanged, 3, "original 3 nodes should still match");
        assert_eq!(summary.added, 1, "theory lemma should appear as added");
        assert_eq!(summary.removed, 0);
        assert_eq!(summary.modified, 0);
    }

    #[test]
    fn test_diff_theory_lemma_removed_from_proof() {
        // Old proof includes a theory lemma; new proof drops it.
        let mut old = simple_tree();
        old.add_theory_lemma(10, "BV", &[7, -8]);
        let new = simple_tree();

        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let summary = result.summary();

        assert_eq!(summary.unchanged, 3, "original 3 nodes should still match");
        assert_eq!(summary.removed, 1, "theory lemma should appear as removed");
        assert_eq!(summary.added, 0);
    }

    // -- Added: modified resolution pivot with unchanged children -------------

    #[test]
    fn test_diff_pivot_change_preserves_unchanged_children() {
        // Two proofs sharing the same input clauses but different resolution pivot.
        let old = ProofTree::from_steps(&[(1, &[1, 2]), (2, &[-1, 3])], &[(3, 1, 2, 1)]);
        let new = ProofTree::from_steps(
            &[(1, &[1, 2]), (2, &[-1, 3])],
            &[(3, 1, 2, 7)], // pivot changed from 1 to 7
        );

        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let summary = result.summary();

        // The two input clauses are identical and should be unchanged.
        assert_eq!(summary.unchanged, 2, "input clauses 1 and 2 should match");
        // The resolution node has a different pivot so fingerprint differs.
        assert_eq!(summary.modified, 1, "resolution node should be modified");

        // Verify the modification is specifically a PivotChanged.
        let pivot_entry = result.entries.iter().find(|e| {
            matches!(
                e,
                DiffEntry::Modified {
                    kind: DiffKind::PivotChanged { .. },
                    ..
                }
            )
        });
        let DiffEntry::Modified {
            kind:
                DiffKind::PivotChanged {
                    old_pivot,
                    new_pivot,
                },
            ..
        } = pivot_entry.expect("should have a PivotChanged entry")
        else {
            panic!("wrong variant");
        };
        assert_eq!(*old_pivot, 1);
        assert_eq!(*new_pivot, 7);
    }

    // -- Added: minimal single-clause difference ------------------------------

    #[test]
    fn test_diff_single_input_clause_literal_change() {
        // Two single-node proofs that differ in one literal.
        let old = ProofTree::from_steps(&[(1, &[10, 20, 30])], &[]);
        let new = ProofTree::from_steps(&[(1, &[10, 20, 99])], &[]); // 30 -> 99

        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let summary = result.summary();

        // They cannot fingerprint-match, so the differ should pair them by kind.
        assert_eq!(summary.total, 1, "one entry total for one-node trees");
        assert_eq!(summary.modified, 1, "the single node should be modified");

        let clause_change = result.entries.iter().any(|e| {
            matches!(
                e,
                DiffEntry::Modified {
                    kind: DiffKind::InputClauseChanged { .. },
                    ..
                }
            )
        });
        assert!(clause_change, "should classify as InputClauseChanged");
    }

    // -- Added: DiffKind Display for remaining variants -----------------------

    #[test]
    fn test_diff_kind_display_node_removed() {
        assert_eq!(format!("{}", DiffKind::NodeRemoved), "node removed");
    }

    #[test]
    fn test_diff_kind_display_input_clause_changed() {
        let kind = DiffKind::InputClauseChanged {
            old_literals: vec![1, 2],
            new_literals: vec![1, 3],
        };
        assert_eq!(format!("{kind}"), "input clause changed");
    }

    #[test]
    fn test_diff_kind_display_structure_changed() {
        assert_eq!(
            format!("{}", DiffKind::StructureChanged),
            "structure changed"
        );
    }

    // -- Added: DiffSummary display at 100% similarity ------------------------

    #[test]
    fn test_summary_display_full_similarity() {
        let summary = DiffSummary {
            added: 0,
            removed: 0,
            modified: 0,
            unchanged: 5,
            total: 5,
        };
        let s = format!("{summary}");
        assert!(
            s.contains("similarity=100.0%"),
            "expected 100.0%% similarity in '{s}'",
        );
        assert!(s.contains("added=0"));
        assert!(s.contains("unchanged=5"));
    }

    // -- Added: IncrementalCheckPlan with mixed diff types --------------------

    #[test]
    fn test_incremental_plan_mixed_added_modified_unchanged() {
        // Build a proof, modify one leaf, add a new node — keeps some unchanged.
        let old = ProofTree::from_steps(&[(1, &[1, 2]), (2, &[-1, 3])], &[(3, 1, 2, 1)]);
        // New proof: clause 2 has different literals (modified), plus a brand
        // new node 4.
        let mut new = ProofTree::from_steps(&[(1, &[1, 2]), (2, &[-1, 99])], &[(3, 1, 2, 1)]);
        new.nodes.insert(
            4,
            ProofNode {
                id: 4,
                kind: ProofNodeKind::InputClause {
                    literals: vec![50, 60],
                },
            },
        );

        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let plan = result.incremental_plan();

        // Should not be a no-op (there are changes) and not a full recheck
        // (some nodes are unchanged).
        assert!(!plan.is_no_op(), "there are new/modified nodes to check");
        assert!(
            !plan.nodes_to_check.is_empty(),
            "at least the added and modified nodes need checking",
        );
        assert!(
            plan.estimated_savings > 0.0,
            "some savings from unchanged nodes"
        );
        assert!(plan.estimated_savings < 1.0, "not everything is unchanged");
    }

    // -- Added: SharedSubproof partial sharing --------------------------------

    #[test]
    fn test_shared_subproofs_partial_overlap() {
        // Old: two input clauses + resolution.
        let old = ProofTree::from_steps(&[(1, &[1, 2]), (2, &[-1, 3])], &[(3, 1, 2, 1)]);
        // New: keeps clause 1 identical, replaces clause 2 with different
        // literals, and changes the resolution pivot.
        let new = ProofTree::from_steps(&[(1, &[1, 2]), (2, &[-1, 99])], &[(3, 1, 2, 5)]);

        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let shared = result.shared_subproofs();

        // Clause 1 is identical and should be shared. Clause 2 and the
        // resolution node differ, so they should not be shared.
        assert_eq!(shared.len(), 1, "only clause 1 should be shared");
        assert!(
            shared.iter().any(|s| s.old_root == 1 && s.new_root == 1),
            "shared subproof should map old node 1 to new node 1",
        );
    }

    // -- Added: two-step proof with deep leaf change --------------------------

    #[test]
    fn test_diff_deep_leaf_change_propagates_to_ancestors() {
        // Old: full two-step proof.
        let old = two_step_tree();
        // New: identical except clause 1 has different literals.
        let mut new = two_step_tree();
        new.nodes.get_mut(&1).unwrap().kind = ProofNodeKind::InputClause {
            literals: vec![77, 88],
        };

        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let summary = result.summary();

        // Clause 1 changed → fingerprint of resolution step 4 changes (it
        // depends on clause 1) → fingerprint of step 5 changes (depends on
        // step 4). Clause 2 and clause 3 are unchanged.
        assert_eq!(
            summary.unchanged, 2,
            "clauses 2 and 3 should remain unchanged",
        );
        // Nodes 1, 4, and 5 should appear as modified or added/removed.
        assert!(
            summary.modified + summary.added + summary.removed >= 1,
            "at least node 1 should be modified (total non-unchanged = {})",
            summary.modified + summary.added + summary.removed,
        );
        // Overall total should account for all 5 nodes.
        assert_eq!(summary.total, 5, "both trees have 5 nodes each");
    }

    // =====================================================================
    // Extended test coverage
    // =====================================================================

    // -- Theory lemma fingerprint differences --------------------------------

    #[test]
    fn test_fingerprint_theory_lemma_different_theory_same_literals() {
        let mut tree1 = ProofTree::new();
        tree1.add_theory_lemma(1, "EUF", &[10, -20]);
        let mut tree2 = ProofTree::new();
        tree2.add_theory_lemma(1, "LRA", &[10, -20]);

        let fp1 = ProofFingerprint::compute(&tree1, 1).unwrap();
        let fp2 = ProofFingerprint::compute(&tree2, 1).unwrap();
        assert_ne!(
            fp1, fp2,
            "different theory names should produce different fingerprints"
        );
    }

    #[test]
    fn test_fingerprint_theory_lemma_same_theory_different_literals() {
        let mut tree1 = ProofTree::new();
        tree1.add_theory_lemma(1, "BV", &[10, -20]);
        let mut tree2 = ProofTree::new();
        tree2.add_theory_lemma(1, "BV", &[10, -30]);

        let fp1 = ProofFingerprint::compute(&tree1, 1).unwrap();
        let fp2 = ProofFingerprint::compute(&tree2, 1).unwrap();
        assert_ne!(
            fp1, fp2,
            "different literals should produce different fingerprints"
        );
    }

    #[test]
    fn test_fingerprint_theory_lemma_literal_order_irrelevant() {
        let mut tree1 = ProofTree::new();
        tree1.add_theory_lemma(1, "NIA", &[5, 3, 1]);
        let mut tree2 = ProofTree::new();
        tree2.add_theory_lemma(1, "NIA", &[1, 3, 5]);

        let fp1 = ProofFingerprint::compute(&tree1, 1).unwrap();
        let fp2 = ProofFingerprint::compute(&tree2, 1).unwrap();
        assert_eq!(
            fp1, fp2,
            "theory lemma fingerprints should be order-independent for literals"
        );
    }

    // -- Theory lemma modification detection ---------------------------------

    #[test]
    fn test_diff_theory_lemma_theory_name_changed() {
        // Old proof has an EUF theory lemma, new proof has LRA with same literals.
        let mut old = ProofTree::new();
        old.add_theory_lemma(1, "EUF", &[5, -6]);
        old.root = Some(1);

        let mut new = ProofTree::new();
        new.add_theory_lemma(1, "LRA", &[5, -6]);
        new.root = Some(1);

        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let summary = result.summary();

        // The fingerprints differ so they won't match; both are TheoryLemma
        // so they should pair and classify as StructureChanged (theory name
        // difference falls through to the catch-all).
        assert_eq!(summary.total, 1);
        assert_eq!(
            summary.modified, 1,
            "theory name change should be detected as modification"
        );
    }

    #[test]
    fn test_diff_theory_lemma_literals_changed() {
        let mut old = ProofTree::new();
        old.add_theory_lemma(1, "BV", &[10, 20]);
        old.root = Some(1);

        let mut new = ProofTree::new();
        new.add_theory_lemma(1, "BV", &[10, 30]);
        new.root = Some(1);

        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let summary = result.summary();

        assert_eq!(
            summary.modified, 1,
            "theory lemma literal change should be detected"
        );
    }

    #[test]
    fn test_diff_multiple_theory_lemmas_mixed() {
        // Old: two theory lemmas (EUF and BV).
        let mut old = simple_tree();
        old.add_theory_lemma(10, "EUF", &[5, -6]);
        old.add_theory_lemma(11, "BV", &[7, -8]);

        // New: same base tree, same EUF lemma, but BV lemma changed literals.
        let mut new = simple_tree();
        new.add_theory_lemma(10, "EUF", &[5, -6]);
        new.add_theory_lemma(11, "BV", &[7, -9]); // -8 -> -9

        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let summary = result.summary();

        // 3 base nodes unchanged + EUF lemma unchanged = 4 unchanged.
        assert_eq!(
            summary.unchanged, 4,
            "3 base nodes + EUF lemma should be unchanged"
        );
        // BV lemma changed.
        assert_eq!(summary.modified, 1, "BV lemma should be modified");
    }

    // -- ignore_literal_order=false ------------------------------------------

    #[test]
    fn test_diff_literal_order_matters_when_config_false() {
        // With ignore_literal_order=false, same literals in different order
        // should be detected as a change.
        let old = ProofTree::from_steps(&[(1, &[1, 2, 3])], &[]);
        let new = ProofTree::from_steps(&[(1, &[3, 2, 1])], &[]);

        let config = DiffConfig {
            ignore_literal_order: false,
            ..DiffConfig::default()
        };
        let differ = ProofDiffer::new(config);
        let result = differ.diff(&old, &new);
        let summary = result.summary();

        // Fingerprints sort literals, so they still match. The differ will
        // see them as unchanged at the fingerprint level. This test
        // documents that fingerprinting is always order-independent even when
        // the config says order matters (the config only affects
        // classify_change for unmatched nodes).
        assert_eq!(summary.unchanged, 1);
    }

    #[test]
    fn test_diff_literal_order_matters_when_content_differs() {
        // When ignore_literal_order=false AND content actually differs,
        // the change should be classified as InputClauseChanged (not
        // StructureChanged) because the sorted+deduped forms also differ.
        let old = ProofTree::from_steps(&[(1, &[1, 2])], &[]);
        let new = ProofTree::from_steps(&[(1, &[2, 3])], &[]);

        let config = DiffConfig {
            ignore_literal_order: false,
            ..DiffConfig::default()
        };
        let differ = ProofDiffer::new(config);
        let result = differ.diff(&old, &new);

        let has_clause_change = result.entries.iter().any(|e| {
            matches!(
                e,
                DiffEntry::Modified {
                    kind: DiffKind::InputClauseChanged { .. },
                    ..
                }
            )
        });
        assert!(
            has_clause_change,
            "should detect input clause change even with order-sensitive config"
        );
    }

    // -- Fingerprint value() accessor ----------------------------------------

    #[test]
    fn test_fingerprint_value_nonzero() {
        let tree = simple_tree();
        let fp = ProofFingerprint::compute(&tree, 1).unwrap();
        // FNV-1a on non-empty input should not produce zero.
        assert_ne!(
            fp.value(),
            0,
            "fingerprint value should be nonzero for non-trivial content"
        );
    }

    #[test]
    fn test_fingerprint_value_deterministic() {
        let tree = simple_tree();
        let fp1 = ProofFingerprint::compute(&tree, 2).unwrap();
        let fp2 = ProofFingerprint::compute(&tree, 2).unwrap();
        assert_eq!(
            fp1.value(),
            fp2.value(),
            "fingerprint value should be deterministic"
        );
    }

    // -- Fingerprint stability across different node IDs ---------------------

    #[test]
    fn test_fingerprint_input_clause_same_content_different_node_ids() {
        // Two trees with identical input clause content but different node IDs.
        // Fingerprints depend on content, not node ID.
        let tree1 = ProofTree::from_steps(&[(100, &[1, 2, 3])], &[]);
        let tree2 = ProofTree::from_steps(&[(200, &[1, 2, 3])], &[]);

        let fp1 = ProofFingerprint::compute(&tree1, 100).unwrap();
        let fp2 = ProofFingerprint::compute(&tree2, 200).unwrap();
        assert_eq!(
            fp1, fp2,
            "same content with different node IDs should produce same fingerprint"
        );
    }

    // -- Subtree with theory lemma nodes -------------------------------------

    #[test]
    fn test_subtree_includes_theory_lemma() {
        let mut tree = simple_tree();
        tree.add_theory_lemma(10, "EUF", &[5, -6]);
        // Add edge from resolution node 3 to theory lemma 10, simulating
        // that node 3's derivation uses the theory lemma as additional input.
        tree.edges.get_mut(&3).unwrap().push(10);

        let sub = tree.subtree(3);
        assert_eq!(sub.len(), 4, "subtree should include nodes 1, 2, 3, and 10");
        assert!(
            sub.nodes.contains_key(&10),
            "theory lemma should be in subtree"
        );
    }

    // -- DiffEntry variant node ID inspection --------------------------------

    #[test]
    fn test_diff_added_entries_contain_correct_node_ids() {
        let old = ProofTree::new();
        let new = ProofTree::from_steps(&[(1, &[10]), (2, &[-10])], &[]);

        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);

        let added_ids: HashSet<NodeId> = result
            .entries
            .iter()
            .filter_map(|e| match e {
                DiffEntry::Added { node_id } => Some(*node_id),
                _ => None,
            })
            .collect();

        assert!(added_ids.contains(&1), "node 1 should be in added set");
        assert!(added_ids.contains(&2), "node 2 should be in added set");
        assert_eq!(added_ids.len(), 2);
    }

    #[test]
    fn test_diff_removed_entries_contain_correct_node_ids() {
        let old = ProofTree::from_steps(&[(1, &[10]), (2, &[-10])], &[]);
        let new = ProofTree::new();

        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);

        let removed_ids: HashSet<NodeId> = result
            .entries
            .iter()
            .filter_map(|e| match e {
                DiffEntry::Removed { node_id } => Some(*node_id),
                _ => None,
            })
            .collect();

        assert!(removed_ids.contains(&1), "node 1 should be in removed set");
        assert!(removed_ids.contains(&2), "node 2 should be in removed set");
        assert_eq!(removed_ids.len(), 2);
    }

    // -- IncrementalCheckPlan with only removals -----------------------------

    #[test]
    fn test_incremental_plan_only_removals_is_no_op() {
        // Old tree has nodes, new tree is empty. Everything is removed, nothing
        // needs checking in the new proof.
        let old = simple_tree();
        let new = ProofTree::new();

        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let plan = result.incremental_plan();

        assert!(plan.is_no_op(), "no nodes to check in empty new proof");
        assert!(
            plan.nodes_to_skip.is_empty(),
            "no nodes to skip in empty new proof"
        );
    }

    #[test]
    fn test_incremental_plan_estimated_savings_bounds() {
        // Savings should always be in [0.0, 1.0].
        let old = simple_tree();
        let new = simple_tree();
        let differ = ProofDiffer::with_defaults();

        let result = differ.diff(&old, &new);
        let plan = result.incremental_plan();
        assert!(
            (0.0..=1.0).contains(&plan.estimated_savings),
            "savings {:.3} should be in [0,1]",
            plan.estimated_savings,
        );

        let result2 = differ.diff(&ProofTree::new(), &new);
        let plan2 = result2.incremental_plan();
        assert!(
            (0.0..=1.0).contains(&plan2.estimated_savings),
            "savings {:.3} should be in [0,1]",
            plan2.estimated_savings,
        );
    }

    // -- max_depth with deeper trees -----------------------------------------

    #[test]
    fn test_diff_max_depth_one_includes_root_and_children() {
        let old = two_step_tree();
        let mut new = two_step_tree();
        // Modify a leaf (depth 2) — should be filtered at max_depth=1.
        new.nodes.get_mut(&1).unwrap().kind = ProofNodeKind::InputClause { literals: vec![99] };

        let config = DiffConfig {
            max_depth: Some(1),
            ..DiffConfig::default()
        };
        let differ = ProofDiffer::new(config);
        let result = differ.diff(&old, &new);

        // At max_depth=1, nodes at depth 0 (root=5) and depth 1 (nodes 4 and 3)
        // should be included, but depth-2 nodes (1 and 2) should be filtered.
        let depths = ProofDiffer::compute_depths(&new);
        for entry in &result.entries {
            let nid = match entry {
                DiffEntry::Added { node_id } => *node_id,
                DiffEntry::Removed { node_id } => *node_id,
                DiffEntry::Modified { new_node_id, .. } => *new_node_id,
                DiffEntry::Unchanged { new_node_id, .. } => *new_node_id,
            };
            let d = depths.get(&nid).copied().unwrap_or(usize::MAX);
            assert!(
                d <= 1,
                "node {nid} at depth {d} should be filtered at max_depth=1"
            );
        }
    }

    #[test]
    fn test_diff_max_depth_none_includes_all() {
        let old = two_step_tree();
        let differ = ProofDiffer::with_defaults(); // max_depth=None
        let result = differ.diff(&old, &old);
        assert_eq!(
            result.summary().total,
            5,
            "without depth limit, all 5 nodes should appear"
        );
    }

    // -- structural_only mode with input clause changes ----------------------

    #[test]
    fn test_structural_only_mode_classifies_clause_change_as_structure() {
        let old = ProofTree::from_steps(&[(1, &[1, 2])], &[]);
        let new = ProofTree::from_steps(&[(1, &[1, 3])], &[]); // literal 2 -> 3

        let config = DiffConfig {
            structural_only: true,
            ..DiffConfig::default()
        };
        let differ = ProofDiffer::new(config);
        let result = differ.diff(&old, &new);

        // In structural_only mode, the change should be StructureChanged, not
        // InputClauseChanged.
        let has_structure = result.entries.iter().any(|e| {
            matches!(
                e,
                DiffEntry::Modified {
                    kind: DiffKind::StructureChanged,
                    ..
                }
            )
        });
        let has_clause = result.entries.iter().any(|e| {
            matches!(
                e,
                DiffEntry::Modified {
                    kind: DiffKind::InputClauseChanged { .. },
                    ..
                }
            )
        });
        assert!(
            has_structure,
            "structural_only mode should use StructureChanged"
        );
        assert!(
            !has_clause,
            "structural_only mode should not use InputClauseChanged"
        );
    }

    // -- DiffSummary zero-total edge cases -----------------------------------

    #[test]
    fn test_summary_added_fraction_zero_total() {
        let summary = DiffSummary {
            added: 0,
            removed: 0,
            modified: 0,
            unchanged: 0,
            total: 0,
        };
        assert!((summary.added_fraction() - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_summary_removed_fraction_zero_total() {
        let summary = DiffSummary {
            added: 0,
            removed: 0,
            modified: 0,
            unchanged: 0,
            total: 0,
        };
        assert!((summary.removed_fraction() - 0.0).abs() < f64::EPSILON);
    }

    // -- Large tree with modifications (not just self-diff) ------------------

    #[test]
    fn test_diff_large_tree_with_modifications() {
        // Build a chain of 50 resolution steps.
        let mut inputs: Vec<(NodeId, Vec<LiteralId>)> = Vec::new();
        for i in 1..=50 {
            inputs.push((i, vec![i as LiteralId, -(i as LiteralId + 100)]));
        }
        let input_refs: Vec<(NodeId, &[LiteralId])> = inputs
            .iter()
            .map(|(id, lits)| (*id, lits.as_slice()))
            .collect();

        let mut steps = Vec::new();
        let mut current = 1u64;
        for (next_id, i) in (51u64..).zip(2..=50u64) {
            steps.push((next_id, current, i, i as LiteralId));
            current = next_id;
        }

        let old = ProofTree::from_steps(&input_refs, &steps);
        assert_eq!(old.len(), 99); // 50 inputs + 49 steps

        // Build a modified version: change the first input clause's literals.
        let mut mod_inputs = inputs.clone();
        mod_inputs[0].1 = vec![999, -999];
        let mod_input_refs: Vec<(NodeId, &[LiteralId])> = mod_inputs
            .iter()
            .map(|(id, lits)| (*id, lits.as_slice()))
            .collect();
        let new = ProofTree::from_steps(&mod_input_refs, &steps);

        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let summary = result.summary();

        assert_eq!(summary.total, 99);
        // At least node 1 should be modified; many ancestors along the chain
        // will also differ in fingerprint.
        assert!(summary.modified >= 1, "at least node 1 should be modified");
        assert!(
            summary.unchanged >= 1,
            "nodes far from the change should be unchanged"
        );
        assert!(
            summary.unchanged + summary.modified + summary.added + summary.removed == 99,
            "all 99 nodes should be accounted for"
        );
    }

    // -- ProofEvolution: multi-version non-monotonic similarity ---------------

    #[test]
    fn test_evolution_similarity_trend_non_monotonic() {
        let mut evo = ProofEvolution::new();

        // v1: simple tree
        evo.add_version("v1", simple_tree());
        // v2: completely different tree (low similarity to v1)
        evo.add_version(
            "v2",
            ProofTree::from_steps(&[(100, &[50, 60]), (101, &[-50, 70])], &[]),
        );
        // v3: back to simple tree (high similarity to v2's successor, which
        // is actually a return to v1)
        evo.add_version("v3", simple_tree());

        let trend = evo.similarity_trend();
        assert_eq!(trend.len(), 3);
        assert!((trend[0].1 - 1.0).abs() < f64::EPSILON, "v1 is always 1.0");
        // v2 vs v1 should have low similarity.
        assert!(trend[1].1 < 0.8, "v2 should differ significantly from v1");
        // v3 vs v2 should also have low similarity (different trees).
        assert!(trend[2].1 < 0.8, "v3 should differ significantly from v2");
    }

    #[test]
    fn test_evolution_many_identical_versions() {
        let mut evo = ProofEvolution::new();
        for i in 0..10 {
            evo.add_version(&format!("v{i}"), simple_tree());
        }
        assert_eq!(evo.version_count(), 10);

        let trend = evo.similarity_trend();
        assert_eq!(trend.len(), 10);
        for (_, sim) in &trend {
            assert!(
                (*sim - 1.0).abs() < f64::EPSILON,
                "all identical versions should have similarity 1.0"
            );
        }
    }

    // -- ProofEvolution: version accessor edge case --------------------------

    #[test]
    fn test_evolution_version_returns_correct_tree() {
        let mut evo = ProofEvolution::new();
        evo.add_version("simple", simple_tree());
        evo.add_version("two_step", two_step_tree());

        let (label, tree) = evo.version(0).unwrap();
        assert_eq!(label, "simple");
        assert_eq!(tree.len(), 3);

        let (label, tree) = evo.version(1).unwrap();
        assert_eq!(label, "two_step");
        assert_eq!(tree.len(), 5);
    }

    // -- Shared subproofs with theory lemmas ---------------------------------

    #[test]
    fn test_shared_subproofs_with_identical_theory_lemma() {
        let mut old = simple_tree();
        old.add_theory_lemma(10, "EUF", &[5, -6]);

        let mut new = simple_tree();
        new.add_theory_lemma(10, "EUF", &[5, -6]);

        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let shared = result.shared_subproofs();

        // All 4 nodes (3 base + 1 theory lemma) should be shared.
        assert_eq!(
            shared.len(),
            4,
            "all nodes including theory lemma should be shared"
        );
    }

    #[test]
    fn test_shared_subproofs_theory_lemma_differs() {
        let mut old = simple_tree();
        old.add_theory_lemma(10, "EUF", &[5, -6]);

        let mut new = simple_tree();
        new.add_theory_lemma(10, "LRA", &[5, -6]); // different theory

        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let shared = result.shared_subproofs();

        // The 3 base nodes are shared, but the theory lemma differs.
        assert_eq!(shared.len(), 3, "only the 3 base nodes should be shared");
    }

    // -- Diff symmetry: swapping old and new ---------------------------------

    #[test]
    fn test_diff_swap_added_becomes_removed() {
        let a = ProofTree::from_steps(&[(1, &[1, 2])], &[]);
        let b = ProofTree::from_steps(&[(1, &[1, 2]), (2, &[-1])], &[]);

        let differ = ProofDiffer::with_defaults();
        let forward = differ.diff(&a, &b);
        let backward = differ.diff(&b, &a);

        assert_eq!(forward.summary().added, backward.summary().removed);
        assert_eq!(forward.summary().removed, backward.summary().added);
        assert_eq!(forward.summary().unchanged, backward.summary().unchanged);
    }

    // -- ProofTree from_steps edge: no inputs, only resolution ---------------

    #[test]
    fn test_proof_tree_from_steps_resolution_only() {
        // Resolution steps referencing non-existent parents.
        // This is structurally allowed (no panic) even if semantically odd.
        let tree = ProofTree::from_steps(&[], &[(10, 1, 2, 1)]);
        assert_eq!(
            tree.len(),
            1,
            "only the resolution node itself should exist"
        );
        assert_eq!(tree.root, Some(10));
        // Edges should reference non-existent nodes 1 and 2.
        let edges = tree.edges.get(&10).unwrap();
        assert_eq!(edges, &[1, 2]);
    }

    // -- ProofTree: multiple add_theory_lemma calls --------------------------

    #[test]
    fn test_proof_tree_multiple_theory_lemmas() {
        let mut tree = ProofTree::new();
        tree.add_theory_lemma(1, "EUF", &[1, -2]);
        tree.add_theory_lemma(2, "LRA", &[3, -4]);
        tree.add_theory_lemma(3, "BV", &[5, -6]);
        assert_eq!(tree.len(), 3);

        // Verify each node has the correct theory name.
        for (id, expected_theory) in [(1, "EUF"), (2, "LRA"), (3, "BV")] {
            let node = &tree.nodes[&id];
            match &node.kind {
                ProofNodeKind::TheoryLemma { theory, .. } => {
                    assert_eq!(theory, expected_theory);
                }
                other => panic!("expected TheoryLemma, got {other:?}"),
            }
        }
    }

    // -- Fingerprint: empty clause -------------------------------------------

    #[test]
    fn test_fingerprint_empty_clause() {
        let tree = ProofTree::from_steps(&[(1, &[])], &[]);
        let fp = ProofFingerprint::compute(&tree, 1).unwrap();
        // Empty clause should still produce a valid fingerprint.
        assert_ne!(fp.value(), 0);
    }

    #[test]
    fn test_fingerprint_empty_clause_differs_from_nonempty() {
        let tree1 = ProofTree::from_steps(&[(1, &[])], &[]);
        let tree2 = ProofTree::from_steps(&[(1, &[42])], &[]);
        let fp1 = ProofFingerprint::compute(&tree1, 1).unwrap();
        let fp2 = ProofFingerprint::compute(&tree2, 1).unwrap();
        assert_ne!(fp1, fp2, "empty clause should differ from non-empty clause");
    }

    // -- Diff: completely disjoint large trees --------------------------------

    #[test]
    fn test_diff_completely_disjoint_trees() {
        // Two trees with entirely different node IDs and content.
        let old = ProofTree::from_steps(&[(1, &[1, 2]), (2, &[-1, 3])], &[(3, 1, 2, 1)]);
        let new = ProofTree::from_steps(
            &[(100, &[50, 60]), (101, &[-50, 70])],
            &[(102, 100, 101, 50)],
        );

        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let summary = result.summary();

        assert_eq!(summary.unchanged, 0, "no nodes should match");
        // The differ pairs by kind: old has 2 InputClause + 1 Resolution,
        // new has 2 InputClause + 1 Resolution. They should pair as modified.
        assert_eq!(
            summary.total,
            summary.added + summary.removed + summary.modified
        );
    }

    // -- Diff: resolution step same pivot, different children fingerprint -----

    #[test]
    fn test_diff_same_pivot_different_children() {
        // Same pivot (1) but different children content.
        let old = ProofTree::from_steps(&[(1, &[1, 2]), (2, &[-1, 3])], &[(3, 1, 2, 1)]);
        let new = ProofTree::from_steps(
            &[(1, &[1, 99]), (2, &[-1, 88])],
            &[(3, 1, 2, 1)], // same pivot
        );

        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);

        // The input clauses differ → resolution fingerprint differs.
        // Since the resolution nodes share the same pivot, classify_change
        // will return StructureChanged (same pivot but fingerprint mismatch
        // lands them in the unmatched pool).
        let summary = result.summary();
        assert!(
            summary.modified >= 1,
            "at least some nodes should be modified"
        );
    }

    // -- DiffSummary: Display with all zeros ---------------------------------

    #[test]
    fn test_summary_display_all_zeros() {
        let summary = DiffSummary {
            added: 0,
            removed: 0,
            modified: 0,
            unchanged: 0,
            total: 0,
        };
        let s = format!("{summary}");
        // structural_similarity returns 1.0 for empty, so display should show 100.0%.
        assert!(
            s.contains("similarity=100.0%"),
            "empty summary should show 100%% similarity, got '{s}'"
        );
    }

    // -- IncrementalCheckPlan: empty diff produces empty plan -----------------

    #[test]
    fn test_incremental_plan_empty_diff() {
        let result = DiffResult {
            entries: Vec::new(),
            matched_nodes: HashMap::new(),
        };
        let plan = result.incremental_plan();
        assert!(plan.is_no_op());
        assert!(plan.is_full_recheck()); // no nodes to skip either
        assert!((plan.estimated_savings - 0.0).abs() < f64::EPSILON);
    }

    // -- DiffResult: summary total consistency --------------------------------

    #[test]
    fn test_summary_total_equals_sum_of_parts() {
        let old = two_step_tree();
        let mut new = two_step_tree();
        new.add_theory_lemma(10, "EUF", &[5, -6]);
        new.nodes.get_mut(&1).unwrap().kind = ProofNodeKind::InputClause { literals: vec![77] };

        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&old, &new);
        let s = result.summary();

        assert_eq!(
            s.total,
            s.added + s.removed + s.modified + s.unchanged,
            "total should be sum of added+removed+modified+unchanged"
        );
    }

    // -- Shared subproofs: no duplicates -------------------------------------

    #[test]
    fn test_shared_subproofs_no_duplicates() {
        let tree = two_step_tree();
        let differ = ProofDiffer::with_defaults();
        let result = differ.diff(&tree, &tree);
        let shared = result.shared_subproofs();

        // Each shared subproof should be unique.
        let mut seen = HashSet::new();
        for sp in &shared {
            assert!(
                seen.insert((sp.old_root, sp.new_root)),
                "duplicate shared subproof ({}, {})",
                sp.old_root,
                sp.new_root,
            );
        }
    }

    // -- ProofTree: from_steps root is last resolution step ------------------

    #[test]
    fn test_from_steps_root_is_last_resolution() {
        let tree = ProofTree::from_steps(
            &[(1, &[1]), (2, &[-1]), (3, &[2])],
            &[(10, 1, 2, 1), (20, 10, 3, 2)],
        );
        assert_eq!(
            tree.root,
            Some(20),
            "root should be the last resolution step"
        );
    }

    // -- FnvHasher: exercise through fingerprint collisions check ------------

    #[test]
    fn test_fingerprint_no_trivial_collisions() {
        // 20 distinct single-literal input clauses should all produce
        // distinct fingerprints.
        let mut fps = HashSet::new();
        for lit in 1..=20i64 {
            let tree = ProofTree::from_steps(&[(1, &[lit])], &[]);
            let fp = ProofFingerprint::compute(&tree, 1).unwrap();
            fps.insert(fp.value());
        }
        assert_eq!(
            fps.len(),
            20,
            "20 distinct clauses should produce 20 distinct fingerprints"
        );
    }

    // -- ProofEvolution: changes_between reversed order ----------------------

    #[test]
    fn test_evolution_changes_between_reversed() {
        let mut evo = ProofEvolution::new();
        evo.add_version("v1", simple_tree());
        evo.add_version("v2", two_step_tree());

        let forward = evo.changes_between(0, 1).unwrap();
        let backward = evo.changes_between(1, 0).unwrap();

        // Swapping old and new should swap added/removed.
        assert_eq!(forward.summary().added, backward.summary().removed);
        assert_eq!(forward.summary().removed, backward.summary().added);
    }

    // -- Compute depths: correctness check -----------------------------------

    #[test]
    fn test_compute_depths_two_step_tree() {
        let tree = two_step_tree();
        let depths = ProofDiffer::compute_depths(&tree);

        // Root is node 5 at depth 0.
        assert_eq!(depths[&5], 0);
        // Node 4 and node 3 are children of 5, at depth 1.
        assert_eq!(depths[&4], 1);
        assert_eq!(depths[&3], 1);
        // Nodes 1 and 2 are children of 4, at depth 2.
        assert_eq!(depths[&1], 2);
        assert_eq!(depths[&2], 2);
    }

    #[test]
    fn test_compute_depths_empty_tree() {
        let tree = ProofTree::new();
        let depths = ProofDiffer::compute_depths(&tree);
        assert!(depths.is_empty());
    }

    #[test]
    fn test_compute_depths_single_node() {
        let tree = ProofTree::from_steps(&[(1, &[42])], &[]);
        let depths = ProofDiffer::compute_depths(&tree);
        assert_eq!(depths.len(), 1);
        assert_eq!(depths[&1], 0);
    }
}
