// assumption_tracker.rs — Assumption dependency tracker for the verification engine.
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates Apache 2.0

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt::{self, Write as _};

// ---------------------------------------------------------------------------
// Identifiers
// ---------------------------------------------------------------------------

/// Unique identifier for an assumption.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AssumptionId(pub String);

impl fmt::Display for AssumptionId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// Unique identifier for a proof obligation.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ObligationId(pub String);

impl fmt::Display for ObligationId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// An assumption in the verification context.
#[derive(Debug, Clone)]
pub struct Assumption {
    pub id: AssumptionId,
    pub label: String,
    pub expression: String,
    pub source: AssumptionSource,
    pub is_trusted: bool,
}

impl Assumption {
    /// Builds a cited fact: an explicitly *trusted* assumption with provenance.
    ///
    /// Mirrors the `Axiom` trust path — the fact is recorded as trusted
    /// (`is_trusted = true`) under [`AssumptionSource::Cite`] carrying the
    /// optional citation `reference`. SOUNDNESS: the cited fact is *assumed*,
    /// so it is surfaced as part of the trust surface and never licenses an
    /// obligation to be reported as proven.
    #[must_use]
    pub fn cite(
        id: AssumptionId,
        label: impl Into<String>,
        expression: impl Into<String>,
        reference: Option<String>,
    ) -> Self {
        Self {
            id,
            label: label.into(),
            expression: expression.into(),
            source: AssumptionSource::Cite { reference },
            is_trusted: true,
        }
    }
}

/// Where the assumption originated.
#[derive(Debug, Clone, PartialEq)]
pub enum AssumptionSource {
    Requires,
    Invariant,
    Broadcast,
    Axiom,
    InductionHypothesis,
    UserAssume,
    /// A cited fact: an explicitly *trusted* assumption with provenance.
    ///
    /// Semantically identical to [`AssumptionSource::Axiom`] (an assumed,
    /// trust-tainted fact) but annotated with a citation reference — a string
    /// and/or a path to an external proof, lemma, or source. The `reference`
    /// is the provenance; `None` means the citation reference was omitted.
    ///
    /// SOUNDNESS: a `Cite` fact is *assumed*, never *proven*. It is treated as
    /// trusted everywhere [`AssumptionSource::Axiom`] is (see
    /// [`AssumptionSource::is_trusted_source`]).
    Cite {
        reference: Option<String>,
    },
}

impl AssumptionSource {
    /// Whether this source introduces an *explicitly trusted* fact into the
    /// assumption base — the cited/axiomatic trust surface.
    ///
    /// `Cite` is trusted exactly like `Axiom`: any obligation relying on such a
    /// fact is trust-tainted and must never be reported as proven on that basis.
    #[must_use]
    pub fn is_trusted_source(&self) -> bool {
        matches!(
            self,
            AssumptionSource::Axiom | AssumptionSource::Cite { .. }
        )
    }
}

/// A proof obligation that may depend on assumptions.
#[derive(Debug, Clone)]
pub struct Obligation {
    pub id: ObligationId,
    pub label: String,
    pub expression: String,
}

/// Records which assumptions a particular obligation used and whether it verified.
#[derive(Debug, Clone)]
pub struct UsageDependency {
    pub obligation: ObligationId,
    pub assumptions_used: HashSet<AssumptionId>,
    pub is_verified: bool,
}

// ---------------------------------------------------------------------------
// Analysis results
// ---------------------------------------------------------------------------

/// Full analysis produced by [`AssumptionTracker::analyze`].
#[derive(Debug, Clone)]
pub struct AssumptionAnalysis {
    pub unused_assumptions: Vec<AssumptionId>,
    pub critical_assumptions: Vec<AssumptionId>,
    pub assumption_usage_count: HashMap<AssumptionId, usize>,
    pub minimal_assumption_sets: Vec<HashSet<AssumptionId>>,
    pub circular_dependencies: Vec<Vec<AssumptionId>>,
    pub trusted_assumption_count: usize,
    pub trust_ratio: f64,
}

/// Coarse classification of how important an assumption is.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum AssumptionStrength {
    Trivial,
    Weak,
    Moderate,
    Strong,
    Critical,
}

// ---------------------------------------------------------------------------
// MinimalSetFinder — greedy set-cover helper
// ---------------------------------------------------------------------------

/// Finds minimal assumption sets that cover all obligations.
pub struct MinimalSetFinder {
    universe: HashSet<ObligationId>,
    assumption_covers: HashMap<AssumptionId, HashSet<ObligationId>>,
}

impl MinimalSetFinder {
    /// Create a new finder from the full obligation universe and a map of
    /// which obligations each assumption covers.
    pub fn new(
        universe: HashSet<ObligationId>,
        assumption_covers: HashMap<AssumptionId, HashSet<ObligationId>>,
    ) -> Self {
        Self {
            universe,
            assumption_covers,
        }
    }

    /// Greedy set-cover: repeatedly pick the assumption that covers the most
    /// uncovered obligations until everything is covered (or no progress).
    #[must_use]
    pub fn find_greedy(&self) -> HashSet<AssumptionId> {
        let mut uncovered: HashSet<ObligationId> = self.universe.clone();
        let mut selected: HashSet<AssumptionId> = HashSet::new();

        while !uncovered.is_empty() {
            // Find assumption covering the most uncovered obligations.
            let best = self
                .assumption_covers
                .iter()
                .filter(|(aid, _)| !selected.contains(aid))
                .max_by_key(|(_, cover)| cover.intersection(&uncovered).count());

            match best {
                Some((aid, cover)) => {
                    let covered_now: HashSet<_> = cover.intersection(&uncovered).cloned().collect();
                    if covered_now.is_empty() {
                        break; // no progress
                    }
                    for o in &covered_now {
                        uncovered.remove(o);
                    }
                    selected.insert(aid.clone());
                }
                None => break,
            }
        }
        selected
    }

    /// Enumerate all minimal covers up to `max_solutions` via DFS with
    /// pruning. A cover is minimal if removing any single element leaves
    /// at least one obligation uncovered.
    #[must_use]
    pub fn find_all_minimal(&self, max_solutions: usize) -> Vec<HashSet<AssumptionId>> {
        let mut results: Vec<HashSet<AssumptionId>> = Vec::new();
        let aids: Vec<AssumptionId> = self.assumption_covers.keys().cloned().collect();

        self.enumerate_covers(
            &aids,
            0,
            &HashSet::new(),
            &self.universe,
            max_solutions,
            &mut results,
        );
        results
    }

    fn enumerate_covers(
        &self,
        aids: &[AssumptionId],
        start: usize,
        current: &HashSet<AssumptionId>,
        remaining: &HashSet<ObligationId>,
        max: usize,
        results: &mut Vec<HashSet<AssumptionId>>,
    ) {
        if results.len() >= max {
            return;
        }
        if remaining.is_empty() {
            // Check minimality: every element in `current` must be needed.
            for a in current {
                let cover = self.assumption_covers.get(a).cloned().unwrap_or_default();
                // If every obligation covered by `a` is also covered by some other selected assumption, `a` is redundant.
                let dominated = cover.iter().all(|o| {
                    if !self.universe.contains(o) {
                        return true;
                    }
                    current.iter().any(|other| {
                        other != a
                            && self
                                .assumption_covers
                                .get(other)
                                .is_some_and(|oc| oc.contains(o))
                    })
                });
                if dominated {
                    return; // not minimal
                }
            }
            results.push(current.clone());
            return;
        }
        for i in start..aids.len() {
            if results.len() >= max {
                return;
            }
            let aid = &aids[i];
            let cover = self.assumption_covers.get(aid).cloned().unwrap_or_default();
            let new_remaining: HashSet<_> = remaining.difference(&cover).cloned().collect();
            let mut next = current.clone();
            next.insert(aid.clone());
            self.enumerate_covers(aids, i + 1, &next, &new_remaining, max, results);
        }
    }
}

// ---------------------------------------------------------------------------
// AssumptionTracker
// ---------------------------------------------------------------------------

/// Tracks assumptions, obligations, and their dependencies.
pub struct AssumptionTracker {
    assumptions: BTreeMap<AssumptionId, Assumption>,
    obligations: BTreeMap<ObligationId, Obligation>,
    dependencies: Vec<UsageDependency>,
    /// Assumption-to-assumption dependency: `from` depends on `to`.
    assumption_deps: HashMap<AssumptionId, HashSet<AssumptionId>>,
}

impl AssumptionTracker {
    /// Create an empty tracker.
    #[must_use]
    pub fn new() -> Self {
        Self {
            assumptions: BTreeMap::new(),
            obligations: BTreeMap::new(),
            dependencies: Vec::new(),
            assumption_deps: HashMap::new(),
        }
    }

    /// Register an assumption.
    pub fn add_assumption(&mut self, assumption: Assumption) {
        self.assumptions.insert(assumption.id.clone(), assumption);
    }

    /// Register a proof obligation.
    pub fn add_obligation(&mut self, obligation: Obligation) {
        self.obligations.insert(obligation.id.clone(), obligation);
    }

    /// Record that `obligation_id` used `assumption_ids` and whether it verified.
    pub fn record_usage(
        &mut self,
        obligation_id: ObligationId,
        assumption_ids: HashSet<AssumptionId>,
        verified: bool,
    ) {
        self.dependencies.push(UsageDependency {
            obligation: obligation_id,
            assumptions_used: assumption_ids,
            is_verified: verified,
        });
    }

    /// Declare that assumption `from` depends on assumption `to`.
    pub fn add_assumption_dependency(&mut self, from: AssumptionId, to: AssumptionId) {
        self.assumption_deps.entry(from).or_default().insert(to);
    }

    // -- Queries -----------------------------------------------------------

    /// Assumptions that are not referenced by any obligation.
    #[must_use]
    pub fn unused_assumptions(&self) -> Vec<&AssumptionId> {
        let used: HashSet<&AssumptionId> = self
            .dependencies
            .iter()
            .flat_map(|d| d.assumptions_used.iter())
            .collect();
        self.assumptions
            .keys()
            .filter(|aid| !used.contains(aid))
            .collect()
    }

    /// Assumptions that appear in *every* obligation's dependency set.
    #[must_use]
    pub fn critical_assumptions(&self) -> Vec<&AssumptionId> {
        if self.dependencies.is_empty() {
            return Vec::new();
        }

        // Gather the unique obligations that have dependencies recorded.
        let obligation_sets: Vec<&HashSet<AssumptionId>> = self
            .dependencies
            .iter()
            .map(|d| &d.assumptions_used)
            .collect();

        // An assumption is critical if it appears in *every* dependency record.
        self.assumptions
            .keys()
            .filter(|aid| obligation_sets.iter().all(|s| s.contains(aid)))
            .collect()
    }

    /// Classify assumption strength based on usage ratio across obligations.
    #[must_use]
    pub fn classify_strength(&self, id: &AssumptionId) -> AssumptionStrength {
        if self.dependencies.is_empty() || !self.assumptions.contains_key(id) {
            return AssumptionStrength::Trivial;
        }

        let total = self.dependencies.len();
        let count = self
            .dependencies
            .iter()
            .filter(|d| d.assumptions_used.contains(id))
            .count();

        let ratio = count as f64 / total as f64;
        if ratio <= 0.0 {
            AssumptionStrength::Trivial
        } else if ratio < 0.25 {
            AssumptionStrength::Weak
        } else if ratio < 0.5 {
            AssumptionStrength::Moderate
        } else if ratio < 1.0 {
            AssumptionStrength::Strong
        } else {
            AssumptionStrength::Critical
        }
    }

    /// Detect cycles in the assumption-to-assumption dependency graph.
    /// Returns each cycle as a path of assumption IDs.
    #[must_use]
    pub fn detect_circular_dependencies(&self) -> Vec<Vec<AssumptionId>> {
        // Tarjan's SCC — cycles are SCCs of size > 1.
        let mut tarjan = TarjanState {
            index_counter: 0,
            stack: Vec::new(),
            on_stack: HashSet::new(),
            indices: HashMap::new(),
            lowlinks: HashMap::new(),
            sccs: Vec::new(),
        };

        // Collect all nodes present in the dep graph (both sides).
        let mut all_nodes: BTreeSet<AssumptionId> = BTreeSet::new();
        for (from, tos) in &self.assumption_deps {
            all_nodes.insert(from.clone());
            for to in tos {
                all_nodes.insert(to.clone());
            }
        }

        struct TarjanState {
            index_counter: usize,
            stack: Vec<AssumptionId>,
            on_stack: HashSet<AssumptionId>,
            indices: HashMap<AssumptionId, usize>,
            lowlinks: HashMap<AssumptionId, usize>,
            sccs: Vec<Vec<AssumptionId>>,
        }

        fn strongconnect(
            v: &AssumptionId,
            deps: &HashMap<AssumptionId, HashSet<AssumptionId>>,
            st: &mut TarjanState,
        ) {
            st.indices.insert(v.clone(), st.index_counter);
            st.lowlinks.insert(v.clone(), st.index_counter);
            st.index_counter += 1;
            st.stack.push(v.clone());
            st.on_stack.insert(v.clone());

            if let Some(neighbors) = deps.get(v) {
                for w in neighbors {
                    if !st.indices.contains_key(w) {
                        strongconnect(w, deps, st);
                        if let (Some(lw), Some(lv)) =
                            (st.lowlinks.get(w).copied(), st.lowlinks.get_mut(v))
                        {
                            if lw < *lv {
                                *lv = lw;
                            }
                        }
                    } else if st.on_stack.contains(w) {
                        if let (Some(iw), Some(lv)) =
                            (st.indices.get(w).copied(), st.lowlinks.get_mut(v))
                        {
                            if iw < *lv {
                                *lv = iw;
                            }
                        }
                    }
                }
            }

            let is_root = st.lowlinks.get(v) == st.indices.get(v);
            if is_root {
                let mut scc = Vec::new();
                while let Some(w) = st.stack.pop() {
                    st.on_stack.remove(&w);
                    scc.push(w.clone());
                    if w == *v {
                        break;
                    }
                }
                if scc.len() > 1 {
                    scc.sort();
                    st.sccs.push(scc);
                }
            }
        }

        for node in &all_nodes {
            if !tarjan.indices.contains_key(node) {
                strongconnect(node, &self.assumption_deps, &mut tarjan);
            }
        }

        tarjan.sccs
    }

    /// Compute transitive closure of assumption dependencies for a single root.
    #[must_use]
    pub fn transitive_closure(&self, assumption_id: &AssumptionId) -> HashSet<AssumptionId> {
        let mut visited: HashSet<AssumptionId> = HashSet::new();
        let mut queue: VecDeque<AssumptionId> = VecDeque::new();

        if let Some(direct) = self.assumption_deps.get(assumption_id) {
            for d in direct {
                queue.push_back(d.clone());
            }
        }

        while let Some(current) = queue.pop_front() {
            if visited.insert(current.clone()) {
                if let Some(next) = self.assumption_deps.get(&current) {
                    for n in next {
                        if !visited.contains(n) {
                            queue.push_back(n.clone());
                        }
                    }
                }
            }
        }
        visited
    }

    /// `(trusted_count, total_count, ratio)`.
    #[must_use]
    pub fn trust_audit(&self) -> (usize, usize, f64) {
        let total = self.assumptions.len();
        let trusted = self.assumptions.values().filter(|a| a.is_trusted).count();
        let ratio = if total == 0 {
            0.0
        } else {
            trusted as f64 / total as f64
        };
        (trusted, total, ratio)
    }

    /// Which assumptions does a given obligation depend on?
    #[must_use]
    pub fn obligation_assumptions(&self, id: &ObligationId) -> Option<HashSet<AssumptionId>> {
        // Merge all dependency records for this obligation.
        let mut merged: Option<HashSet<AssumptionId>> = None;
        for dep in &self.dependencies {
            if dep.obligation == *id {
                match &mut merged {
                    Some(s) => {
                        s.extend(dep.assumptions_used.iter().cloned());
                    }
                    None => {
                        merged = Some(dep.assumptions_used.clone());
                    }
                }
            }
        }
        merged
    }

    /// Reverse lookup: which obligations use a given assumption?
    #[must_use]
    pub fn assumption_obligations(&self, id: &AssumptionId) -> HashSet<&ObligationId> {
        self.dependencies
            .iter()
            .filter(|d| d.assumptions_used.contains(id))
            .map(|d| &d.obligation)
            .collect()
    }

    /// Full analysis: unused, critical, usage counts, minimal sets, cycles, trust.
    #[must_use]
    pub fn analyze(&self) -> AssumptionAnalysis {
        let unused: Vec<AssumptionId> = self.unused_assumptions().into_iter().cloned().collect();
        let critical: Vec<AssumptionId> =
            self.critical_assumptions().into_iter().cloned().collect();

        // Usage counts
        let mut usage_count: HashMap<AssumptionId, usize> = HashMap::new();
        for aid in self.assumptions.keys() {
            usage_count.insert(aid.clone(), 0);
        }
        for dep in &self.dependencies {
            for aid in &dep.assumptions_used {
                *usage_count.entry(aid.clone()).or_default() += 1;
            }
        }

        // Minimal assumption sets via greedy set-cover
        let universe: HashSet<ObligationId> = self.obligations.keys().cloned().collect();
        let mut covers: HashMap<AssumptionId, HashSet<ObligationId>> = HashMap::new();
        for dep in &self.dependencies {
            for aid in &dep.assumptions_used {
                covers
                    .entry(aid.clone())
                    .or_default()
                    .insert(dep.obligation.clone());
            }
        }
        let finder = MinimalSetFinder::new(universe, covers);
        let greedy = finder.find_greedy();
        let all_minimal = finder.find_all_minimal(10);
        let minimal_sets = if all_minimal.is_empty() && !greedy.is_empty() {
            vec![greedy]
        } else {
            all_minimal
        };

        let circular = self.detect_circular_dependencies();
        let (trusted, _total, ratio) = self.trust_audit();

        AssumptionAnalysis {
            unused_assumptions: unused,
            critical_assumptions: critical,
            assumption_usage_count: usage_count,
            minimal_assumption_sets: minimal_sets,
            circular_dependencies: circular,
            trusted_assumption_count: trusted,
            trust_ratio: ratio,
        }
    }

    /// Render the dependency graph as a GraphViz DOT string.
    #[must_use]
    pub fn dependency_graph_dot(&self) -> String {
        let mut dot = String::from("digraph assumption_deps {\n");
        dot.push_str("  rankdir=LR;\n");
        dot.push_str("  node [shape=box];\n");

        // Assumption nodes
        for (aid, a) in &self.assumptions {
            let color = if a.is_trusted { "red" } else { "black" };
            let _ = writeln!(
                dot,
                "  \"{}\" [label=\"{}\", color={}];",
                aid.0, a.label, color
            );
        }

        // Obligation nodes
        for (oid, o) in &self.obligations {
            let _ = writeln!(
                dot,
                "  \"{}\" [label=\"{}\", shape=ellipse];",
                oid.0, o.label
            );
        }

        // Obligation -> Assumption edges
        for dep in &self.dependencies {
            let style = if dep.is_verified { "solid" } else { "dashed" };
            for aid in &dep.assumptions_used {
                let _ = writeln!(
                    dot,
                    "  \"{}\" -> \"{}\" [style={}];",
                    dep.obligation.0, aid.0, style
                );
            }
        }

        // Assumption -> Assumption edges
        for (from, tos) in &self.assumption_deps {
            for to in tos {
                let _ = writeln!(
                    dot,
                    "  \"{}\" -> \"{}\" [style=dotted, color=blue];",
                    from.0, to.0
                );
            }
        }

        dot.push_str("}\n");
        dot
    }
}

impl Default for AssumptionTracker {
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

    // -- helpers -----------------------------------------------------------

    fn aid(s: &str) -> AssumptionId {
        AssumptionId(s.to_string())
    }

    fn oid(s: &str) -> ObligationId {
        ObligationId(s.to_string())
    }

    fn make_assumption(name: &str, source: AssumptionSource, trusted: bool) -> Assumption {
        Assumption {
            id: aid(name),
            label: name.to_string(),
            expression: format!("expr_{name}"),
            source,
            is_trusted: trusted,
        }
    }

    fn make_obligation(name: &str) -> Obligation {
        Obligation {
            id: oid(name),
            label: name.to_string(),
            expression: format!("expr_{name}"),
        }
    }

    // -- 1. empty tracker -------------------------------------------------

    #[test]
    fn test_empty_tracker_analysis() {
        let tracker = AssumptionTracker::new();
        let analysis = tracker.analyze();
        assert!(analysis.unused_assumptions.is_empty());
        assert!(analysis.critical_assumptions.is_empty());
        assert!(analysis.circular_dependencies.is_empty());
        assert_eq!(analysis.trusted_assumption_count, 0);
        assert_eq!(analysis.trust_ratio, 0.0);
    }

    #[test]
    fn test_empty_tracker_unused() {
        let tracker = AssumptionTracker::new();
        assert!(tracker.unused_assumptions().is_empty());
    }

    #[test]
    fn test_empty_tracker_critical() {
        let tracker = AssumptionTracker::new();
        assert!(tracker.critical_assumptions().is_empty());
    }

    // -- 2. single assumption, single obligation --------------------------

    #[test]
    fn test_single_assumption_single_obligation() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a1", AssumptionSource::Requires, false));
        t.add_obligation(make_obligation("o1"));
        t.record_usage(oid("o1"), [aid("a1")].into_iter().collect(), true);

        assert!(t.unused_assumptions().is_empty());
        assert_eq!(t.critical_assumptions(), vec![&aid("a1")]);
    }

    // -- 3. unused assumption detection -----------------------------------

    #[test]
    fn test_unused_assumption_detection() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a1", AssumptionSource::Requires, false));
        t.add_assumption(make_assumption("a2", AssumptionSource::Axiom, false));
        t.add_obligation(make_obligation("o1"));
        t.record_usage(oid("o1"), [aid("a1")].into_iter().collect(), true);

        let unused = t.unused_assumptions();
        assert_eq!(unused.len(), 1);
        assert_eq!(unused[0], &aid("a2"));
    }

    // -- 4. critical assumption identification ----------------------------

    #[test]
    fn test_critical_across_multiple_obligations() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a1", AssumptionSource::Axiom, false));
        t.add_assumption(make_assumption("a2", AssumptionSource::Requires, false));
        t.add_obligation(make_obligation("o1"));
        t.add_obligation(make_obligation("o2"));
        t.record_usage(
            oid("o1"),
            [aid("a1"), aid("a2")].into_iter().collect(),
            true,
        );
        t.record_usage(oid("o2"), [aid("a1")].into_iter().collect(), true);

        let crit = t.critical_assumptions();
        assert_eq!(crit.len(), 1);
        assert_eq!(crit[0], &aid("a1"));
    }

    // -- 5. circular dependency detection (A->B->C->A) --------------------

    #[test]
    fn test_circular_dependency_abc() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a", AssumptionSource::Axiom, false));
        t.add_assumption(make_assumption("b", AssumptionSource::Axiom, false));
        t.add_assumption(make_assumption("c", AssumptionSource::Axiom, false));
        t.add_assumption_dependency(aid("a"), aid("b"));
        t.add_assumption_dependency(aid("b"), aid("c"));
        t.add_assumption_dependency(aid("c"), aid("a"));

        let cycles = t.detect_circular_dependencies();
        assert_eq!(cycles.len(), 1);
        let cycle = &cycles[0];
        assert_eq!(cycle.len(), 3);
        assert!(cycle.contains(&aid("a")));
        assert!(cycle.contains(&aid("b")));
        assert!(cycle.contains(&aid("c")));
    }

    // -- 6. no circular deps when acyclic ---------------------------------

    #[test]
    fn test_no_circular_deps_acyclic() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a", AssumptionSource::Axiom, false));
        t.add_assumption(make_assumption("b", AssumptionSource::Axiom, false));
        t.add_assumption(make_assumption("c", AssumptionSource::Axiom, false));
        t.add_assumption_dependency(aid("a"), aid("b"));
        t.add_assumption_dependency(aid("b"), aid("c"));

        let cycles = t.detect_circular_dependencies();
        assert!(cycles.is_empty());
    }

    // -- 7. greedy minimal set cover --------------------------------------

    #[test]
    fn test_greedy_set_cover() {
        let universe: HashSet<ObligationId> =
            [oid("o1"), oid("o2"), oid("o3")].into_iter().collect();
        let mut covers = HashMap::new();
        // a1 covers o1, o2
        covers.insert(aid("a1"), [oid("o1"), oid("o2")].into_iter().collect());
        // a2 covers o2, o3
        covers.insert(aid("a2"), [oid("o2"), oid("o3")].into_iter().collect());
        // a3 covers o1
        covers.insert(aid("a3"), [oid("o1")].into_iter().collect());

        let finder = MinimalSetFinder::new(universe.clone(), covers);
        let result = finder.find_greedy();
        // Greedy should pick 2 assumptions that together cover all 3 obligations.
        assert_eq!(result.len(), 2);
        // Verify the selected assumptions actually cover all obligations.
        let mut covered = HashSet::new();
        for a in &result {
            if *a == aid("a1") {
                covered.extend([oid("o1"), oid("o2")]);
            } else if *a == aid("a2") {
                covered.extend([oid("o2"), oid("o3")]);
            } else if *a == aid("a3") {
                covered.insert(oid("o1"));
            }
        }
        assert!(universe.is_subset(&covered));
    }

    // -- 8. multiple minimal sets -----------------------------------------

    #[test]
    fn test_multiple_minimal_sets() {
        // Two obligations, two assumptions each covering one.
        let universe: HashSet<ObligationId> = [oid("o1"), oid("o2")].into_iter().collect();
        let mut covers = HashMap::new();
        covers.insert(aid("a1"), [oid("o1")].into_iter().collect());
        covers.insert(aid("a2"), [oid("o2")].into_iter().collect());
        covers.insert(aid("a3"), [oid("o1"), oid("o2")].into_iter().collect());

        let finder = MinimalSetFinder::new(universe, covers);
        let all = finder.find_all_minimal(10);
        // Minimal covers: {a1,a2} and {a3}
        assert!(all.len() >= 2);
        let single: HashSet<AssumptionId> = [aid("a3")].into_iter().collect();
        let pair: HashSet<AssumptionId> = [aid("a1"), aid("a2")].into_iter().collect();
        assert!(all.contains(&single));
        assert!(all.contains(&pair));
    }

    // -- 9. trust ratio computation ---------------------------------------

    #[test]
    fn test_trust_ratio_all_trusted() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a1", AssumptionSource::UserAssume, true));
        t.add_assumption(make_assumption("a2", AssumptionSource::Axiom, true));

        let (trusted, total, ratio) = t.trust_audit();
        assert_eq!(trusted, 2);
        assert_eq!(total, 2);
        assert!((ratio - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_trust_ratio_none_trusted() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a1", AssumptionSource::Requires, false));

        let (trusted, total, ratio) = t.trust_audit();
        assert_eq!(trusted, 0);
        assert_eq!(total, 1);
        assert!((ratio - 0.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_trust_ratio_mixed() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a1", AssumptionSource::Requires, false));
        t.add_assumption(make_assumption("a2", AssumptionSource::UserAssume, true));
        t.add_assumption(make_assumption("a3", AssumptionSource::Invariant, false));
        t.add_assumption(make_assumption("a4", AssumptionSource::Axiom, true));

        let (trusted, total, ratio) = t.trust_audit();
        assert_eq!(trusted, 2);
        assert_eq!(total, 4);
        assert!((ratio - 0.5).abs() < f64::EPSILON);
    }

    // -- 10. assumption strength classification ---------------------------

    #[test]
    fn test_strength_trivial_unused() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a1", AssumptionSource::Axiom, false));
        t.add_obligation(make_obligation("o1"));
        t.record_usage(oid("o1"), HashSet::new(), true);

        assert_eq!(t.classify_strength(&aid("a1")), AssumptionStrength::Trivial);
    }

    #[test]
    fn test_strength_critical_used_everywhere() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a1", AssumptionSource::Axiom, false));
        t.add_obligation(make_obligation("o1"));
        t.add_obligation(make_obligation("o2"));
        t.record_usage(oid("o1"), [aid("a1")].into_iter().collect(), true);
        t.record_usage(oid("o2"), [aid("a1")].into_iter().collect(), true);

        assert_eq!(
            t.classify_strength(&aid("a1")),
            AssumptionStrength::Critical
        );
    }

    #[test]
    fn test_strength_weak() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a1", AssumptionSource::Axiom, false));
        // used in 1 of 5 obligations
        for i in 0..5 {
            t.add_obligation(make_obligation(&format!("o{i}")));
            if i == 0 {
                t.record_usage(
                    oid(&format!("o{i}")),
                    [aid("a1")].into_iter().collect(),
                    true,
                );
            } else {
                t.record_usage(oid(&format!("o{i}")), HashSet::new(), true);
            }
        }
        assert_eq!(t.classify_strength(&aid("a1")), AssumptionStrength::Weak);
    }

    #[test]
    fn test_strength_moderate() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a1", AssumptionSource::Axiom, false));
        // used in 2 of 5 (40%)
        for i in 0..5 {
            t.add_obligation(make_obligation(&format!("o{i}")));
            if i < 2 {
                t.record_usage(
                    oid(&format!("o{i}")),
                    [aid("a1")].into_iter().collect(),
                    true,
                );
            } else {
                t.record_usage(oid(&format!("o{i}")), HashSet::new(), true);
            }
        }
        assert_eq!(
            t.classify_strength(&aid("a1")),
            AssumptionStrength::Moderate
        );
    }

    #[test]
    fn test_strength_strong() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a1", AssumptionSource::Axiom, false));
        // used in 3 of 5 (60%)
        for i in 0..5 {
            t.add_obligation(make_obligation(&format!("o{i}")));
            if i < 3 {
                t.record_usage(
                    oid(&format!("o{i}")),
                    [aid("a1")].into_iter().collect(),
                    true,
                );
            } else {
                t.record_usage(oid(&format!("o{i}")), HashSet::new(), true);
            }
        }
        assert_eq!(t.classify_strength(&aid("a1")), AssumptionStrength::Strong);
    }

    #[test]
    fn test_strength_unknown_assumption() {
        let t = AssumptionTracker::new();
        assert_eq!(
            t.classify_strength(&aid("nonexistent")),
            AssumptionStrength::Trivial
        );
    }

    // -- 11. transitive closure -------------------------------------------

    #[test]
    fn test_transitive_closure_chain() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a", AssumptionSource::Axiom, false));
        t.add_assumption(make_assumption("b", AssumptionSource::Axiom, false));
        t.add_assumption(make_assumption("c", AssumptionSource::Axiom, false));
        t.add_assumption(make_assumption("d", AssumptionSource::Axiom, false));
        t.add_assumption_dependency(aid("a"), aid("b"));
        t.add_assumption_dependency(aid("b"), aid("c"));
        t.add_assumption_dependency(aid("c"), aid("d"));

        let closure = t.transitive_closure(&aid("a"));
        assert_eq!(closure.len(), 3);
        assert!(closure.contains(&aid("b")));
        assert!(closure.contains(&aid("c")));
        assert!(closure.contains(&aid("d")));
    }

    #[test]
    fn test_transitive_closure_no_deps() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a", AssumptionSource::Axiom, false));
        let closure = t.transitive_closure(&aid("a"));
        assert!(closure.is_empty());
    }

    #[test]
    fn test_transitive_closure_with_cycle() {
        let mut t = AssumptionTracker::new();
        t.add_assumption_dependency(aid("a"), aid("b"));
        t.add_assumption_dependency(aid("b"), aid("a"));

        let closure = t.transitive_closure(&aid("a"));
        assert_eq!(closure.len(), 2);
        assert!(closure.contains(&aid("a")));
        assert!(closure.contains(&aid("b")));
    }

    // -- 12. reverse lookup (assumption -> obligations) --------------------

    #[test]
    fn test_assumption_obligations_reverse_lookup() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a1", AssumptionSource::Axiom, false));
        t.add_obligation(make_obligation("o1"));
        t.add_obligation(make_obligation("o2"));
        t.add_obligation(make_obligation("o3"));
        t.record_usage(oid("o1"), [aid("a1")].into_iter().collect(), true);
        t.record_usage(oid("o2"), [aid("a1")].into_iter().collect(), true);
        t.record_usage(oid("o3"), HashSet::new(), true);

        let obs = t.assumption_obligations(&aid("a1"));
        assert_eq!(obs.len(), 2);
        assert!(obs.contains(&oid("o1")));
        assert!(obs.contains(&oid("o2")));
    }

    #[test]
    fn test_assumption_obligations_empty() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a1", AssumptionSource::Axiom, false));
        let obs = t.assumption_obligations(&aid("a1"));
        assert!(obs.is_empty());
    }

    // -- 13. DOT graph output format --------------------------------------

    #[test]
    fn test_dot_output_basic_format() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a1", AssumptionSource::Axiom, false));
        t.add_obligation(make_obligation("o1"));
        t.record_usage(oid("o1"), [aid("a1")].into_iter().collect(), true);

        let dot = t.dependency_graph_dot();
        assert!(dot.starts_with("digraph assumption_deps {"));
        assert!(dot.ends_with("}\n"));
        assert!(dot.contains("\"a1\""));
        assert!(dot.contains("\"o1\""));
        assert!(dot.contains("shape=ellipse"));
        assert!(dot.contains("style=solid"));
    }

    #[test]
    fn test_dot_output_trusted_color() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption(
            "trusted_a",
            AssumptionSource::UserAssume,
            true,
        ));
        let dot = t.dependency_graph_dot();
        assert!(dot.contains("color=red"));
    }

    #[test]
    fn test_dot_output_unverified_dashed() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a1", AssumptionSource::Axiom, false));
        t.add_obligation(make_obligation("o1"));
        t.record_usage(oid("o1"), [aid("a1")].into_iter().collect(), false);

        let dot = t.dependency_graph_dot();
        assert!(dot.contains("style=dashed"));
    }

    #[test]
    fn test_dot_output_assumption_dep_edge() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a1", AssumptionSource::Axiom, false));
        t.add_assumption(make_assumption("a2", AssumptionSource::Axiom, false));
        t.add_assumption_dependency(aid("a1"), aid("a2"));

        let dot = t.dependency_graph_dot();
        assert!(dot.contains("style=dotted, color=blue"));
    }

    // -- 14. complex scenario (10+ assumptions, 5+ obligations) -----------

    #[test]
    fn test_complex_scenario() {
        let mut t = AssumptionTracker::new();

        // 12 assumptions
        for i in 0..12 {
            let trusted = i % 3 == 0;
            let source = match i % 5 {
                0 => AssumptionSource::Requires,
                1 => AssumptionSource::Invariant,
                2 => AssumptionSource::Broadcast,
                3 => AssumptionSource::Axiom,
                _ => AssumptionSource::UserAssume,
            };
            t.add_assumption(make_assumption(&format!("a{i}"), source, trusted));
        }

        // 6 obligations
        for i in 0..6 {
            t.add_obligation(make_obligation(&format!("o{i}")));
        }

        // Wire up: each obligation uses a subset of assumptions
        // o0 uses a0, a1, a2
        t.record_usage(
            oid("o0"),
            [aid("a0"), aid("a1"), aid("a2")].into_iter().collect(),
            true,
        );
        // o1 uses a0, a3, a4
        t.record_usage(
            oid("o1"),
            [aid("a0"), aid("a3"), aid("a4")].into_iter().collect(),
            true,
        );
        // o2 uses a0, a5, a6
        t.record_usage(
            oid("o2"),
            [aid("a0"), aid("a5"), aid("a6")].into_iter().collect(),
            true,
        );
        // o3 uses a0, a7
        t.record_usage(
            oid("o3"),
            [aid("a0"), aid("a7")].into_iter().collect(),
            false,
        );
        // o4 uses a0, a8, a9
        t.record_usage(
            oid("o4"),
            [aid("a0"), aid("a8"), aid("a9")].into_iter().collect(),
            true,
        );
        // o5 uses a0, a10
        t.record_usage(
            oid("o5"),
            [aid("a0"), aid("a10")].into_iter().collect(),
            true,
        );

        // a11 is completely unused

        // Add some assumption-to-assumption deps
        t.add_assumption_dependency(aid("a1"), aid("a2"));
        t.add_assumption_dependency(aid("a5"), aid("a6"));

        let analysis = t.analyze();

        // a11 should be unused
        assert!(analysis.unused_assumptions.contains(&aid("a11")));

        // a0 is critical (in every obligation)
        assert!(analysis.critical_assumptions.contains(&aid("a0")));

        // a0 usage count should be 6
        assert_eq!(analysis.assumption_usage_count[&aid("a0")], 6);

        // a11 usage count should be 0
        assert_eq!(analysis.assumption_usage_count[&aid("a11")], 0);

        // No cycles (acyclic deps)
        assert!(analysis.circular_dependencies.is_empty());

        // Trust: a0, a3, a6, a9 are trusted (i % 3 == 0)
        assert_eq!(analysis.trusted_assumption_count, 4);
        assert!((analysis.trust_ratio - 4.0 / 12.0).abs() < f64::EPSILON);
    }

    // -- 15. all assumptions used (none unused) ---------------------------

    #[test]
    fn test_all_assumptions_used() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a1", AssumptionSource::Axiom, false));
        t.add_assumption(make_assumption("a2", AssumptionSource::Axiom, false));
        t.add_obligation(make_obligation("o1"));
        t.record_usage(
            oid("o1"),
            [aid("a1"), aid("a2")].into_iter().collect(),
            true,
        );

        assert!(t.unused_assumptions().is_empty());
    }

    // -- 16. all assumptions unused (no obligations) ----------------------

    #[test]
    fn test_all_assumptions_unused_no_obligations() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a1", AssumptionSource::Axiom, false));
        t.add_assumption(make_assumption("a2", AssumptionSource::Axiom, false));
        t.add_assumption(make_assumption("a3", AssumptionSource::Axiom, false));

        let unused = t.unused_assumptions();
        assert_eq!(unused.len(), 3);
    }

    // -- 17. mixed verified/unverified ------------------------------------

    #[test]
    fn test_mixed_verified_unverified() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a1", AssumptionSource::Axiom, false));
        t.add_obligation(make_obligation("o1"));
        t.add_obligation(make_obligation("o2"));
        t.record_usage(oid("o1"), [aid("a1")].into_iter().collect(), true);
        t.record_usage(oid("o2"), [aid("a1")].into_iter().collect(), false);

        // a1 is still critical regardless of verification status
        assert_eq!(t.critical_assumptions(), vec![&aid("a1")]);

        // Verify DOT output distinguishes them
        let dot = t.dependency_graph_dot();
        assert!(dot.contains("style=solid"));
        assert!(dot.contains("style=dashed"));
    }

    // -- 18. assumption depends on another assumption ---------------------

    #[test]
    fn test_assumption_depends_on_assumption() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a1", AssumptionSource::Requires, false));
        t.add_assumption(make_assumption("a2", AssumptionSource::Axiom, false));
        t.add_assumption_dependency(aid("a1"), aid("a2"));

        let closure = t.transitive_closure(&aid("a1"));
        assert_eq!(closure.len(), 1);
        assert!(closure.contains(&aid("a2")));
    }

    // -- 19. obligation_assumptions returns None for unknown obligation ----

    #[test]
    fn test_obligation_assumptions_unknown() {
        let t = AssumptionTracker::new();
        assert!(t.obligation_assumptions(&oid("missing")).is_none());
    }

    #[test]
    fn test_obligation_assumptions_known() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a1", AssumptionSource::Axiom, false));
        t.add_assumption(make_assumption("a2", AssumptionSource::Axiom, false));
        t.add_obligation(make_obligation("o1"));
        t.record_usage(
            oid("o1"),
            [aid("a1"), aid("a2")].into_iter().collect(),
            true,
        );

        let result = t.obligation_assumptions(&oid("o1")).unwrap();
        assert_eq!(result.len(), 2);
        assert!(result.contains(&aid("a1")));
        assert!(result.contains(&aid("a2")));
    }

    // -- 20. two separate cycles ------------------------------------------

    #[test]
    fn test_two_separate_cycles() {
        let mut t = AssumptionTracker::new();
        // Cycle 1: a->b->a
        t.add_assumption_dependency(aid("a"), aid("b"));
        t.add_assumption_dependency(aid("b"), aid("a"));
        // Cycle 2: c->d->c
        t.add_assumption_dependency(aid("c"), aid("d"));
        t.add_assumption_dependency(aid("d"), aid("c"));

        let cycles = t.detect_circular_dependencies();
        assert_eq!(cycles.len(), 2);
    }

    // -- 21. greedy set cover: single assumption covers all ---------------

    #[test]
    fn test_greedy_single_covers_all() {
        let universe: HashSet<ObligationId> = [oid("o1"), oid("o2")].into_iter().collect();
        let mut covers = HashMap::new();
        covers.insert(aid("a1"), [oid("o1"), oid("o2")].into_iter().collect());
        covers.insert(aid("a2"), [oid("o1")].into_iter().collect());

        let finder = MinimalSetFinder::new(universe, covers);
        let result = finder.find_greedy();
        assert_eq!(result.len(), 1);
        assert!(result.contains(&aid("a1")));
    }

    // -- 22. greedy set cover: empty universe -----------------------------

    #[test]
    fn test_greedy_empty_universe() {
        let finder = MinimalSetFinder::new(HashSet::new(), HashMap::new());
        let result = finder.find_greedy();
        assert!(result.is_empty());
    }

    // -- 23. find_all_minimal: limit is respected -------------------------

    #[test]
    fn test_find_all_minimal_limit() {
        // Construct a scenario with many minimal covers.
        let universe: HashSet<ObligationId> = [oid("o1")].into_iter().collect();
        let mut covers = HashMap::new();
        for i in 0..20 {
            covers.insert(aid(&format!("a{i}")), [oid("o1")].into_iter().collect());
        }

        let finder = MinimalSetFinder::new(universe, covers);
        let results = finder.find_all_minimal(5);
        assert!(results.len() <= 5);
        // Each minimal set should have exactly 1 element.
        for s in &results {
            assert_eq!(s.len(), 1);
        }
    }

    // -- 24. Default trait -------------------------------------------------

    #[test]
    fn test_default_trait() {
        let t = AssumptionTracker::default();
        assert!(t.unused_assumptions().is_empty());
        assert!(t.critical_assumptions().is_empty());
    }

    // -- 25. Display impls ------------------------------------------------

    #[test]
    fn test_display_assumption_id() {
        let a = aid("test_id");
        assert_eq!(format!("{a}"), "test_id");
    }

    #[test]
    fn test_display_obligation_id() {
        let o = oid("test_ob");
        assert_eq!(format!("{o}"), "test_ob");
    }

    // -- 26. AssumptionSource variants ------------------------------------

    #[test]
    fn test_assumption_source_equality() {
        assert_eq!(AssumptionSource::Requires, AssumptionSource::Requires);
        assert_ne!(AssumptionSource::Requires, AssumptionSource::Axiom);
        assert_ne!(AssumptionSource::Broadcast, AssumptionSource::UserAssume);
        assert_eq!(
            AssumptionSource::InductionHypothesis,
            AssumptionSource::InductionHypothesis
        );
    }

    // -- 27. strength ordering --------------------------------------------

    #[test]
    fn test_strength_ordering() {
        assert!(AssumptionStrength::Trivial < AssumptionStrength::Weak);
        assert!(AssumptionStrength::Weak < AssumptionStrength::Moderate);
        assert!(AssumptionStrength::Moderate < AssumptionStrength::Strong);
        assert!(AssumptionStrength::Strong < AssumptionStrength::Critical);
    }

    // -- 28. multiple records for same obligation -------------------------

    #[test]
    fn test_multiple_records_same_obligation() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a1", AssumptionSource::Axiom, false));
        t.add_assumption(make_assumption("a2", AssumptionSource::Axiom, false));
        t.add_obligation(make_obligation("o1"));
        // Two separate usage records for same obligation
        t.record_usage(oid("o1"), [aid("a1")].into_iter().collect(), true);
        t.record_usage(oid("o1"), [aid("a2")].into_iter().collect(), true);

        // obligation_assumptions should merge both
        let result = t.obligation_assumptions(&oid("o1")).unwrap();
        assert_eq!(result.len(), 2);
        assert!(result.contains(&aid("a1")));
        assert!(result.contains(&aid("a2")));
    }

    // -- 29. transitive closure: diamond shape ----------------------------

    #[test]
    fn test_transitive_closure_diamond() {
        let mut t = AssumptionTracker::new();
        // a -> b, a -> c, b -> d, c -> d
        t.add_assumption_dependency(aid("a"), aid("b"));
        t.add_assumption_dependency(aid("a"), aid("c"));
        t.add_assumption_dependency(aid("b"), aid("d"));
        t.add_assumption_dependency(aid("c"), aid("d"));

        let closure = t.transitive_closure(&aid("a"));
        assert_eq!(closure.len(), 3);
        assert!(closure.contains(&aid("b")));
        assert!(closure.contains(&aid("c")));
        assert!(closure.contains(&aid("d")));
    }

    // -- 30. analyze with cycles ------------------------------------------

    #[test]
    fn test_analyze_with_cycles() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a1", AssumptionSource::Axiom, false));
        t.add_assumption(make_assumption("a2", AssumptionSource::Axiom, false));
        t.add_obligation(make_obligation("o1"));
        t.record_usage(
            oid("o1"),
            [aid("a1"), aid("a2")].into_iter().collect(),
            true,
        );
        t.add_assumption_dependency(aid("a1"), aid("a2"));
        t.add_assumption_dependency(aid("a2"), aid("a1"));

        let analysis = t.analyze();
        assert_eq!(analysis.circular_dependencies.len(), 1);
        assert!(analysis.unused_assumptions.is_empty());
        assert_eq!(analysis.critical_assumptions.len(), 2);
    }

    // -- 31. greedy cover: no assumptions cover anything ------------------

    #[test]
    fn test_greedy_no_coverage() {
        let universe: HashSet<ObligationId> = [oid("o1")].into_iter().collect();
        let covers: HashMap<AssumptionId, HashSet<ObligationId>> = HashMap::new();

        let finder = MinimalSetFinder::new(universe, covers);
        let result = finder.find_greedy();
        assert!(result.is_empty());
    }

    // -- 32. large transitive closure -------------------------------------

    #[test]
    fn test_transitive_closure_long_chain() {
        let mut t = AssumptionTracker::new();
        for i in 0..20 {
            t.add_assumption_dependency(aid(&format!("a{i}")), aid(&format!("a{}", i + 1)));
        }
        let closure = t.transitive_closure(&aid("a0"));
        assert_eq!(closure.len(), 20);
        for i in 1..=20 {
            assert!(closure.contains(&aid(&format!("a{i}"))));
        }
    }

    // -- 33. DOT graph empty tracker --------------------------------------

    #[test]
    fn test_dot_empty_tracker() {
        let t = AssumptionTracker::new();
        let dot = t.dependency_graph_dot();
        assert!(dot.starts_with("digraph assumption_deps {"));
        assert!(dot.contains("rankdir=LR"));
        assert!(dot.ends_with("}\n"));
    }

    // -- 34. analysis minimal sets with disjoint coverage -----------------

    #[test]
    fn test_analysis_disjoint_coverage() {
        let mut t = AssumptionTracker::new();
        t.add_assumption(make_assumption("a1", AssumptionSource::Axiom, false));
        t.add_assumption(make_assumption("a2", AssumptionSource::Axiom, false));
        t.add_obligation(make_obligation("o1"));
        t.add_obligation(make_obligation("o2"));
        // a1 covers o1 only, a2 covers o2 only — both needed
        t.record_usage(oid("o1"), [aid("a1")].into_iter().collect(), true);
        t.record_usage(oid("o2"), [aid("a2")].into_iter().collect(), true);

        let analysis = t.analyze();
        // Only one minimal set: {a1, a2}
        assert!(!analysis.minimal_assumption_sets.is_empty());
        let expected: HashSet<AssumptionId> = [aid("a1"), aid("a2")].into_iter().collect();
        assert!(analysis.minimal_assumption_sets.contains(&expected));
    }

    // -- 35. self-cycle (A depends on A) ----------------------------------

    #[test]
    fn test_self_cycle_not_reported() {
        // A self-loop is technically a cycle of size 1.
        // Tarjan SCC reports SCCs of size > 1, so self-loops are excluded
        // unless there is an explicit self-edge in the SCC algo.
        // Our implementation checks scc.len() > 1, so a pure self-loop is not reported.
        let mut t = AssumptionTracker::new();
        t.add_assumption_dependency(aid("a"), aid("a"));

        let cycles = t.detect_circular_dependencies();
        // Self-loops are size-1 SCCs — not reported.
        assert!(cycles.is_empty());
    }

    // -- 36. Cite is a trusted source exactly like Axiom ------------------

    #[test]
    fn test_cite_source_is_trusted_like_axiom() {
        // The cited/axiomatic trust surface: Cite is trusted iff Axiom is.
        assert!(AssumptionSource::Axiom.is_trusted_source());
        assert!(AssumptionSource::Cite { reference: None }.is_trusted_source());
        assert!(AssumptionSource::Cite {
            reference: Some("proofs::lemma_4_2".to_string())
        }
        .is_trusted_source());
        assert_eq!(
            AssumptionSource::Cite { reference: None }.is_trusted_source(),
            AssumptionSource::Axiom.is_trusted_source()
        );

        // Non-trusted sources must NOT be classified as trusted.
        assert!(!AssumptionSource::Requires.is_trusted_source());
        assert!(!AssumptionSource::Invariant.is_trusted_source());
        assert!(!AssumptionSource::Broadcast.is_trusted_source());
        assert!(!AssumptionSource::InductionHypothesis.is_trusted_source());
        assert!(!AssumptionSource::UserAssume.is_trusted_source());
    }

    #[test]
    fn test_cite_constructor_builds_trusted_assumption() {
        let cited = Assumption::cite(
            aid("c1"),
            "len_nonneg",
            "xs.len() >= 0",
            Some("proofs/seq.lean#len_nonneg".to_string()),
        );
        assert!(cited.is_trusted, "cited facts must be trusted");
        assert_eq!(
            cited.source,
            AssumptionSource::Cite {
                reference: Some("proofs/seq.lean#len_nonneg".to_string())
            }
        );
    }

    #[test]
    fn test_cite_assumption_counts_as_trusted_like_axiom() {
        // A Cite assumption and an Axiom assumption must be audited identically
        // as trusted, so the trust surface stays explicit.
        let mut t = AssumptionTracker::new();
        t.add_assumption(Assumption::cite(
            aid("c1"),
            "cited",
            "p(x)",
            Some("ref".to_string()),
        ));
        t.add_assumption(make_assumption("ax1", AssumptionSource::Axiom, true));
        t.add_assumption(make_assumption("r1", AssumptionSource::Requires, false));

        let (trusted, total, _ratio) = t.trust_audit();
        assert_eq!(total, 3);
        assert_eq!(
            trusted, 2,
            "both the Cite and Axiom assumptions are trusted"
        );
    }
}
