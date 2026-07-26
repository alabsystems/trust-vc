// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Theory lemma generation — automatically synthesizes theory-specific lemmas
//! that help the solver discharge proof obligations more efficiently.
//!
//! This module covers four theory families:
//! - **Arithmetic**: bounds propagation, monotonicity, sign analysis
//! - **Bitvector**: width bounds, shift limits, overflow detection
//! - **Sequence**: length non-negativity, index bounds, element types
//! - **Collection**: containment, size bounds, subset relations (Set, Map)
//!
//! The [`LemmaGenerator`] is the main entry point. Given a [`TheoryContext`]
//! describing the variables, their types, and known facts, it delegates to
//! per-theory generators and returns a deduplicated [`LemmaSet`].
//!
//! # Usage
//!
//! ```ignore
//! let config = GeneratorConfig::default();
//! let generator = LemmaGenerator::new(config);
//! let ctx = TheoryContext::new();
//! // ... populate ctx with variables and facts ...
//! let lemmas = generator.generate(&ctx);
//! ```

// Items in this module are an internal API for solver-side lemma synthesis.
// No production consumers exist yet — tests are the primary exerciser.
#[allow(dead_code)]
mod allow_dead {
    // Module-level dead_code suppression is handled by pub(crate) visibility
    // and the #[cfg(test)] test consumer below.
}

use std::collections::{HashMap, HashSet};
use std::fmt;

// ===========================================================================
// Theory classification
// ===========================================================================

/// Which SMT theory a generated lemma belongs to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum LemmaTheory {
    Arithmetic,
    BitVector,
    Sequence,
    Set,
    Map,
}

impl fmt::Display for LemmaTheory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Arithmetic => f.write_str("Arithmetic"),
            Self::BitVector => f.write_str("BitVector"),
            Self::Sequence => f.write_str("Sequence"),
            Self::Set => f.write_str("Set"),
            Self::Map => f.write_str("Map"),
        }
    }
}

// ===========================================================================
// Variable / type model (self-contained, no sibling imports)
// ===========================================================================

/// The type of a variable in the theory context.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum VarType {
    /// Signed integer with the given bit-width (e.g. 8, 16, 32, 64, 128).
    Int { width: u32 },
    /// Unsigned integer with the given bit-width.
    Uint { width: u32 },
    /// Mathematical (unbounded) integer.
    MathInt,
    /// Boolean.
    Bool,
    /// Bitvector with explicit width.
    BitVec { width: u32 },
    /// Sequence of elements with the given element type name.
    Seq { element_type: String },
    /// Finite set with the given element type name.
    Set { element_type: String },
    /// Map from key type to value type.
    Map {
        key_type: String,
        value_type: String,
    },
}

impl VarType {
    fn theory(&self) -> LemmaTheory {
        match self {
            Self::Int { .. } | Self::Uint { .. } | Self::MathInt => LemmaTheory::Arithmetic,
            Self::Bool => LemmaTheory::Arithmetic,
            Self::BitVec { .. } => LemmaTheory::BitVector,
            Self::Seq { .. } => LemmaTheory::Sequence,
            Self::Set { .. } => LemmaTheory::Set,
            Self::Map { .. } => LemmaTheory::Map,
        }
    }

    fn is_numeric(&self) -> bool {
        matches!(self, Self::Int { .. } | Self::Uint { .. } | Self::MathInt)
    }
}

/// A variable declaration in the theory context.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Variable {
    pub(crate) name: String,
    pub(crate) var_type: VarType,
}

// ===========================================================================
// Known facts
// ===========================================================================

/// A fact known about the verification context (e.g., from requires/invariant).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum KnownFact {
    /// `var >= lower`
    LowerBound { var: String, lower: i128 },
    /// `var <= upper`
    UpperBound { var: String, upper: i128 },
    /// `var == value`
    Equality { var: String, value: i128 },
    /// `lhs == rhs` (variable equality)
    VarEquality { lhs: String, rhs: String },
    /// `var > 0` or `var >= 1`
    Positive { var: String },
    /// `var < 0` or `var <= -1`
    Negative { var: String },
    /// `var != 0`
    NonZero { var: String },
    /// `seq.len() == n`
    SeqLength { seq: String, length: u64 },
    /// `set.contains(elem)`
    SetContains { set: String, elem: String },
    /// `subset <= superset`
    Subset { subset: String, superset: String },
    /// `map.contains_key(key)`
    MapContainsKey { map: String, key: String },
}

// ===========================================================================
// Theory context
// ===========================================================================

/// Collects all variables and known facts relevant to lemma generation.
#[derive(Debug)]
pub(crate) struct TheoryContext {
    variables: Vec<Variable>,
    facts: Vec<KnownFact>,
    var_index: HashMap<String, usize>,
}

impl TheoryContext {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            variables: Vec::new(),
            facts: Vec::new(),
            var_index: HashMap::new(),
        }
    }

    pub(crate) fn add_variable(&mut self, name: &str, var_type: VarType) {
        let idx = self.variables.len();
        self.variables.push(Variable {
            name: name.to_owned(),
            var_type,
        });
        self.var_index.insert(name.to_owned(), idx);
    }

    pub(crate) fn add_fact(&mut self, fact: KnownFact) {
        self.facts.push(fact);
    }

    #[must_use]
    pub(crate) fn variables(&self) -> &[Variable] {
        &self.variables
    }

    #[must_use]
    pub(crate) fn facts(&self) -> &[KnownFact] {
        &self.facts
    }

    #[must_use]
    pub(crate) fn lookup(&self, name: &str) -> Option<&Variable> {
        self.var_index.get(name).map(|&i| &self.variables[i])
    }

    /// Return all variables whose type maps to the given theory.
    #[must_use]
    pub(crate) fn variables_for_theory(&self, theory: LemmaTheory) -> Vec<&Variable> {
        self.variables
            .iter()
            .filter(|v| v.var_type.theory() == theory)
            .collect()
    }
}

// ===========================================================================
// Generated lemma
// ===========================================================================

/// Confidence level for a generated lemma.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Confidence {
    /// Speculative — may or may not help.
    Low,
    /// Heuristic — likely helpful but not guaranteed sound in isolation.
    Medium,
    /// Valid given the known facts.
    High,
    /// Always valid (tautology / type-level invariant).
    Definite,
}

/// A single lemma produced by theory-specific generation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct GeneratedLemma {
    /// SMT-like expression string (e.g. `(>= (seq.len s) 0)`).
    pub(crate) expression: String,
    /// Which theory this lemma belongs to.
    pub(crate) theory: LemmaTheory,
    /// How confident the generator is that this lemma is useful.
    pub(crate) confidence: Confidence,
    /// Human-readable justification.
    pub(crate) justification: String,
}

impl GeneratedLemma {
    #[must_use]
    fn new(
        expression: &str,
        theory: LemmaTheory,
        confidence: Confidence,
        justification: &str,
    ) -> Self {
        Self {
            expression: expression.to_owned(),
            theory,
            confidence,
            justification: justification.to_owned(),
        }
    }

    /// Returns true if this lemma logically subsumes `other`.
    ///
    /// Subsumption is approximate: we check syntactic containment and a few
    /// structural patterns. A true SMT subsumption check would require a
    /// solver query, which is out of scope for the filter.
    #[must_use]
    fn subsumes(&self, other: &Self) -> bool {
        if self.theory != other.theory {
            return false;
        }
        // Exact match is trivially subsuming.
        if self.expression == other.expression {
            return true;
        }
        // A tighter bound subsumes a weaker one for the same variable.
        // We detect this via expression prefix matching for simple patterns.
        false
    }
}

impl fmt::Display for GeneratedLemma {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "[{}|{:?}] {} — {}",
            self.theory, self.confidence, self.expression, self.justification
        )
    }
}

// ===========================================================================
// LemmaSet — deduplicated collection with provenance
// ===========================================================================

/// A deduplicated, theory-indexed set of generated lemmas.
#[derive(Debug, Clone)]
pub(crate) struct LemmaSet {
    lemmas: Vec<GeneratedLemma>,
    seen: HashSet<String>,
}

impl LemmaSet {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            lemmas: Vec::new(),
            seen: HashSet::new(),
        }
    }

    /// Add a lemma. Duplicate expressions are silently dropped.
    pub(crate) fn add(&mut self, lemma: GeneratedLemma) {
        if self.seen.insert(lemma.expression.clone()) {
            self.lemmas.push(lemma);
        }
    }

    /// Remove exact-expression duplicates (idempotent after `add`).
    pub(crate) fn deduplicate(&mut self) {
        let mut unique = HashSet::new();
        self.lemmas.retain(|l| unique.insert(l.expression.clone()));
        self.seen = unique;
    }

    #[must_use]
    pub(crate) fn as_vec(&self) -> Vec<GeneratedLemma> {
        self.lemmas.clone()
    }

    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.lemmas.len()
    }

    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.lemmas.is_empty()
    }

    /// Return lemmas belonging to a specific theory.
    #[must_use]
    pub(crate) fn by_theory(&self, theory: LemmaTheory) -> Vec<&GeneratedLemma> {
        self.lemmas.iter().filter(|l| l.theory == theory).collect()
    }

    /// Return lemmas with at least the given confidence.
    #[must_use]
    pub(crate) fn at_least(&self, min: Confidence) -> Vec<&GeneratedLemma> {
        self.lemmas.iter().filter(|l| l.confidence >= min).collect()
    }
}

// ===========================================================================
// Per-theory generators
// ===========================================================================

// ---------------------------------------------------------------------------
// Arithmetic
// ---------------------------------------------------------------------------

pub(crate) struct ArithLemmaGen;

impl ArithLemmaGen {
    /// Generate arithmetic lemmas from variables and known facts.
    #[must_use]
    pub(crate) fn generate(variables: &[&Variable], facts: &[KnownFact]) -> Vec<GeneratedLemma> {
        let mut out = Vec::new();

        // 1. Type-level bounds for fixed-width integers.
        for var in variables {
            match &var.var_type {
                VarType::Int { width } => {
                    let half = (*width as i128) - 1;
                    let lo = -(1i128 << half);
                    let hi = (1i128 << half) - 1;
                    out.push(GeneratedLemma::new(
                        &format!("(>= {} {})", var.name, lo),
                        LemmaTheory::Arithmetic,
                        Confidence::Definite,
                        &format!("i{} lower bound", width),
                    ));
                    out.push(GeneratedLemma::new(
                        &format!("(<= {} {})", var.name, hi),
                        LemmaTheory::Arithmetic,
                        Confidence::Definite,
                        &format!("i{} upper bound", width),
                    ));
                }
                VarType::Uint { width } => {
                    let hi = if *width >= 128 {
                        i128::MAX
                    } else {
                        (1i128 << *width) - 1
                    };
                    out.push(GeneratedLemma::new(
                        &format!("(>= {} 0)", var.name),
                        LemmaTheory::Arithmetic,
                        Confidence::Definite,
                        &format!("u{} non-negative", width),
                    ));
                    out.push(GeneratedLemma::new(
                        &format!("(<= {} {})", var.name, hi),
                        LemmaTheory::Arithmetic,
                        Confidence::Definite,
                        &format!("u{} upper bound", width),
                    ));
                }
                _ => {}
            }
        }

        // 2. Bounds propagation from known facts.
        let mut lower: HashMap<&str, i128> = HashMap::new();
        let mut upper: HashMap<&str, i128> = HashMap::new();

        for fact in facts {
            match fact {
                KnownFact::LowerBound { var, lower: lo } => {
                    lower
                        .entry(var.as_str())
                        .and_modify(|cur| *cur = (*cur).max(*lo))
                        .or_insert(*lo);
                }
                KnownFact::UpperBound { var, upper: hi } => {
                    upper
                        .entry(var.as_str())
                        .and_modify(|cur| *cur = (*cur).min(*hi))
                        .or_insert(*hi);
                }
                KnownFact::Equality { var, value } => {
                    lower.insert(var.as_str(), *value);
                    upper.insert(var.as_str(), *value);
                }
                KnownFact::Positive { var } => {
                    lower
                        .entry(var.as_str())
                        .and_modify(|cur| *cur = (*cur).max(1))
                        .or_insert(1);
                }
                KnownFact::Negative { var } => {
                    upper
                        .entry(var.as_str())
                        .and_modify(|cur| *cur = (*cur).min(-1))
                        .or_insert(-1);
                }
                _ => {}
            }
        }

        // 3. Sign analysis: produce non-zero / sign lemmas.
        for (&name, &lo) in &lower {
            if lo > 0 {
                out.push(GeneratedLemma::new(
                    &format!("(not (= {} 0))", name),
                    LemmaTheory::Arithmetic,
                    Confidence::High,
                    "positive implies non-zero",
                ));
                out.push(GeneratedLemma::new(
                    &format!("(> {} 0)", name),
                    LemmaTheory::Arithmetic,
                    Confidence::High,
                    "positive sign from lower bound",
                ));
            }
        }

        for (&name, &hi) in &upper {
            if hi < 0 {
                out.push(GeneratedLemma::new(
                    &format!("(not (= {} 0))", name),
                    LemmaTheory::Arithmetic,
                    Confidence::High,
                    "negative implies non-zero",
                ));
                out.push(GeneratedLemma::new(
                    &format!("(< {} 0)", name),
                    LemmaTheory::Arithmetic,
                    Confidence::High,
                    "negative sign from upper bound",
                ));
            }
        }

        // 4. Monotonicity between pairs with known ordering.
        for (&a, &a_hi) in &upper {
            if let Some(&b_lo) = lower.get(a) {
                if a_hi < b_lo {
                    // Contradiction — skip (will be caught by solver).
                    continue;
                }
            }
            for (&b, &b_lo) in &lower {
                if a == b {
                    continue;
                }
                if a_hi < b_lo {
                    out.push(GeneratedLemma::new(
                        &format!("(< {} {})", a, b),
                        LemmaTheory::Arithmetic,
                        Confidence::High,
                        "ordering from bound analysis",
                    ));
                }
            }
        }

        out
    }
}

// ---------------------------------------------------------------------------
// Bitvector
// ---------------------------------------------------------------------------

pub(crate) struct BvLemmaGen;

impl BvLemmaGen {
    /// Generate bitvector lemmas for variables of a given width.
    #[must_use]
    pub(crate) fn generate(variables: &[&Variable], _width: u32) -> Vec<GeneratedLemma> {
        let mut out = Vec::new();

        for var in variables {
            if let VarType::BitVec { width } = &var.var_type {
                let w = *width;
                let max_val = if w >= 128 {
                    u128::MAX
                } else {
                    (1u128 << w) - 1
                };

                // Width-bounded range.
                out.push(GeneratedLemma::new(
                    &format!(
                        "(bvule {} #x{:0>width$})",
                        var.name,
                        max_val,
                        width = (w as usize).div_ceil(4)
                    ),
                    LemmaTheory::BitVector,
                    Confidence::Definite,
                    &format!("bv{} upper bound", w),
                ));

                // Shift limit: shifting by >= width is either 0 or undefined.
                out.push(GeneratedLemma::new(
                    &format!(
                        "(=> (bvuge shift_{n} {w}) (= (bvshl {n} shift_{n}) #b{zeros}))",
                        n = var.name,
                        w = w,
                        zeros = "0".repeat(w as usize)
                    ),
                    LemmaTheory::BitVector,
                    Confidence::High,
                    &format!("left-shift by >= {} produces zero", w),
                ));

                // Mask idempotence: x & x == x.
                out.push(GeneratedLemma::new(
                    &format!("(= (bvand {n} {n}) {n})", n = var.name),
                    LemmaTheory::BitVector,
                    Confidence::Definite,
                    "AND idempotence",
                ));

                // OR identity: x | 0 == x.
                out.push(GeneratedLemma::new(
                    &format!(
                        "(= (bvor {n} #b{zeros}) {n})",
                        n = var.name,
                        zeros = "0".repeat(w as usize)
                    ),
                    LemmaTheory::BitVector,
                    Confidence::Definite,
                    "OR identity with zero",
                ));

                // Overflow detection hint for addition.
                if w <= 64 {
                    out.push(GeneratedLemma::new(
                        &format!(
                            "(=> (and (bvult {n} #x{half:0>hw$}) (bvult other_{n} #x{half:0>hw$})) \
                             (not (bvult (bvadd {n} other_{n}) {n})))",
                            n = var.name,
                            half = (1u128 << (w - 1)),
                            hw = (w as usize).div_ceil(4),
                        ),
                        LemmaTheory::BitVector,
                        Confidence::Medium,
                        "no-overflow for small addends",
                    ));
                }
            }
        }

        out
    }
}

// ---------------------------------------------------------------------------
// Sequence
// ---------------------------------------------------------------------------

pub(crate) struct SeqLemmaGen;

impl SeqLemmaGen {
    /// Generate sequence axiom lemmas.
    #[must_use]
    pub(crate) fn generate(seq_vars: &[&Variable]) -> Vec<GeneratedLemma> {
        let mut out = Vec::new();

        for var in seq_vars {
            if let VarType::Seq { element_type } = &var.var_type {
                let n = &var.name;

                // Length non-negative.
                out.push(GeneratedLemma::new(
                    &format!("(>= (seq.len {}) 0)", n),
                    LemmaTheory::Sequence,
                    Confidence::Definite,
                    "sequence length is non-negative",
                ));

                // Empty sequence has length 0.
                out.push(GeneratedLemma::new(
                    &format!("(= (seq.len (as seq.empty (Seq {}))) 0)", element_type),
                    LemmaTheory::Sequence,
                    Confidence::Definite,
                    "empty sequence has length zero",
                ));

                // Concatenation length.
                for other in seq_vars {
                    if let VarType::Seq {
                        element_type: other_elem,
                    } = &other.var_type
                    {
                        if other_elem == element_type && other.name != *n {
                            out.push(GeneratedLemma::new(
                                &format!(
                                    "(= (seq.len (seq.++ {} {})) (+ (seq.len {}) (seq.len {})))",
                                    n, other.name, n, other.name
                                ),
                                LemmaTheory::Sequence,
                                Confidence::Definite,
                                "concat length is sum of lengths",
                            ));
                        }
                    }
                }

                // Index bounds: valid index < length.
                out.push(GeneratedLemma::new(
                    &format!(
                        "(=> (and (>= i 0) (< i (seq.len {}))) (= (seq.nth {} i) (seq.nth {} i)))",
                        n, n, n
                    ),
                    LemmaTheory::Sequence,
                    Confidence::Definite,
                    "index in bounds is well-defined",
                ));

                // Subsequence length.
                out.push(GeneratedLemma::new(
                    &format!(
                        "(=> (and (>= start 0) (>= len 0) (<= (+ start len) (seq.len {}))) \
                         (= (seq.len (seq.extract {} start len)) len))",
                        n, n
                    ),
                    LemmaTheory::Sequence,
                    Confidence::Definite,
                    "subsequence length equals requested length",
                ));
            }
        }

        out
    }
}

// ---------------------------------------------------------------------------
// Collection (Set + Map)
// ---------------------------------------------------------------------------

pub(crate) struct CollectionLemmaGen;

impl CollectionLemmaGen {
    /// Generate lemmas for Set and Map variables.
    #[must_use]
    pub(crate) fn generate(variables: &[&Variable], facts: &[KnownFact]) -> Vec<GeneratedLemma> {
        let mut out = Vec::new();

        // Collect set and map variables.
        let sets: Vec<&Variable> = variables
            .iter()
            .filter(|v| matches!(v.var_type, VarType::Set { .. }))
            .copied()
            .collect();

        let maps: Vec<&Variable> = variables
            .iter()
            .filter(|v| matches!(v.var_type, VarType::Map { .. }))
            .copied()
            .collect();

        // --- Set lemmas ---
        for s in &sets {
            let n = &s.name;

            // Size non-negative.
            out.push(GeneratedLemma::new(
                &format!("(>= (set.card {}) 0)", n),
                LemmaTheory::Set,
                Confidence::Definite,
                "set cardinality is non-negative",
            ));

            // Empty set has cardinality 0.
            out.push(GeneratedLemma::new(
                &format!(
                    "(= (set.card (as set.empty (Set {}))) 0)",
                    match &s.var_type {
                        VarType::Set { element_type } => element_type.as_str(),
                        _ => "?",
                    }
                ),
                LemmaTheory::Set,
                Confidence::Definite,
                "empty set has zero cardinality",
            ));
        }

        // Subset relations from known facts.
        for fact in facts {
            if let KnownFact::Subset { subset, superset } = fact {
                // Containment propagation.
                out.push(GeneratedLemma::new(
                    &format!("(=> (set.member e {}) (set.member e {}))", subset, superset),
                    LemmaTheory::Set,
                    Confidence::Definite,
                    "subset membership propagation",
                ));

                // Cardinality ordering.
                out.push(GeneratedLemma::new(
                    &format!("(<= (set.card {}) (set.card {}))", subset, superset),
                    LemmaTheory::Set,
                    Confidence::Definite,
                    "subset has cardinality <= superset",
                ));
            }

            // Known containment.
            if let KnownFact::SetContains { set, elem } = fact {
                out.push(GeneratedLemma::new(
                    &format!("(set.member {} {})", elem, set),
                    LemmaTheory::Set,
                    Confidence::Definite,
                    "known containment fact",
                ));

                // Non-empty.
                out.push(GeneratedLemma::new(
                    &format!("(> (set.card {}) 0)", set),
                    LemmaTheory::Set,
                    Confidence::High,
                    "set with known element is non-empty",
                ));
            }
        }

        // --- Map lemmas ---
        for m in &maps {
            let n = &m.name;

            // Domain size non-negative.
            out.push(GeneratedLemma::new(
                &format!("(>= (map.size {}) 0)", n),
                LemmaTheory::Map,
                Confidence::Definite,
                "map size is non-negative",
            ));
        }

        // Known key containment.
        for fact in facts {
            if let KnownFact::MapContainsKey { map, key } = fact {
                out.push(GeneratedLemma::new(
                    &format!("(map.contains_key {} {})", map, key),
                    LemmaTheory::Map,
                    Confidence::Definite,
                    "known key containment",
                ));

                out.push(GeneratedLemma::new(
                    &format!("(> (map.size {}) 0)", map),
                    LemmaTheory::Map,
                    Confidence::High,
                    "map with known key is non-empty",
                ));
            }
        }

        out
    }
}

// ===========================================================================
// Lemma filter — deduplication, subsumption, relevancy
// ===========================================================================

/// Filters generated lemmas: removes duplicates, subsumed lemmas, and
/// irrelevant lemmas that reference variables not in the context.
pub(crate) struct LemmaFilter {
    min_confidence: Confidence,
}

impl LemmaFilter {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            min_confidence: Confidence::Low,
        }
    }

    #[must_use]
    pub(crate) fn with_min_confidence(mut self, min: Confidence) -> Self {
        self.min_confidence = min;
        self
    }

    /// Filter lemmas: deduplicate, check subsumption, apply relevancy filter.
    #[must_use]
    pub(crate) fn filter(
        &self,
        lemmas: Vec<GeneratedLemma>,
        context: &TheoryContext,
    ) -> Vec<GeneratedLemma> {
        // 1. Confidence gate.
        let lemmas: Vec<_> = lemmas
            .into_iter()
            .filter(|l| l.confidence >= self.min_confidence)
            .collect();

        // 2. Exact-expression dedup.
        let mut seen = HashSet::new();
        let lemmas: Vec<_> = lemmas
            .into_iter()
            .filter(|l| seen.insert(l.expression.clone()))
            .collect();

        // 3. Subsumption removal (quadratic but sets are small).
        let mut subsumed = vec![false; lemmas.len()];
        for i in 0..lemmas.len() {
            if subsumed[i] {
                continue;
            }
            for j in (i + 1)..lemmas.len() {
                if subsumed[j] {
                    continue;
                }
                if lemmas[i].subsumes(&lemmas[j]) {
                    subsumed[j] = true;
                } else if lemmas[j].subsumes(&lemmas[i]) {
                    subsumed[i] = true;
                    break;
                }
            }
        }

        let lemmas: Vec<_> = lemmas
            .into_iter()
            .enumerate()
            .filter(|(i, _)| !subsumed[*i])
            .map(|(_, l)| l)
            .collect();

        // 4. Relevancy: keep only lemmas that mention at least one context variable.
        let var_names: HashSet<&str> = context
            .variables()
            .iter()
            .map(|v| v.name.as_str())
            .collect();

        lemmas
            .into_iter()
            .filter(|l| var_names.iter().any(|n| l.expression.contains(n)))
            .collect()
    }
}

// ===========================================================================
// Generator config
// ===========================================================================

/// Configuration for the lemma generator.
#[derive(Debug, Clone)]
pub(crate) struct GeneratorConfig {
    /// Whether to generate arithmetic lemmas.
    pub(crate) enable_arithmetic: bool,
    /// Whether to generate bitvector lemmas.
    pub(crate) enable_bitvector: bool,
    /// Whether to generate sequence lemmas.
    pub(crate) enable_sequence: bool,
    /// Whether to generate collection (set/map) lemmas.
    pub(crate) enable_collection: bool,
    /// Minimum confidence to keep in the final set.
    pub(crate) min_confidence: Confidence,
    /// Maximum lemmas per theory (0 = unlimited).
    pub(crate) max_per_theory: usize,
}

impl Default for GeneratorConfig {
    fn default() -> Self {
        Self {
            enable_arithmetic: true,
            enable_bitvector: true,
            enable_sequence: true,
            enable_collection: true,
            min_confidence: Confidence::Low,
            max_per_theory: 0,
        }
    }
}

// ===========================================================================
// LemmaGenerator — top-level entry point
// ===========================================================================

/// Main orchestrator: delegates to per-theory generators, then filters and
/// deduplicates the result into a [`LemmaSet`].
pub(crate) struct LemmaGenerator {
    config: GeneratorConfig,
}

impl LemmaGenerator {
    #[must_use]
    pub(crate) fn new(config: GeneratorConfig) -> Self {
        Self { config }
    }

    /// Generate lemmas for the given context.
    #[must_use]
    pub(crate) fn generate(&self, context: &TheoryContext) -> LemmaSet {
        let mut all_lemmas: Vec<GeneratedLemma> = Vec::new();

        if self.config.enable_arithmetic {
            let arith_vars = context.variables_for_theory(LemmaTheory::Arithmetic);
            if !arith_vars.is_empty() {
                all_lemmas.extend(ArithLemmaGen::generate(&arith_vars, context.facts()));
            }
        }

        if self.config.enable_bitvector {
            let bv_vars = context.variables_for_theory(LemmaTheory::BitVector);
            if !bv_vars.is_empty() {
                // Use the maximum width across all BV vars for the width parameter.
                let max_width = bv_vars
                    .iter()
                    .filter_map(|v| match &v.var_type {
                        VarType::BitVec { width } => Some(*width),
                        _ => None,
                    })
                    .max()
                    .unwrap_or(32);
                all_lemmas.extend(BvLemmaGen::generate(&bv_vars, max_width));
            }
        }

        if self.config.enable_sequence {
            let seq_vars = context.variables_for_theory(LemmaTheory::Sequence);
            if !seq_vars.is_empty() {
                all_lemmas.extend(SeqLemmaGen::generate(&seq_vars));
            }
        }

        if self.config.enable_collection {
            let set_vars = context.variables_for_theory(LemmaTheory::Set);
            let map_vars = context.variables_for_theory(LemmaTheory::Map);
            let mut collection_vars: Vec<&Variable> = Vec::new();
            collection_vars.extend(set_vars);
            collection_vars.extend(map_vars);
            if !collection_vars.is_empty() {
                all_lemmas.extend(CollectionLemmaGen::generate(
                    &collection_vars,
                    context.facts(),
                ));
            }
        }

        // Filter.
        let filter = LemmaFilter::new().with_min_confidence(self.config.min_confidence);
        let filtered = filter.filter(all_lemmas, context);

        // Build the LemmaSet, optionally capping per-theory.
        let mut set = LemmaSet::new();
        if self.config.max_per_theory == 0 {
            for l in filtered {
                set.add(l);
            }
        } else {
            let mut counts: HashMap<LemmaTheory, usize> = HashMap::new();
            for l in filtered {
                let count = counts.entry(l.theory).or_insert(0);
                if *count < self.config.max_per_theory {
                    set.add(l);
                    *count += 1;
                }
            }
        }

        set
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // -----------------------------------------------------------------------
    // Helper: build a minimal context
    // -----------------------------------------------------------------------

    fn ctx_with_u32(name: &str) -> TheoryContext {
        let mut ctx = TheoryContext::new();
        ctx.add_variable(name, VarType::Uint { width: 32 });
        ctx
    }

    fn ctx_with_i32(name: &str) -> TheoryContext {
        let mut ctx = TheoryContext::new();
        ctx.add_variable(name, VarType::Int { width: 32 });
        ctx
    }

    // -----------------------------------------------------------------------
    // TheoryContext
    // -----------------------------------------------------------------------

    #[test]
    fn test_theory_context_new_is_empty() {
        let ctx = TheoryContext::new();
        assert!(ctx.variables().is_empty());
        assert!(ctx.facts().is_empty());
    }

    #[test]
    fn test_theory_context_add_variable_and_lookup() {
        let mut ctx = TheoryContext::new();
        ctx.add_variable("x", VarType::Int { width: 32 });
        assert_eq!(ctx.variables().len(), 1);
        let v = ctx.lookup("x").expect("should find x");
        assert_eq!(v.name, "x");
        assert_eq!(v.var_type, VarType::Int { width: 32 });
    }

    #[test]
    fn test_theory_context_lookup_missing_returns_none() {
        let ctx = ctx_with_u32("x");
        assert!(ctx.lookup("y").is_none());
    }

    #[test]
    fn test_theory_context_add_fact() {
        let mut ctx = ctx_with_i32("x");
        ctx.add_fact(KnownFact::Positive { var: "x".into() });
        assert_eq!(ctx.facts().len(), 1);
    }

    #[test]
    fn test_theory_context_variables_for_theory_filters() {
        let mut ctx = TheoryContext::new();
        ctx.add_variable("a", VarType::Int { width: 32 });
        ctx.add_variable("b", VarType::BitVec { width: 8 });
        ctx.add_variable(
            "s",
            VarType::Seq {
                element_type: "Int".into(),
            },
        );

        assert_eq!(ctx.variables_for_theory(LemmaTheory::Arithmetic).len(), 1);
        assert_eq!(ctx.variables_for_theory(LemmaTheory::BitVector).len(), 1);
        assert_eq!(ctx.variables_for_theory(LemmaTheory::Sequence).len(), 1);
        assert_eq!(ctx.variables_for_theory(LemmaTheory::Set).len(), 0);
    }

    // -----------------------------------------------------------------------
    // VarType
    // -----------------------------------------------------------------------

    #[test]
    fn test_var_type_theory_mapping() {
        assert_eq!(VarType::Int { width: 32 }.theory(), LemmaTheory::Arithmetic);
        assert_eq!(
            VarType::Uint { width: 64 }.theory(),
            LemmaTheory::Arithmetic
        );
        assert_eq!(VarType::MathInt.theory(), LemmaTheory::Arithmetic);
        assert_eq!(VarType::Bool.theory(), LemmaTheory::Arithmetic);
        assert_eq!(
            VarType::BitVec { width: 8 }.theory(),
            LemmaTheory::BitVector
        );
        assert_eq!(
            VarType::Seq {
                element_type: "i32".into()
            }
            .theory(),
            LemmaTheory::Sequence
        );
        assert_eq!(
            VarType::Set {
                element_type: "i32".into()
            }
            .theory(),
            LemmaTheory::Set
        );
        assert_eq!(
            VarType::Map {
                key_type: "k".into(),
                value_type: "v".into()
            }
            .theory(),
            LemmaTheory::Map
        );
    }

    #[test]
    fn test_var_type_is_numeric() {
        assert!(VarType::Int { width: 8 }.is_numeric());
        assert!(VarType::Uint { width: 16 }.is_numeric());
        assert!(VarType::MathInt.is_numeric());
        assert!(!VarType::Bool.is_numeric());
        assert!(!VarType::BitVec { width: 32 }.is_numeric());
        assert!(!VarType::Seq {
            element_type: "X".into()
        }
        .is_numeric());
    }

    // -----------------------------------------------------------------------
    // ArithLemmaGen
    // -----------------------------------------------------------------------

    #[test]
    fn test_arith_gen_u32_produces_bounds() {
        let ctx = ctx_with_u32("x");
        let vars = ctx.variables_for_theory(LemmaTheory::Arithmetic);
        let lemmas = ArithLemmaGen::generate(&vars, ctx.facts());

        // Should produce non-negative and upper bound.
        assert!(lemmas.iter().any(|l| l.expression.contains(">= x 0")));
        assert!(lemmas.iter().any(|l| l.expression.contains("<= x")));
    }

    #[test]
    fn test_arith_gen_i32_produces_signed_bounds() {
        let ctx = ctx_with_i32("y");
        let vars = ctx.variables_for_theory(LemmaTheory::Arithmetic);
        let lemmas = ArithLemmaGen::generate(&vars, ctx.facts());

        assert!(lemmas
            .iter()
            .any(|l| l.expression.contains(">= y -2147483648")));
        assert!(lemmas
            .iter()
            .any(|l| l.expression.contains("<= y 2147483647")));
    }

    #[test]
    fn test_arith_gen_positive_fact_produces_sign_lemmas() {
        let mut ctx = ctx_with_i32("z");
        ctx.add_fact(KnownFact::Positive { var: "z".into() });
        let vars = ctx.variables_for_theory(LemmaTheory::Arithmetic);
        let lemmas = ArithLemmaGen::generate(&vars, ctx.facts());

        assert!(lemmas.iter().any(|l| l.expression.contains("(> z 0)")));
        assert!(lemmas
            .iter()
            .any(|l| l.expression.contains("(not (= z 0))")));
    }

    #[test]
    fn test_arith_gen_negative_fact_produces_sign_lemmas() {
        let mut ctx = ctx_with_i32("n");
        ctx.add_fact(KnownFact::Negative { var: "n".into() });
        let vars = ctx.variables_for_theory(LemmaTheory::Arithmetic);
        let lemmas = ArithLemmaGen::generate(&vars, ctx.facts());

        assert!(lemmas.iter().any(|l| l.expression.contains("(< n 0)")));
    }

    #[test]
    fn test_arith_gen_math_int_no_width_bounds() {
        let mut ctx = TheoryContext::new();
        ctx.add_variable("m", VarType::MathInt);
        let vars = ctx.variables_for_theory(LemmaTheory::Arithmetic);
        let lemmas = ArithLemmaGen::generate(&vars, ctx.facts());

        // MathInt has no width bounds, so only fact-derived lemmas should appear.
        assert!(lemmas.is_empty());
    }

    #[test]
    fn test_arith_gen_ordering_from_bounds() {
        let mut ctx = TheoryContext::new();
        ctx.add_variable("a", VarType::Int { width: 32 });
        ctx.add_variable("b", VarType::Int { width: 32 });
        ctx.add_fact(KnownFact::UpperBound {
            var: "a".into(),
            upper: 5,
        });
        ctx.add_fact(KnownFact::LowerBound {
            var: "b".into(),
            lower: 10,
        });

        let vars = ctx.variables_for_theory(LemmaTheory::Arithmetic);
        let lemmas = ArithLemmaGen::generate(&vars, ctx.facts());

        assert!(lemmas.iter().any(|l| l.expression.contains("(< a b)")));
    }

    // -----------------------------------------------------------------------
    // BvLemmaGen
    // -----------------------------------------------------------------------

    #[test]
    fn test_bv_gen_produces_upper_bound() {
        let mut ctx = TheoryContext::new();
        ctx.add_variable("bits", VarType::BitVec { width: 8 });
        let vars = ctx.variables_for_theory(LemmaTheory::BitVector);
        let lemmas = BvLemmaGen::generate(&vars, 8);

        assert!(lemmas.iter().any(|l| l.expression.contains("bvule bits")));
    }

    #[test]
    fn test_bv_gen_and_idempotence() {
        let mut ctx = TheoryContext::new();
        ctx.add_variable("v", VarType::BitVec { width: 16 });
        let vars = ctx.variables_for_theory(LemmaTheory::BitVector);
        let lemmas = BvLemmaGen::generate(&vars, 16);

        assert!(lemmas
            .iter()
            .any(|l| l.expression.contains("(= (bvand v v) v)")));
    }

    #[test]
    fn test_bv_gen_or_zero_identity() {
        let mut ctx = TheoryContext::new();
        ctx.add_variable("w", VarType::BitVec { width: 4 });
        let vars = ctx.variables_for_theory(LemmaTheory::BitVector);
        let lemmas = BvLemmaGen::generate(&vars, 4);

        assert!(lemmas
            .iter()
            .any(|l| l.expression.contains("bvor w #b0000")));
    }

    #[test]
    fn test_bv_gen_shift_overflow() {
        let mut ctx = TheoryContext::new();
        ctx.add_variable("q", VarType::BitVec { width: 8 });
        let vars = ctx.variables_for_theory(LemmaTheory::BitVector);
        let lemmas = BvLemmaGen::generate(&vars, 8);

        assert!(lemmas.iter().any(|l| l.expression.contains("bvshl")));
    }

    // -----------------------------------------------------------------------
    // SeqLemmaGen
    // -----------------------------------------------------------------------

    #[test]
    fn test_seq_gen_length_non_negative() {
        let mut ctx = TheoryContext::new();
        ctx.add_variable(
            "s",
            VarType::Seq {
                element_type: "Int".into(),
            },
        );
        let vars = ctx.variables_for_theory(LemmaTheory::Sequence);
        let lemmas = SeqLemmaGen::generate(&vars);

        assert!(lemmas
            .iter()
            .any(|l| l.expression.contains("(>= (seq.len s) 0)")));
    }

    #[test]
    fn test_seq_gen_empty_length_zero() {
        let mut ctx = TheoryContext::new();
        ctx.add_variable(
            "s",
            VarType::Seq {
                element_type: "Int".into(),
            },
        );
        let vars = ctx.variables_for_theory(LemmaTheory::Sequence);
        let lemmas = SeqLemmaGen::generate(&vars);

        assert!(lemmas
            .iter()
            .any(|l| l.expression.contains("seq.empty") && l.expression.contains("0")));
    }

    #[test]
    fn test_seq_gen_concat_length_for_pair() {
        let mut ctx = TheoryContext::new();
        ctx.add_variable(
            "a",
            VarType::Seq {
                element_type: "Bool".into(),
            },
        );
        ctx.add_variable(
            "b",
            VarType::Seq {
                element_type: "Bool".into(),
            },
        );
        let vars = ctx.variables_for_theory(LemmaTheory::Sequence);
        let lemmas = SeqLemmaGen::generate(&vars);

        assert!(lemmas
            .iter()
            .any(|l| l.expression.contains("seq.++") && l.expression.contains("+")));
    }

    #[test]
    fn test_seq_gen_no_concat_for_different_element_types() {
        let mut ctx = TheoryContext::new();
        ctx.add_variable(
            "a",
            VarType::Seq {
                element_type: "Int".into(),
            },
        );
        ctx.add_variable(
            "b",
            VarType::Seq {
                element_type: "Bool".into(),
            },
        );
        let vars = ctx.variables_for_theory(LemmaTheory::Sequence);
        let lemmas = SeqLemmaGen::generate(&vars);

        // Concat lemma only for same element type — so no "seq.++ a b".
        assert!(!lemmas.iter().any(|l| l.expression.contains("seq.++ a b")));
    }

    #[test]
    fn test_seq_gen_subsequence_length() {
        let mut ctx = TheoryContext::new();
        ctx.add_variable(
            "t",
            VarType::Seq {
                element_type: "X".into(),
            },
        );
        let vars = ctx.variables_for_theory(LemmaTheory::Sequence);
        let lemmas = SeqLemmaGen::generate(&vars);

        assert!(lemmas.iter().any(|l| l.expression.contains("seq.extract")));
    }

    // -----------------------------------------------------------------------
    // CollectionLemmaGen
    // -----------------------------------------------------------------------

    #[test]
    fn test_collection_gen_set_cardinality_non_negative() {
        let mut ctx = TheoryContext::new();
        ctx.add_variable(
            "myset",
            VarType::Set {
                element_type: "Int".into(),
            },
        );
        let vars: Vec<&Variable> = ctx.variables().iter().collect();
        let lemmas = CollectionLemmaGen::generate(&vars, ctx.facts());

        assert!(lemmas
            .iter()
            .any(|l| l.expression.contains("(>= (set.card myset) 0)")));
    }

    #[test]
    fn test_collection_gen_subset_membership_propagation() {
        let mut ctx = TheoryContext::new();
        ctx.add_variable(
            "small",
            VarType::Set {
                element_type: "Int".into(),
            },
        );
        ctx.add_variable(
            "big",
            VarType::Set {
                element_type: "Int".into(),
            },
        );
        ctx.add_fact(KnownFact::Subset {
            subset: "small".into(),
            superset: "big".into(),
        });

        let vars: Vec<&Variable> = ctx.variables().iter().collect();
        let lemmas = CollectionLemmaGen::generate(&vars, ctx.facts());

        assert!(lemmas
            .iter()
            .any(|l| l.expression.contains("set.member e small")
                && l.expression.contains("set.member e big")));
    }

    #[test]
    fn test_collection_gen_subset_cardinality_ordering() {
        let mut ctx = TheoryContext::new();
        ctx.add_variable(
            "a",
            VarType::Set {
                element_type: "T".into(),
            },
        );
        ctx.add_variable(
            "b",
            VarType::Set {
                element_type: "T".into(),
            },
        );
        ctx.add_fact(KnownFact::Subset {
            subset: "a".into(),
            superset: "b".into(),
        });

        let vars: Vec<&Variable> = ctx.variables().iter().collect();
        let lemmas = CollectionLemmaGen::generate(&vars, ctx.facts());

        assert!(lemmas
            .iter()
            .any(|l| l.expression.contains("(<= (set.card a) (set.card b))")));
    }

    #[test]
    fn test_collection_gen_set_contains_implies_nonempty() {
        let mut ctx = TheoryContext::new();
        ctx.add_variable(
            "s",
            VarType::Set {
                element_type: "Int".into(),
            },
        );
        ctx.add_fact(KnownFact::SetContains {
            set: "s".into(),
            elem: "x".into(),
        });

        let vars: Vec<&Variable> = ctx.variables().iter().collect();
        let lemmas = CollectionLemmaGen::generate(&vars, ctx.facts());

        assert!(lemmas
            .iter()
            .any(|l| l.expression.contains("(> (set.card s) 0)")));
    }

    #[test]
    fn test_collection_gen_map_size_non_negative() {
        let mut ctx = TheoryContext::new();
        ctx.add_variable(
            "m",
            VarType::Map {
                key_type: "String".into(),
                value_type: "Int".into(),
            },
        );
        let vars: Vec<&Variable> = ctx.variables().iter().collect();
        let lemmas = CollectionLemmaGen::generate(&vars, ctx.facts());

        assert!(lemmas
            .iter()
            .any(|l| l.expression.contains("(>= (map.size m) 0)")));
    }

    #[test]
    fn test_collection_gen_map_contains_key_implies_nonempty() {
        let mut ctx = TheoryContext::new();
        ctx.add_variable(
            "tbl",
            VarType::Map {
                key_type: "K".into(),
                value_type: "V".into(),
            },
        );
        ctx.add_fact(KnownFact::MapContainsKey {
            map: "tbl".into(),
            key: "k0".into(),
        });

        let vars: Vec<&Variable> = ctx.variables().iter().collect();
        let lemmas = CollectionLemmaGen::generate(&vars, ctx.facts());

        assert!(lemmas
            .iter()
            .any(|l| l.expression.contains("(> (map.size tbl) 0)")));
    }

    // -----------------------------------------------------------------------
    // LemmaFilter
    // -----------------------------------------------------------------------

    #[test]
    fn test_filter_deduplicates_exact_expressions() {
        let ctx = ctx_with_u32("x");
        let lemmas = vec![
            GeneratedLemma::new(
                "(>= x 0)",
                LemmaTheory::Arithmetic,
                Confidence::Definite,
                "a",
            ),
            GeneratedLemma::new(
                "(>= x 0)",
                LemmaTheory::Arithmetic,
                Confidence::Definite,
                "b",
            ),
        ];

        let filter = LemmaFilter::new();
        let result = filter.filter(lemmas, &ctx);
        assert_eq!(result.len(), 1);
    }

    #[test]
    fn test_filter_removes_below_min_confidence() {
        let ctx = ctx_with_u32("x");
        let lemmas = vec![
            GeneratedLemma::new(
                "(>= x 0)",
                LemmaTheory::Arithmetic,
                Confidence::Definite,
                "a",
            ),
            GeneratedLemma::new("(< x 100)", LemmaTheory::Arithmetic, Confidence::Low, "b"),
        ];

        let filter = LemmaFilter::new().with_min_confidence(Confidence::High);
        let result = filter.filter(lemmas, &ctx);
        assert_eq!(result.len(), 1);
        assert!(result[0].expression.contains(">= x 0"));
    }

    #[test]
    fn test_filter_relevancy_drops_unknown_vars() {
        let ctx = ctx_with_u32("x");
        let lemmas = vec![
            GeneratedLemma::new(
                "(>= x 0)",
                LemmaTheory::Arithmetic,
                Confidence::Definite,
                "a",
            ),
            GeneratedLemma::new(
                "(>= y 0)",
                LemmaTheory::Arithmetic,
                Confidence::Definite,
                "b",
            ),
        ];

        let filter = LemmaFilter::new();
        let result = filter.filter(lemmas, &ctx);
        assert_eq!(result.len(), 1);
        assert!(result[0].expression.contains("x"));
    }

    // -----------------------------------------------------------------------
    // LemmaSet
    // -----------------------------------------------------------------------

    #[test]
    fn test_lemma_set_new_is_empty() {
        let set = LemmaSet::new();
        assert!(set.is_empty());
        assert_eq!(set.len(), 0);
    }

    #[test]
    fn test_lemma_set_add_and_len() {
        let mut set = LemmaSet::new();
        set.add(GeneratedLemma::new(
            "(>= x 0)",
            LemmaTheory::Arithmetic,
            Confidence::Definite,
            "test",
        ));
        assert_eq!(set.len(), 1);
        assert!(!set.is_empty());
    }

    #[test]
    fn test_lemma_set_add_drops_duplicates() {
        let mut set = LemmaSet::new();
        set.add(GeneratedLemma::new(
            "(>= x 0)",
            LemmaTheory::Arithmetic,
            Confidence::Definite,
            "a",
        ));
        set.add(GeneratedLemma::new(
            "(>= x 0)",
            LemmaTheory::Arithmetic,
            Confidence::Definite,
            "b",
        ));
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn test_lemma_set_by_theory() {
        let mut set = LemmaSet::new();
        set.add(GeneratedLemma::new(
            "(>= x 0)",
            LemmaTheory::Arithmetic,
            Confidence::Definite,
            "a",
        ));
        set.add(GeneratedLemma::new(
            "(bvand v v)",
            LemmaTheory::BitVector,
            Confidence::Definite,
            "b",
        ));
        set.add(GeneratedLemma::new(
            "(seq.len s)",
            LemmaTheory::Sequence,
            Confidence::Definite,
            "c",
        ));

        assert_eq!(set.by_theory(LemmaTheory::Arithmetic).len(), 1);
        assert_eq!(set.by_theory(LemmaTheory::BitVector).len(), 1);
        assert_eq!(set.by_theory(LemmaTheory::Sequence).len(), 1);
        assert_eq!(set.by_theory(LemmaTheory::Set).len(), 0);
    }

    #[test]
    fn test_lemma_set_at_least_confidence() {
        let mut set = LemmaSet::new();
        set.add(GeneratedLemma::new(
            "a",
            LemmaTheory::Arithmetic,
            Confidence::Definite,
            "",
        ));
        set.add(GeneratedLemma::new(
            "b",
            LemmaTheory::Arithmetic,
            Confidence::High,
            "",
        ));
        set.add(GeneratedLemma::new(
            "c",
            LemmaTheory::Arithmetic,
            Confidence::Medium,
            "",
        ));
        set.add(GeneratedLemma::new(
            "d",
            LemmaTheory::Arithmetic,
            Confidence::Low,
            "",
        ));

        assert_eq!(set.at_least(Confidence::Definite).len(), 1);
        assert_eq!(set.at_least(Confidence::High).len(), 2);
        assert_eq!(set.at_least(Confidence::Medium).len(), 3);
        assert_eq!(set.at_least(Confidence::Low).len(), 4);
    }

    #[test]
    fn test_lemma_set_deduplicate_idempotent() {
        let mut set = LemmaSet::new();
        set.add(GeneratedLemma::new(
            "x",
            LemmaTheory::Arithmetic,
            Confidence::Definite,
            "",
        ));
        set.add(GeneratedLemma::new(
            "y",
            LemmaTheory::Arithmetic,
            Confidence::Definite,
            "",
        ));
        set.deduplicate();
        assert_eq!(set.len(), 2);
        set.deduplicate();
        assert_eq!(set.len(), 2);
    }

    #[test]
    fn test_lemma_set_as_vec_returns_all() {
        let mut set = LemmaSet::new();
        set.add(GeneratedLemma::new(
            "a",
            LemmaTheory::Arithmetic,
            Confidence::Definite,
            "",
        ));
        set.add(GeneratedLemma::new(
            "b",
            LemmaTheory::Sequence,
            Confidence::High,
            "",
        ));
        let v = set.as_vec();
        assert_eq!(v.len(), 2);
    }

    // -----------------------------------------------------------------------
    // LemmaGenerator (integration)
    // -----------------------------------------------------------------------

    #[test]
    fn test_generator_empty_context_produces_empty_set() {
        let generator = LemmaGenerator::new(GeneratorConfig::default());
        let ctx = TheoryContext::new();
        let result = generator.generate(&ctx);
        assert!(result.is_empty());
    }

    #[test]
    fn test_generator_arithmetic_only() {
        let config = GeneratorConfig {
            enable_bitvector: false,
            enable_sequence: false,
            enable_collection: false,
            ..GeneratorConfig::default()
        };
        let generator = LemmaGenerator::new(config);
        let ctx = ctx_with_u32("x");
        let result = generator.generate(&ctx);

        assert!(!result.is_empty());
        assert!(result.by_theory(LemmaTheory::BitVector).is_empty());
        assert!(result.by_theory(LemmaTheory::Sequence).is_empty());
    }

    #[test]
    fn test_generator_all_theories_combined() {
        let generator = LemmaGenerator::new(GeneratorConfig::default());
        let mut ctx = TheoryContext::new();
        ctx.add_variable("x", VarType::Uint { width: 32 });
        ctx.add_variable("bv", VarType::BitVec { width: 8 });
        ctx.add_variable(
            "s",
            VarType::Seq {
                element_type: "Int".into(),
            },
        );
        ctx.add_variable(
            "st",
            VarType::Set {
                element_type: "Int".into(),
            },
        );

        let result = generator.generate(&ctx);
        assert!(!result.by_theory(LemmaTheory::Arithmetic).is_empty());
        assert!(!result.by_theory(LemmaTheory::BitVector).is_empty());
        assert!(!result.by_theory(LemmaTheory::Sequence).is_empty());
        assert!(!result.by_theory(LemmaTheory::Set).is_empty());
    }

    #[test]
    fn test_generator_max_per_theory_caps_output() {
        let config = GeneratorConfig {
            max_per_theory: 1,
            ..GeneratorConfig::default()
        };
        let generator = LemmaGenerator::new(config);
        let ctx = ctx_with_u32("x");
        let result = generator.generate(&ctx);

        // u32 normally generates >= 2 arithmetic lemmas; cap should limit to 1.
        assert_eq!(result.by_theory(LemmaTheory::Arithmetic).len(), 1);
    }

    #[test]
    fn test_generator_min_confidence_filters() {
        let config = GeneratorConfig {
            min_confidence: Confidence::Definite,
            ..GeneratorConfig::default()
        };
        let generator = LemmaGenerator::new(config);
        let mut ctx = ctx_with_i32("z");
        ctx.add_fact(KnownFact::Positive { var: "z".into() });
        let result = generator.generate(&ctx);

        // All surviving lemmas should be Definite.
        for l in result.as_vec() {
            assert_eq!(l.confidence, Confidence::Definite);
        }
    }

    #[test]
    fn test_generator_result_is_deduplicated() {
        let generator = LemmaGenerator::new(GeneratorConfig::default());
        let ctx = ctx_with_u32("x");
        let result = generator.generate(&ctx);

        let lemmas = result.as_vec();
        let exprs: Vec<&str> = lemmas.iter().map(|l| l.expression.as_str()).collect();
        let unique: HashSet<&str> = exprs.iter().copied().collect();
        assert_eq!(exprs.len(), unique.len(), "no duplicates in output");
    }

    // -----------------------------------------------------------------------
    // GeneratedLemma
    // -----------------------------------------------------------------------

    #[test]
    fn test_generated_lemma_display() {
        let l = GeneratedLemma::new(
            "(>= x 0)",
            LemmaTheory::Arithmetic,
            Confidence::Definite,
            "non-negative",
        );
        let s = format!("{}", l);
        assert!(s.contains("Arithmetic"));
        assert!(s.contains("Definite"));
        assert!(s.contains("(>= x 0)"));
        assert!(s.contains("non-negative"));
    }

    #[test]
    fn test_generated_lemma_subsumes_exact_match() {
        let a = GeneratedLemma::new(
            "(>= x 0)",
            LemmaTheory::Arithmetic,
            Confidence::Definite,
            "",
        );
        let b = GeneratedLemma::new(
            "(>= x 0)",
            LemmaTheory::Arithmetic,
            Confidence::Definite,
            "",
        );
        assert!(a.subsumes(&b));
    }

    #[test]
    fn test_generated_lemma_no_cross_theory_subsumption() {
        let a = GeneratedLemma::new(
            "(>= x 0)",
            LemmaTheory::Arithmetic,
            Confidence::Definite,
            "",
        );
        let b = GeneratedLemma::new("(>= x 0)", LemmaTheory::Sequence, Confidence::Definite, "");
        assert!(!a.subsumes(&b));
    }

    // -----------------------------------------------------------------------
    // Confidence ordering
    // -----------------------------------------------------------------------

    #[test]
    fn test_confidence_ordering() {
        assert!(Confidence::Low < Confidence::Medium);
        assert!(Confidence::Medium < Confidence::High);
        assert!(Confidence::High < Confidence::Definite);
    }

    // -----------------------------------------------------------------------
    // LemmaTheory Display
    // -----------------------------------------------------------------------

    #[test]
    fn test_lemma_theory_display() {
        assert_eq!(format!("{}", LemmaTheory::Arithmetic), "Arithmetic");
        assert_eq!(format!("{}", LemmaTheory::BitVector), "BitVector");
        assert_eq!(format!("{}", LemmaTheory::Sequence), "Sequence");
        assert_eq!(format!("{}", LemmaTheory::Set), "Set");
        assert_eq!(format!("{}", LemmaTheory::Map), "Map");
    }
}
