//! One-goal solver queries for program-level verification-condition generators.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! A program-level VC generator reduces every checked site of a function to
//! one question: do these hypotheses entail this goal? This module answers
//! exactly that question. It sits below `VerificationContext`: there is no
//! obligation stream, no plan keyed on obligation names and no stop at the
//! first failure. A [`Query`] holds
//!
//! * declared symbols (the SSA values of the unit),
//! * uninterpreted functions, optionally with definitional equations,
//! * labelled hypotheses, each tagged with where it came from,
//! * exactly one goal,
//!
//! and [`check`] returns a [`Verdict`] for that goal alone.
//!
//! Terms are [`TrustVcExpr`] and are encoded by the typed IR encoder; the
//! solve runs on ay through the engine's check-sat envelope, model validation
//! and unknown classification (see `encoder::verification::query`).
//!
//! # Admission
//!
//! A query is checked before anything reaches the solver. Anything outside the
//! admitted fragment is an [`Verdict::Error`], never a silently weaker
//! question:
//!
//! * Names are plain lower-case identifiers (see [`is_admitted_name`]). The
//!   encoder gives meaning to some name shapes (`__` prefixes and suffixes),
//!   so a query never uses them.
//! * Symbols are `Bool`, `MathInt`, `Nat` (with its `>= 0` fact), or an
//!   explicitly declared nominal sort. Nominal sorts use `NamedCarrier(name)`
//!   as the typed encoder's named carrier, without registering any
//!   datatype, constructor, selector, field or axiom. They support equality,
//!   conditional values and uninterpreted calls, never integer operations.
//! * Expressions are the scalar fragment: literals, variables, `+ - * / %`
//!   over `MathInt` (division and remainder are Euclidean, as in Verus spec
//!   code), comparisons, `&& || ! ==>`, `if`, `let` and calls of declared
//!   functions. Machine integers never appear: a VC generator models them as
//!   `MathInt` values with explicit range hypotheses, which is Verus's
//!   encoding and keeps the bit-vector theory out of scalar code.
//! * Every expression must type-check, including the `ty` annotations the
//!   encoder relies on.
//!
//! # Definitions
//!
//! A [`Definition`] states `forall params. f(params) == body`. The caller is
//! responsible for that equation being true (for a spec function, that its
//! definition is admitted, for example because it terminates). The query
//! instantiates the equation at every call of `f` that occurs in the
//! hypotheses or the goal, and again at calls inside the instances, for at
//! most [`Limits::unfold_rounds`] rounds. Instances are sound hypotheses, so
//! they can only turn a question into `Proved` legitimately. When the rounds
//! run out with calls still uninstantiated, a satisfying assignment may
//! violate the definition at those calls, so a `sat` answer is then reported
//! as `Unknown` rather than `Refuted`.

mod admit;
#[cfg(test)]
mod bitvector_tests;
mod unfold;

use crate::encoder::UnknownCategory;
use crate::ir::{TrustVcExpr, TrustVcType};

/// A declared solver constant: one SSA value of the unit being checked.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Symbol {
    /// Solver name. Must satisfy [`is_admitted_name`].
    pub name: String,
    /// `Bool`, `MathInt`, `Nat` or a registered `NamedCarrier`.
    pub ty: TrustVcType,
    /// Name shown for this symbol in a counterexample (for example `x` for
    /// the SSA value `x_2`).
    pub display: String,
}

impl Symbol {
    /// A symbol whose display name is its solver name.
    #[must_use]
    pub fn new(name: impl Into<String>, ty: TrustVcType) -> Self {
        let name = name.into();
        Self {
            display: name.clone(),
            name,
            ty,
        }
    }

    /// A symbol with a separate display name.
    #[must_use]
    pub fn with_display(
        name: impl Into<String>,
        ty: TrustVcType,
        display: impl Into<String>,
    ) -> Self {
        Self {
            name: name.into(),
            ty,
            display: display.into(),
        }
    }
}

/// An uninterpreted function symbol.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    /// Solver name. Must satisfy [`is_admitted_name`] and differ from every
    /// symbol name.
    pub name: String,
    /// Parameter types, each scalar or a registered `NamedCarrier`.
    pub params: Vec<TrustVcType>,
    /// Result type, scalar or a registered `NamedCarrier`.
    pub ret: TrustVcType,
}

/// The definitional equation `forall params. function(params) == body`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Definition {
    /// The defined function; it must be declared in [`Query::functions`].
    pub function: String,
    /// Parameter names and types, matching the function's declaration.
    pub params: Vec<(String, TrustVcType)>,
    /// The body. Its free variables are exactly the parameters: a definition
    /// never mentions query symbols.
    pub body: TrustVcExpr,
}

/// Where a hypothesis came from. Carried through to
/// [`Verdict::Proved::used_hypotheses`] by label, so a verdict can say which
/// kinds of facts it rests on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum HypothesisSource {
    /// A precondition of the function being checked.
    Requires,
    /// A user `assume`.
    Assume,
    /// An earlier assertion of the same function, assumed after its own site.
    Assert,
    /// A postcondition of a callee, assumed after the call.
    CalleeEnsures,
    /// A branch condition on the path to the site.
    PathCondition,
    /// The value of an SSA definition (`x_2 == x_1 + 1`).
    Binding,
    /// A range or type fact (`0 <= x && x < 2^32` for a `u32` value).
    TypeFact,
    /// An instance of a [`Definition`], added by the query itself.
    Definition,
}

/// One labelled hypothesis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Hypothesis {
    /// A label unique within the query; reported back in
    /// [`Verdict::Proved::used_hypotheses`].
    pub label: String,
    /// Where the fact came from.
    pub source: HypothesisSource,
    /// A `Bool` expression.
    pub expr: TrustVcExpr,
}

impl Hypothesis {
    /// A hypothesis with the given label and source.
    #[must_use]
    pub fn new(label: impl Into<String>, source: HypothesisSource, expr: TrustVcExpr) -> Self {
        Self {
            label: label.into(),
            source,
            expr,
        }
    }
}

/// One solver question: do the hypotheses entail the goal?
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Query {
    /// A name for the question, used in diagnostics only.
    pub label: String,
    /// Distinct named uninterpreted carriers. A `NamedCarrier(name)` is
    /// admitted only when this registry contains `name`; names use the same
    /// restricted grammar as symbols and cannot alias built-in sorts.
    ///
    /// These are logical carriers, not a library/type authentication receipt.
    pub nominal_sorts: Vec<String>,
    /// Declared constants.
    pub symbols: Vec<Symbol>,
    /// Declared uninterpreted functions.
    pub functions: Vec<Function>,
    /// Definitional equations of declared functions.
    pub definitions: Vec<Definition>,
    /// Facts assumed true.
    pub hypotheses: Vec<Hypothesis>,
    /// The `Bool` expression to prove.
    pub goal: TrustVcExpr,
}

impl Query {
    /// A query with no declarations or hypotheses yet.
    #[must_use]
    pub fn new(label: impl Into<String>, goal: TrustVcExpr) -> Self {
        Self {
            label: label.into(),
            nominal_sorts: Vec::new(),
            symbols: Vec::new(),
            functions: Vec::new(),
            definitions: Vec::new(),
            hypotheses: Vec::new(),
            goal,
        }
    }
}

/// Resource bounds for one query.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limits {
    /// Wall-clock backstop for the solve, in milliseconds. It is a liveness
    /// bound; `conflicts` is the deterministic one.
    pub wall_ms: u64,
    /// Deterministic SAT-conflict budget. `None` uses the engine's default
    /// budget (it never means "unbounded").
    pub conflicts: Option<std::num::NonZeroU64>,
    /// Rounds of definition unfolding (see the module documentation).
    pub unfold_rounds: u32,
    /// Upper bound on the number of definition instances in one query.
    pub max_instances: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            wall_ms: 30_000,
            conflicts: None,
            unfold_rounds: 8,
            max_instances: 2_000,
        }
    }
}

/// One model value of a refuted query.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModelEntry {
    /// The symbol's display name.
    pub name: String,
    /// The solver name of the symbol.
    pub symbol: String,
    /// The rendered value.
    pub value: String,
}

/// The answer to one query.
#[derive(Debug, Clone, PartialEq)]
pub enum Verdict {
    /// The hypotheses entail the goal (the negated goal is unsatisfiable).
    Proved {
        /// Labels of the hypotheses in the solver's unsatisfiable core, when
        /// the solver produced one. The core is a sufficient set, not
        /// necessarily a minimal one.
        used_hypotheses: Option<Vec<String>>,
    },
    /// The solver found an assignment of the symbols that satisfies every
    /// hypothesis and falsifies the goal, and ay validated it.
    Refuted {
        /// Values of the declared symbols in that assignment.
        model: Vec<ModelEntry>,
    },
    /// No answer: resource limit, incompleteness, an unvalidated model, or an
    /// encoding approximation.
    Unknown {
        /// Human-readable reason.
        reason: String,
        /// Structured classification.
        category: UnknownCategory,
    },
    /// The query was not admitted or could not be encoded.
    Error {
        /// What was wrong.
        message: String,
    },
}

impl Verdict {
    /// True for [`Verdict::Proved`].
    #[must_use]
    pub fn is_proved(&self) -> bool {
        matches!(self, Self::Proved { .. })
    }

    /// True for [`Verdict::Refuted`].
    #[must_use]
    pub fn is_refuted(&self) -> bool {
        matches!(self, Self::Refuted { .. })
    }
}

/// Is `name` usable as a solver name in a query?
///
/// Admitted names start with a lower-case ASCII letter, continue with
/// lower-case ASCII letters, digits and single underscores, do not end with an
/// underscore, and are at most 64 bytes long. Double underscores are excluded
/// because the encoder reserves names built with them.
#[must_use]
pub fn is_admitted_name(name: &str) -> bool {
    let bytes = name.as_bytes();
    let Some(&first) = bytes.first() else {
        return false;
    };
    if bytes.len() > 64 || !first.is_ascii_lowercase() || name.ends_with('_') {
        return false;
    }
    if name.contains("__") {
        return false;
    }
    bytes
        .iter()
        .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || *b == b'_')
}

/// Check names, signatures and the complete scalar fragment without creating
/// a solver. A caller establishing several architecture cases can admit all
/// of them before starting either native solve.
pub fn validate(query: &Query) -> Result<(), String> {
    admit::admit(query).map(|_| ())
}

/// Answer one query.
///
/// Admission errors, encoding failures and solver panics are all reported in
/// the returned verdict; this function does not panic on malformed input.
#[must_use]
pub fn check(query: &Query, limits: &Limits) -> Verdict {
    let admitted = match admit::admit(query) {
        Ok(admitted) => admitted,
        Err(message) => return Verdict::Error { message },
    };
    let unfolded = match unfold::unfold(&admitted, limits) {
        Ok(unfolded) => unfolded,
        Err(message) => return Verdict::Error { message },
    };
    crate::encoder::solve_query(&unfolded, limits)
}

/// Answer an isolated, explicitly typed bit-vector query. Only this query's
/// own requires clauses are asserted; ordinary query hypotheses and function
/// definitions cannot cross the boundary. Uses the same native AY acceptance
/// and model-validation gates as [`check`].
#[must_use]
pub fn check_bitvector(query: &trust_vc_bitvector::Query, label: &str, limits: &Limits) -> Verdict {
    if let Err(message) = query.validate() {
        return Verdict::Error {
            message: format!("isolated BV query '{label}': {message}"),
        };
    }
    crate::encoder::solve_bitvector_query(query, label, limits)
}

/// A query that passed admission, with every `let` eliminated.
#[derive(Debug, Clone)]
pub(crate) struct AdmittedQuery {
    pub(crate) label: String,
    pub(crate) symbols: Vec<Symbol>,
    pub(crate) functions: Vec<Function>,
    pub(crate) definitions: Vec<Definition>,
    pub(crate) hypotheses: Vec<Hypothesis>,
    pub(crate) goal: TrustVcExpr,
}

/// A query ready for the solver: definition instances appended to the
/// hypotheses, and whether unfolding reached a fixpoint.
#[derive(Debug, Clone)]
pub(crate) struct UnfoldedQuery {
    pub(crate) label: String,
    pub(crate) symbols: Vec<Symbol>,
    pub(crate) functions: Vec<Function>,
    pub(crate) hypotheses: Vec<Hypothesis>,
    pub(crate) goal: TrustVcExpr,
    /// False when some call of a defined function has no instance.
    pub(crate) complete: bool,
}
