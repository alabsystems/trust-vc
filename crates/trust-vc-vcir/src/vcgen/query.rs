//! Generated queries and checks.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! A [`Query`] asks one question: do the hypotheses entail the goal? It
//! mirrors trust-vc-core's one-goal query API (`trust_vc_core::query`), so
//! the translation is one-to-one (see `crate::solve`, feature `solve`). A
//! [`Check`] is one query together with what it checks and where, which is
//! what a producer needs to report a failure the way Verus does.

use crate::ids::{FnId, SiteId, SpanId};
use crate::stmt::{ClauseAttrs, InvariantKind};

use super::term::{Sort, Term};

/// A declared constant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Symbol {
    /// Solver name: lower-case ASCII, digits and single underscores.
    pub name: String,
    /// Its sort.
    pub sort: Sort,
    /// What the value is in the source, for counterexamples (`x`, `t.f`).
    pub display: String,
}

/// A declared function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    /// Solver name.
    pub name: String,
    /// Parameter sorts.
    pub params: Vec<Sort>,
    /// Result sort.
    pub ret: Sort,
}

/// `forall params. function(params) == body`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Definition {
    /// The defined function.
    pub function: String,
    /// Parameter names and sorts; the body's only free variables.
    pub params: Vec<(String, Sort)>,
    /// The defining term.
    pub body: Term,
}

/// Where a hypothesis comes from.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Source {
    /// A precondition of the function being checked.
    Requires,
    /// A user `assume`.
    Assume,
    /// An earlier assertion, assumed after its site.
    Assert,
    /// An earlier exec check (overflow, division by zero), assumed after its
    /// site as Verus does.
    CheckAssumed,
    /// An earlier precondition clause of the same call, assumed while the
    /// later clauses are checked.
    CallRequires,
    /// A postcondition of a callee, assumed after the call.
    CalleeEnsures,
    /// A branch condition on the path to the site.
    PathCondition,
    /// The value of a named intermediate value.
    Binding,
    /// A range fact of a typed value.
    TypeFact,
    /// A ground instance of one of Verus's arithmetic axioms.
    Axiom,
    /// A loop invariant, assumed at the start of an iteration or after the
    /// loop.
    LoopInvariant,
    /// The negated condition of a `while` loop, after the loop.
    LoopExit,
}

/// A labelled hypothesis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Hypothesis {
    /// Unique within the query.
    pub label: String,
    /// Where it comes from.
    pub source: Source,
    /// A `Bool` term.
    pub term: Term,
}

/// One question for the solver.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Query {
    /// Conjunction of the complete32/64 ordinary verification contexts.
    /// Both cases are admitted before either is solved. Children may be
    /// scalar or isolated BV questions, but may not nest another batch.
    pub architectures: Option<Vec<(u32, Query)>>,
    /// A separately typed, isolated BV question. When present, all scalar
    /// inventories must be empty and `goal` must be the unused `false`
    /// sentinel. Admission rejects mixed encodings before either solver.
    /// One case for a fixed architecture, or both distinct 32/64 cases. The
    /// whole batch is one source obligation, proved only if every case is.
    pub bitvector: Option<Vec<crate::bitvector::Query>>,
    /// Nominal carrier identities, indexed by `Sort::Nominal`. Each is a
    /// complete `Ty::Adt`, preserving declaration identity and type arguments.
    /// No field, constructor, layout or private axiom is declared by a row.
    pub nominal_types: Vec<crate::Ty>,
    /// Declared constants.
    pub symbols: Vec<Symbol>,
    /// Declared functions.
    pub functions: Vec<Function>,
    /// Definitions of declared functions.
    pub definitions: Vec<Definition>,
    /// Facts assumed true.
    pub hypotheses: Vec<Hypothesis>,
    /// The `Bool` term to prove.
    pub goal: Term,
}

/// What a check establishes, with the positions a producer needs to report
/// its failure.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CheckKind {
    /// A user assertion.
    Assert {
        /// The asserted expression.
        span: SpanId,
        /// Its proof note or custom error.
        attrs: ClauseAttrs,
    },
    /// An isolated bit-vector assertion. Its failure belongs to the original
    /// assertion statement rather than an ordinary assertion clause.
    BitvectorAssert {
        /// The original isolated assertion statement.
        span: SpanId,
        /// Live translation of some requires/ensures in this assertion
        /// resolved pointer width under the default architecture setting.
        /// This is diagnostic metadata, never query or ownership authority.
        architecture_specialized: bool,
    },
    /// An explicit precondition of an isolated BV assertion, checked in
    /// the surrounding mathematical proof before the isolated question.
    BitvectorRequires {
        /// The original `requires` expression.
        span: SpanId,
    },
    /// One precondition clause of a callee, at a call.
    Precondition {
        /// The call.
        call: SpanId,
        /// The callee.
        callee: FnId,
        /// Index into the callee's `requires`.
        clause: usize,
    },
    /// The caller's entry-state unwind promise must imply the callee's
    /// promise at the actual call arguments.
    Unwind {
        /// The call being checked, at its existing call site.
        call: SpanId,
        /// The callee whose unwind contract is required.
        callee: FnId,
    },
    /// Optional failed-function diagnostic at an actual Spec call. This
    /// never enters the normal obligation set or supplies an assumed fact.
    Recommendation {
        call: SpanId,
        callee: FnId,
        clause: usize,
    },
    /// Auxiliary choose-existence diagnostic; never a normal proof premise.
    ChoiceRecommendation { span: SpanId },
    /// One postcondition clause, at an exit of the function.
    Postcondition {
        /// The exit: the returned expression, or the `return`.
        exit: SpanId,
        /// Index into the function's `ensures`.
        clause: usize,
    },
    /// An exec operation whose exact result must fit its type.
    Overflow {
        /// The operation.
        span: SpanId,
    },
    /// An exec division or remainder whose divisor must not be zero.
    DivByZero {
        /// The operation.
        span: SpanId,
    },
    /// One loop invariant, where it must hold.
    LoopInvariant {
        /// Where.
        at: InvariantAt,
        /// The invariant clause.
        invariant: SpanId,
        /// Its kind.
        kind: InvariantKind,
    },
    /// A recursive call: the callee's measure at the arguments must be below
    /// the caller's measure at entry (Verus's `check_decrease`, reported as
    /// "could not prove termination").
    Termination {
        /// The call.
        call: SpanId,
        /// The callee.
        callee: FnId,
    },
    /// A loop's `decreases` measure must have decreased.
    LoopDecreases {
        /// The loop, for the end of its body, or the `continue`.
        span: SpanId,
        /// At a `continue` rather than at the end of the body.
        at_continue: bool,
    },
}

/// Where a loop invariant is checked.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InvariantAt {
    /// Before the loop.
    Entry,
    /// At the end of the body.
    End,
    /// Where the loop is left: a `break`, or the condition of a `while`.
    Break(SpanId),
    /// At a `continue`.
    Continue(SpanId),
}

/// Which of a function's solver queries a check belongs to. Verus checks
/// the body of a loop with `loop_isolation` in a query of its own; it runs
/// those queries first, each when the loop's body is done (inner loops
/// before outer ones), and the function body's query last. Its limit on
/// reported errors applies per query.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum QueryGroup {
    /// The query of the loop whose body is the `index`-th to be completed.
    Loop {
        /// Completion order, from 0.
        index: u32,
        /// The loop's header.
        span: SpanId,
    },
    /// An isolated BV assertion has its own error-reporting query group.
    Bitvector {
        /// Order of the isolated assertions in the function.
        index: u32,
        /// The source assertion.
        span: SpanId,
    },
    /// The function body's query.
    Body,
}

/// One checked obligation of a function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Check {
    /// The site in the function's VcIR.
    pub site: SiteId,
    /// What is checked.
    pub kind: CheckKind,
    /// The question.
    pub query: Query,
    /// True when the query stands in uninterpreted functions for something
    /// Verus reasons about more precisely (products and quotients of two
    /// non-constant values). A proof of such a query is sound; a refutation
    /// may be spurious and is not a verdict.
    pub approximate: bool,
    /// True when the query leaves uninterpreted a spec function whose
    /// definition Verus may have emitted before checking the function
    /// ([`crate::DefOrder::Unknown`]). A proof holds either way; a
    /// refutation may be spurious and is not a verdict.
    pub order_unknown: bool,
    /// The query the check belongs to in Verus's encoding.
    pub group: QueryGroup,
}

/// A construct the generator does not handle; the function is not checked.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VcRefusal {
    /// Lowercase words joined by dashes.
    pub tag: &'static str,
    /// What exactly was not handled.
    pub detail: String,
    /// Where.
    pub span: SpanId,
}

/// What the generator produced for one function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FnVcs {
    /// A spec function: nothing to check. Its definition, if it has one, is
    /// available to the queries of other functions.
    Spec,
    /// `#[verifier::external_body]`: the body is not checked and the
    /// contract is trusted by callers.
    Trusted,
    /// A bodyless trait method or an imported specification signature:
    /// nothing is counted as verified. Trait clauses are checked where
    /// used; the initial imported fragment has no contract clauses.
    Declared,
    /// An instance of a generic function ([`crate::FnRole::Instance`]):
    /// the generic function is checked, the instance is not.
    Instance,
    /// A `decreases_by` proof function ([`crate::FnAttrs::is_decreases_by`]):
    /// Verus does not check it on its own; its body is checked inside the
    /// termination check of the spec function that names it.
    Inlined,
    /// Every checked site of the body, in program order.
    Checks(Vec<Check>),
    /// Not checked.
    Refused(VcRefusal),
}

/// The generator's output for one crate: one entry per function, in the
/// crate's order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CrateVcs {
    /// Functions and what was generated for each.
    pub fns: Vec<(FnId, FnVcs)>,
}

impl CrateVcs {
    /// The entry of `id`.
    #[must_use]
    pub fn get(&self, id: FnId) -> Option<&FnVcs> {
        self.fns
            .iter()
            .find(|(fn_id, _)| *fn_id == id)
            .map(|(_, vcs)| vcs)
    }
}

impl std::fmt::Display for Query {
    /// SMT-LIB-like text, for dumps and debugging.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(cases) = &self.architectures {
            for (width, query) in cases {
                writeln!(f, "; complete architecture {width}")?;
                writeln!(f, "{query}")?;
            }
            return Ok(());
        }
        if let Some(query) = &self.bitvector {
            return write!(f, "(isolated-bitvector {query:?})");
        }
        let sort = |s: Sort| match s {
            Sort::Bool => "Bool".to_string(),
            Sort::Int => "Int".to_string(),
            Sort::Nominal(index) => format!("nominal{index}"),
            Sort::Poly => "Poly".to_string(),
            Sort::TypeId => "poly_type".to_string(),
            Sort::Decoration => "poly_dec".to_string(),
        };
        for s in [Sort::Poly, Sort::TypeId, Sort::Decoration] {
            if self.symbols.iter().any(|symbol| symbol.sort == s)
                || self
                    .functions
                    .iter()
                    .any(|function| function.ret == s || function.params.contains(&s))
            {
                writeln!(f, "(declare-sort {} 0)", sort(s))?;
            }
        }
        for (index, ty) in self.nominal_types.iter().enumerate() {
            writeln!(f, "(declare-sort nominal{index} 0) ; {ty:?}")?;
        }
        for symbol in &self.symbols {
            writeln!(
                f,
                "(declare-const {} {}) ; {}",
                symbol.name,
                sort(symbol.sort),
                symbol.display
            )?;
        }
        for function in &self.functions {
            let params: Vec<String> = function.params.iter().map(|p| sort(*p)).collect();
            writeln!(
                f,
                "(declare-fun {} ({}) {})",
                function.name,
                params.join(" "),
                sort(function.ret)
            )?;
        }
        for def in &self.definitions {
            let params: Vec<String> = def
                .params
                .iter()
                .map(|(name, s)| format!("({name} {})", sort(*s)))
                .collect();
            writeln!(
                f,
                "(define {} ({}) {})",
                def.function,
                params.join(" "),
                def.body
            )?;
        }
        for hypothesis in &self.hypotheses {
            writeln!(
                f,
                "(assume {} {:?} {})",
                hypothesis.label, hypothesis.source, hypothesis.term
            )?;
        }
        writeln!(f, "(goal {})", self.goal)
    }
}
