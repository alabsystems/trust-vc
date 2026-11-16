//! One function body to checks.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! The body is walked once, forward, in program order. The walk keeps
//!
//! * the current value of every local, as a [`Val`] over solver terms;
//! * the path condition (the branch conditions that lead to the current
//!   statement);
//! * a list of facts known so far, each guarded by the path condition under
//!   which it was learnt, so a fact from one branch says nothing about the
//!   other;
//! * which spec function definitions are revealed.
//!
//! At every checked site it emits one [`Check`]: all facts so far, the path
//! condition, and the site's condition as the goal. After an assertion or
//! an exec check the condition becomes a fact, as in Verus (a failure is
//! reported once, not again at every later site that depends on it).
//! Preconditions of a call, postconditions at an exit and the termination
//! of a recursive call do not become facts; after a call the callee's
//! postconditions do.
//!
//! Named values. A non-trivial value stored into a local gets a fresh
//! symbol and a binding fact (`path ==> x_3 == x_2 + 1`). Every symbol of a
//! bounded type also gets its range fact, unguarded. That is sound because a
//! bound symbol's value is in range whenever its path holds: machine values
//! are built from in-range values by clips and by checked operations, and a
//! checked operation's range condition is assumed after its check. The
//! order matters: a check's query is built before the value it guards is
//! bound, so the range fact never proves its own check.
//!
//! At the join of an `if`, a local that differs between the branches gets a
//! fresh symbol equal to each branch's value under that branch's path
//! condition, and the path goes on under the condition before the `if` and
//! either branch's own. A path that ended inside a branch (a `return`, a
//! `break`) does not join.
//!
//! Statements are walked as far as Verus keeps them in a block (see
//! `loops::live_prefix`). The ones after a `break` or `continue` statement
//! are kept there although no path reaches them; they are walked on a dead
//! path, whose condition is `false`.
//!
//! Loops follow Verus's encoding (`vir/src/sst_to_air.rs`, `StmX::Loop`).
//! The invariants that hold on entry are checked where the loop starts.
//! Every local the loop assigns then gets a fresh value of its type, and the
//! invariants that hold at an exit are assumed. Unlike an `assert`, which
//! `ast_to_sst.rs` follows with an assumption, a loop's invariant and
//! measure checks are not assumed after their site, so each failing one is
//! reported. A loop with isolation (the
//! default) has its body checked in a query of its own: the walk swaps the
//! facts out and starts the body from fresh values of every local, knowing
//! only their types and the invariants, and swaps the facts back after the
//! body. A loop without isolation is walked in the enclosing query from the
//! havocked values; the paths that `break` out of it join after it.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::ops::Not;

use crate::expr::{Expr, ExprKind, Place, Projection};
use crate::ids::{FnId, LocalId, LoopId, SiteId, SpanId};
use crate::item::{Body, DefOrder, FnDecl, LocalKind, Mode};
use crate::stmt::{Block, InvariantKind, Loop, Stmt, StmtKind};
use crate::ty::Ty;

use super::expr::{type_terms, PendingCheck, PendingKind, Reads, RecEvent, Tr, R};
use super::loops::{diverges, live_prefix, live_prefix_of, loop_infos, LoopInfo};
use super::quant::instantiate;

mod call_result;
mod loan_state;
mod loop_state;
mod unwind;
use super::query::{Check, CheckKind, Hypothesis, InvariantAt, Query, QueryGroup, Source, Symbol};
use super::relevance::{instance_gate, Analysis, CallRole, Position};
use super::spec::{inline, unfold, SpecDef, Tables, Unfoldable, NL_DIV, NL_MOD, NL_MUL};
use super::term::{Sort, Term};
use super::val::{refusal, Ctx, LeafTy, Shape, Val};

/// Upper bound on the term nodes inlining may add to one query.
const INLINE_BUDGET: usize = 200_000;

mod independent;
mod mut_refs;
mod owned_values;

/// The largest relevance condition written out in a fact; a larger one
/// stays a symbol with its definition.
const RELEVANCE_TERM_CAP: usize = 64;

/// A fact known from its point on, with its place in Verus's query.
#[derive(Debug, Clone)]
struct Fact {
    hypothesis: Hypothesis,
    position: Position,
}

/// The state of one path through the body.
#[derive(Debug, Clone, Default)]
struct Path {
    /// Branch conditions that lead here.
    guard: Vec<Term>,
    /// Locals declared on this path, including abstract storage with no value.
    declared: BTreeSet<LocalId>,
    /// Available typed values. A declaration alone cannot supply a Poly value.
    env: HashMap<LocalId, Val>,
    /// False once the path has returned.
    live: bool,
    moved: Vec<Place>,
    loans: Vec<mut_refs::Loan>,
    escaped_loans: Vec<Place>,
    resolved: Vec<Term>,
}

/// Generation state for one function.
pub(crate) struct Gen<'a> {
    ctx: &'a Ctx<'a>,
    tables: &'a Tables,
    decl: &'a FnDecl,
    symbols: Vec<Symbol>,
    facts: Vec<Fact>,
    /// Whether the current query has passed a case split of Verus's
    /// query (a check, or a branch): every fact from here on sits behind
    /// it.
    split: bool,
    checks: Vec<Check>,
    /// Entry value of every parameter.
    entry: HashMap<LocalId, Val>,
    /// The term standing for each type parameter.
    types: super::type_encoding::TypeEnv,
    /// Spec functions whose definition is revealed, with their fuel (1
    /// unless `reveal_with_fuel` gave more).
    visible: BTreeMap<FnId, u32>,
    /// The function whose query the checks belong to: the function itself,
    /// or the spec function whose termination a `decreases_by` body helps
    /// prove. Its definition order and its group decide which spec
    /// definitions the queries see.
    owner: FnId,
    /// The caller's measure at entry, when its recursive calls are checked
    /// to terminate.
    measure: Option<Vec<Term>>,
    /// Counter for the sites of termination checks in spec code, which has
    /// no sites of its own.
    next_spec_site: u32,
    /// Walking a proof block of a spec function's body for its termination
    /// check, where Verus checks the recursive calls in spec expressions
    /// too; those are not generated, so they are refused.
    in_proof_in_spec: bool,
    /// How many loop iterations enclose the current statement.
    loop_depth: u32,
    /// Set once a statement that is not a header ([`is_header`]) has been
    /// generated.
    started: bool,
    /// How many ghost blocks enclose the current statement.
    ghost_depth: u32,
    /// Counters for fresh names. They are `u64` and wrap rather than panic;
    /// one function would need 2^64 names to repeat one.
    next_symbol: u64,
    next_label: u64,
    /// The spec functions visible after the function's header statements:
    /// what a loop's own query starts from.
    header_visible: Option<BTreeMap<FnId, u32>>,
    /// Facts about the function's loops.
    loop_info: HashMap<LoopId, LoopInfo>,
    /// The loops around the current statement, innermost last.
    loops: Vec<LoopFrame<'a>>,
    /// The query checks go to: 0 for the body, else a loop's provisional
    /// number (see [`Self::finish_groups`]).
    group: u32,
    /// Provisional numbers of the loop queries in the order they were
    /// completed, with the loop's header.
    groups_done: Vec<(u32, SpanId)>,
    next_group: u32,
    next_bitvector_group: u32,
    independent: independent::Queries<'a>,
    /// A separate followup which emits only optional domain diagnostics.
    recommendations: bool,
    /// One existing-size grant for the entire auxiliary function traversal.
    recommendation_work: std::rc::Rc<std::cell::Cell<usize>>,
    /// Derived index of actual fresh binder names; no inventory rescans.
    recommendation_symbols: HashMap<String, LeafTy>,
    resolution: super::resolution::Plan,
    classifier: super::resolution::Classifier<'a, 'a>,
    reference_aliases: HashMap<Term, Term>,
    /// These modes depend only on this immutable declaration and Ctx layouts.
    ownership_modes: std::cell::RefCell<HashMap<Place, bool>>,
}

/// A loop around the current statement.
struct LoopFrame<'a> {
    lp: &'a Loop,
    /// Indices of the invariants that hold at the start of an iteration.
    entry_invs: Vec<usize>,
    /// Indices of the invariants that hold where the loop is left.
    exit_invs: Vec<usize>,
    /// The measure at the start of the iteration.
    measure: Vec<Term>,
    /// The query the loop's body is checked in.
    group: u32,
    /// Without isolation: the paths that left the loop.
    breaks: Vec<Path>,
}

/// What a loop's own query replaces while its body is walked.
struct Saved {
    facts: Vec<Fact>,
    split: bool,
    entry: HashMap<LocalId, Val>,
    visible: BTreeMap<FnId, u32>,
    measure: Option<Vec<Term>>,
    loop_depth: u32,
    group: u32,
}

impl<'a> Gen<'a> {
    pub(crate) fn new(ctx: &'a Ctx<'a>, tables: &'a Tables, decl: &'a FnDecl) -> Self {
        let visible = tables
            .defs
            .keys()
            .chain(tables.rec_defs.keys())
            .copied()
            .filter(|id| ctx.fns.get(id).is_some_and(|f| !f.attrs.opaque))
            .map(|id| (id, 1))
            .collect();
        Self {
            ctx,
            tables,
            decl,
            symbols: Vec::new(),
            facts: Vec::new(),
            split: false,
            checks: Vec::new(),
            entry: HashMap::new(),
            types: super::type_encoding::TypeEnv::default(),
            visible,
            owner: decl.id,
            measure: None,
            next_spec_site: u32::MAX,
            in_proof_in_spec: false,
            loop_depth: 0,
            started: false,
            ghost_depth: 0,
            next_symbol: 0,
            next_label: 0,
            header_visible: None,
            loop_info: loop_infos(decl),
            loops: Vec::new(),
            group: 0,
            groups_done: Vec::new(),
            next_group: 1,
            next_bitvector_group: 0,
            independent: independent::Queries::capture(decl),
            recommendations: false,
            recommendation_work: std::rc::Rc::new(std::cell::Cell::new(INLINE_BUDGET)),
            recommendation_symbols: HashMap::new(),
            resolution: super::resolution::Plan::default(),
            classifier: super::resolution::Classifier::new(ctx, decl),
            reference_aliases: HashMap::new(),
            ownership_modes: std::cell::RefCell::new(HashMap::new()),
        }
    }

    pub(crate) fn for_recommendations(mut self) -> Self {
        self.recommendations = true;
        self
    }

    /// Check a dual constant's actual initializer independently of its value
    /// definition. No fact equating its own value is assumed here.
    pub(crate) fn run_constant(mut self) -> R<Vec<Check>> {
        let Body::Constant(expression) = &self.decl.body else {
            return Err(refusal(
                "vcgen-internal",
                "a missing constant initializer",
                self.decl.span,
            ));
        };
        self.types = self.fresh_types(self.decl)?;
        self.visible.remove(&self.decl.id);
        let reads = Reads {
            types: self.types.clone(),
            ..Reads::default()
        };
        let mut tr = Tr::new(self.ctx, &self.tables.sigs, &self.tables.functions, &reads)
            .with_recommendations(self.recommendations)
            .with_recommendation_work(self.recommendation_work.clone());
        let value = tr.expr(expression)?;
        self.called_ok(&tr.called)?;
        let path = Path {
            guard: Vec::new(),
            declared: Default::default(),
            env: HashMap::new(),
            live: true,
            ..Path::default()
        };
        self.pending(&path, tr.checks)?;
        let signature = self.tables.sigs.get(&self.decl.id).ok_or_else(|| {
            refusal(
                "vcgen-internal",
                "a missing constant signature",
                expression.span,
            )
        })?;
        if !value.matches(&signature.result) {
            return Err(refusal(
                "vcgen-internal",
                "a constant result of the wrong shape",
                expression.span,
            ));
        }
        let mut leaves = Vec::new();
        value.leaves(&mut leaves);
        for (output, term) in signature.outputs.iter().zip(leaves) {
            let predicate = self
                .ctx
                .type_fact(output.leaf, &self.types, &term, expression.span)?;
            if predicate != Term::Bool(true) {
                let site = SiteId(self.next_spec_site);
                self.next_spec_site = self.next_spec_site.checked_sub(1).ok_or_else(|| {
                    refusal(
                        "vcgen-internal",
                        "too many constant result checks",
                        expression.span,
                    )
                })?;
                self.check(
                    &path,
                    &[],
                    predicate,
                    site,
                    CheckKind::Overflow {
                        span: expression.span,
                    },
                    Vec::new(),
                )?;
            }
        }
        self.finish_groups()
    }

    /// Generate the checks of an exec or proof function with a body.
    pub(crate) fn run(mut self) -> R<Vec<Check>> {
        let decl = self.decl;
        let Body::Stmts(block) = &decl.body else {
            return Err(refusal(
                "vcgen-internal",
                "a body that is not statements",
                decl.span,
            ));
        };
        // A `&mut` is only modelled as the whole type of a parameter: its
        // referent has an entry value and a current value. Anywhere else
        // (inside a tuple, in a local) it is not.
        for (index, local) in decl.locals.iter().enumerate() {
            let nested = match &local.ty {
                Ty::Ref {
                    mutable: true,
                    inner,
                } if local.kind == LocalKind::Param => contains_mut_ref(inner),
                ty => contains_mut_ref(ty),
            };
            if nested {
                return Err(refusal(
                    "nested-mut-ref",
                    format!(
                        "local {index} (`{}`) holds a `&mut` the generator does not model",
                        local.name
                    ),
                    local.span,
                ));
            }
        }
        self.resolution = super::resolution::analyze(self.ctx, decl, block, &self.classifier)?;
        // Each type parameter stands for some type: an arbitrary term.
        self.types = self.fresh_types(decl)?;
        for param in &decl.params {
            let local = decl
                .local(*param)
                .ok_or_else(|| refusal("vcgen-internal", "a missing parameter", decl.span))?;
            let shape = self.ctx.shape(&local.ty, self.types.owner(), local.span)?;
            let value = self.fresh(&shape, &local.name)?;
            self.entry.insert(*param, value);
        }
        let reads = Reads {
            read: self.entry.clone(),
            old: self.entry.clone(),
            types: self.types.clone(),
            ..Reads::default()
        };
        let mut path = Path {
            guard: Vec::new(),
            declared: self.entry.keys().copied().collect(),
            env: self.entry.clone(),
            live: true,
            ..Path::default()
        };
        for clause in &decl.requires {
            // Verus rejects a precondition that reads through a `&mut`
            // parameter without `old` (there is no current value yet).
            if any_expr(&clause.expr, &|e| match &e.kind {
                ExprKind::Read(place) => self.is_mut_ref_param(place.local),
                _ => false,
            }) {
                return Err(refusal(
                    "mut-ref-requires",
                    "a precondition that reads a `&mut` parameter without `old`",
                    clause.span,
                ));
            }
            let term = self.spec_term(&path, &reads, &clause.expr)?;
            self.fact(&[], Source::Requires, term);
        }
        self.measure = self.entry_measure(decl, &reads)?;
        if self.recommendations {
            for component in &decl.decreases {
                self.recommendation_measure(&path, &reads, component)?;
            }
            if let Some(condition) = decl.unwind_spec().condition() {
                self.recommendation_measure(&path, &reads, condition)?;
            }
        }
        self.block(&mut path, block)?;
        if path.live {
            return Err(refusal(
                "fall-through",
                "a path reaches the end of the body without a return",
                decl.span,
            ));
        }
        self.finish_groups()
    }

    /// Give every check its query in Verus's order: the loop queries in the
    /// order their bodies were completed, then the body's.
    fn finish_groups(mut self) -> R<Vec<Check>> {
        // No required isolated source event may disappear in an ordinary
        // width/reachability context, even when BOTH contexts would omit it.
        self.independent.finish()?;
        let mut order: HashMap<u32, QueryGroup> = HashMap::new();
        for (index, (group, span)) in self.groups_done.iter().enumerate() {
            let index = u32::try_from(index)
                .map_err(|_| refusal("vcgen-internal", "too many loops", self.decl.span))?;
            order.insert(*group, QueryGroup::Loop { index, span: *span });
        }
        for check in &mut self.checks {
            if let QueryGroup::Loop { index, .. } = check.group {
                check.group = *order.get(&index).ok_or_else(|| {
                    refusal(
                        "vcgen-internal",
                        "a check of an unfinished loop",
                        self.decl.span,
                    )
                })?;
            }
        }
        Ok(self.checks)
    }

    // ------------------------------------------------------------------
    // Symbols and facts
    // ------------------------------------------------------------------

    fn label(&mut self, prefix: &str) -> String {
        self.next_label = self.next_label.wrapping_add(1);
        format!("{prefix}{}", self.next_label)
    }

    fn fresh_symbol(&mut self, sort: super::term::Sort, display: &str) -> Term {
        let name = format!("v{}", self.next_symbol);
        self.next_symbol = self.next_symbol.wrapping_add(1);
        self.symbols.push(Symbol {
            name: name.clone(),
            sort,
            display: display.to_string(),
        });
        Term::var(name, sort)
    }

    fn fresh_types(&mut self, declaration: &FnDecl) -> R<super::type_encoding::TypeEnv> {
        use super::term::Sort;
        use super::type_encoding::{TypeArgument, TypeEnv};
        let mut arguments = Vec::new();
        for name in &declaration.type_params {
            let decoration = self.fresh_symbol(Sort::Decoration, &format!("decoration {name}"));
            let identity = self.fresh_symbol(Sort::TypeId, &format!("type {name}"));
            arguments.push(TypeArgument::new(decoration, identity).ok_or_else(|| {
                refusal(
                    "vcgen-internal",
                    "a malformed type-parameter environment",
                    declaration.span,
                )
            })?);
        }
        Ok(TypeEnv::new(declaration.id, arguments))
    }

    /// A fresh value with the predicate licensed by its actual binder scope.
    fn fresh_leaf_at(&mut self, leaf: LeafTy, display: &str, guard: &[Term]) -> R<Term> {
        let term = self.fresh_symbol(leaf.sort(), display);
        let fact = self
            .ctx
            .type_fact(leaf, &self.types, &term, self.decl.span)?;
        if fact != Term::Bool(true) {
            self.fact(
                if matches!(leaf, LeafTy::Poly(_)) {
                    guard
                } else {
                    &[]
                },
                Source::TypeFact,
                fact,
            );
        }
        Ok(term)
    }

    fn fresh(&mut self, shape: &Shape, display: &str) -> R<Val> {
        self.fresh_at(shape, display, &[])
    }

    fn fresh_at(&mut self, shape: &Shape, display: &str, guard: &[Term]) -> R<Val> {
        match shape {
            Shape::Leaf(leaf) => Ok(Val::Leaf(self.fresh_leaf_at(*leaf, display, guard)?)),
            Shape::Node(children) => children
                .iter()
                .enumerate()
                .map(|(i, child)| self.fresh_at(child, &format!("{display}.{i}"), guard))
                .collect::<R<Vec<_>>>()
                .map(Val::Node),
        }
    }

    /// Record `guard ==> term` as known from here on.
    fn fact(&mut self, guard: &[Term], source: Source, term: Term) {
        self.fact_gated(guard, source, term, None);
    }

    /// [`Self::fact`] for a formula of an instance Z3 makes during its
    /// search, with the instance's gate if it sits behind a case split
    /// ([`Position::gate`]).
    fn fact_gated(&mut self, guard: &[Term], source: Source, term: Term, gate: Option<Term>) {
        let term = term.guarded(guard);
        if term == Term::Bool(true) {
            return;
        }
        let label = self.label("h");
        self.facts.push(Fact {
            hypothesis: Hypothesis {
                label,
                source,
                term,
            },
            position: Position {
                late: self.split,
                gate,
            },
        });
    }

    /// Give every non-trivial leaf of `value` a name bound on the path.
    fn name_value(&mut self, path: &Path, value: Val, shape: &Shape, display: &str) -> R<Val> {
        match (value, shape) {
            (Val::Leaf(term), Shape::Leaf(_)) if term.is_atomic() => Ok(Val::Leaf(term)),
            (Val::Leaf(term), Shape::Leaf(leaf)) => {
                let symbol = self.fresh_leaf_at(*leaf, display, &path.guard)?;
                if symbol.sort() == Sort::Poly {
                    let origin = self.reference_origin(&term)?;
                    self.reference_aliases.insert(symbol.clone(), origin);
                }
                self.fact(&path.guard, Source::Binding, Term::eq(symbol.clone(), term));
                Ok(Val::Leaf(symbol))
            }
            (Val::Node(values), Shape::Node(shapes)) if values.len() == shapes.len() => {
                let mut out = Vec::new();
                for (i, (value, shape)) in values.into_iter().zip(shapes).enumerate() {
                    out.push(self.name_value(path, value, shape, &format!("{display}.{i}"))?);
                }
                Ok(Val::Node(out))
            }
            _ => Err(refusal(
                "vcgen-internal",
                "a value that does not fit its type",
                self.decl.span,
            )),
        }
    }

    // ------------------------------------------------------------------
    // Checks
    // ------------------------------------------------------------------

    /// Emit a check of `goal` at the current point of `path`, under the
    /// extra `guard`, with `extra` hypotheses for this check only.
    ///
    /// The query's terms are final: revealed spec functions are inlined,
    /// and every application of a function with a bounded result and every
    /// nonlinear stand-in gets its fact (see `super::spec`).
    fn check(
        &mut self,
        path: &Path,
        guard: &[Term],
        goal: Term,
        site: SiteId,
        kind: CheckKind,
        extra: Vec<(Source, Term)>,
    ) -> R<()> {
        if self.recommendations
            && !matches!(
                kind,
                CheckKind::Recommendation { .. } | CheckKind::ChoiceRecommendation { .. }
            )
        {
            // Upstream replaces ordinary assertions with assumptions in the
            // diagnostic pass. The statement walk still records those facts.
            return Ok(());
        }
        // Verus's query reaches the check behind a case split if it passed
        // one or is on a branch; whatever follows the check sits behind its
        // own.
        let late = self.split || !path.guard.is_empty() || !guard.is_empty() || !extra.is_empty();
        self.split = true;
        // Nothing reaches a site on a dead path.
        if is_dead(&path.guard) || is_dead(guard) {
            return Ok(());
        }
        if self.recommendations {
            // Bound repeated auxiliary query preparation before cloning a
            // growing prefix of state; the ordinary per-query admission still
            // runs unchanged below.
            super::inline_work::items(
                &self.recommendation_work,
                self.symbols.len() + self.facts.len(),
                self.decl.span,
            )?;
            super::inline_work::term(&self.recommendation_work, &goal, 1, self.decl.span)?;
            for fact in &self.facts {
                super::inline_work::term(
                    &self.recommendation_work,
                    &fact.hypothesis.term,
                    1,
                    self.decl.span,
                )?;
            }
            for condition in path.guard.iter().chain(guard) {
                super::inline_work::term(&self.recommendation_work, condition, 1, self.decl.span)?;
            }
        }
        let mut hypotheses = Vec::new();
        let mut positions = Vec::new();
        for fact in &self.facts {
            hypotheses.push(fact.hypothesis.clone());
            positions.push(fact.position.clone());
        }
        let behind = Position {
            late: true,
            gate: None,
        };
        for condition in path.guard.iter().chain(guard) {
            let label = self.label("p");
            hypotheses.push(Hypothesis {
                label,
                source: Source::PathCondition,
                term: condition.clone(),
            });
            positions.push(behind.clone());
        }
        for (source, term) in extra {
            let label = self.label("x");
            hypotheses.push(Hypothesis {
                label,
                source,
                term,
            });
            positions.push(behind.clone());
        }

        // Inline the revealed definitions that Verus has emitted by the
        // time it checks this function. The definitions of the members of
        // the function's own group come after its checks.
        let order = self.ctx.def_order(self.owner);
        let emitted = |id: &FnId| {
            !order.is_some_and(|order| order.contains_key(id))
                && !self.ctx.same_group(self.owner, *id)
        };
        let defs: HashMap<&str, &SpecDef> = self
            .visible
            .keys()
            .filter(|id| emitted(id))
            .filter_map(|id| self.tables.defs.get(id))
            .flatten()
            .map(|def| (def.function.as_str(), def))
            .collect();
        let unfoldable: Unfoldable<'_> = self
            .visible
            .iter()
            .filter(|(id, _)| emitted(id))
            .flat_map(|(id, fuel)| {
                self.tables
                    .rec_defs
                    .get(id)
                    .into_iter()
                    .flatten()
                    .map(move |rec| {
                        let depth = rec.cycle.saturating_add(fuel.saturating_sub(1));
                        (rec.spec_name.as_str(), (rec, depth))
                    })
            })
            .collect();
        // The revealed definitions whose place in Verus's order is unknown.
        let unknown: BTreeSet<&str> = order
            .into_iter()
            .flatten()
            .filter(|(id, why)| **why == DefOrder::Unknown && self.visible.contains_key(id))
            .flat_map(|(id, _)| {
                self.tables
                    .defs
                    .get(id)
                    .into_iter()
                    .flatten()
                    .map(|def| def.function.as_str())
                    .chain(
                        self.tables
                            .rec_defs
                            .get(id)
                            .into_iter()
                            .flatten()
                            .map(|r| r.spec_name.as_str()),
                    )
            })
            .collect();
        let mut budget = INLINE_BUDGET;
        let too_big = || {
            refusal(
                "inline-size",
                "spec function definitions expand beyond the size limit",
                self.decl.span,
            )
        };
        // The relevance analysis reads the terms as written: Z3 rewrites
        // them with the non-recursive spec functions still applications.
        let mut written: Vec<(Term, Position)> = hypotheses
            .iter()
            .zip(positions)
            .map(|(h, position)| (h.term.clone(), position))
            .collect();
        let written_goal = (goal.clone(), Position { late, gate: None });
        for hypothesis in &mut hypotheses {
            hypothesis.term = inline(&hypothesis.term, &defs, &mut budget).ok_or_else(too_big)?;
        }
        let goal = inline(&goal, &defs, &mut budget).ok_or_else(too_big)?;
        let mut symbols = self.symbols.clone();
        // Quantifiers and choices: their facts and instances, as Z3 makes
        // them (`super::quant`).
        let registry = self.ctx.quants.borrow();
        let quantified = hypotheses
            .iter()
            .map(|h| &h.term)
            .chain([&goal])
            .any(|term| registry.mentioned_in(term));
        if quantified {
            let found = instantiate(
                self.ctx,
                &registry,
                &written,
                &written_goal,
                &defs,
                self.tables,
            );
            symbols.extend(found.symbols);
            for (fact, position) in found.facts {
                let label = self.label("qi");
                let term = inline(&fact, &defs, &mut budget).ok_or_else(too_big)?;
                hypotheses.push(Hypothesis {
                    label,
                    source: Source::Axiom,
                    term,
                });
                written.push((fact, position));
            }
            for definition in found.definitions {
                let label = self.label("qd");
                hypotheses.push(Hypothesis {
                    label,
                    source: Source::Axiom,
                    term: definition,
                });
            }
        }
        // Recursive definitions, unfolded as far as Verus's fuel goes, at
        // the applications Z3 has relevant.
        let mentioned = !unfoldable.is_empty()
            && hypotheses
                .iter()
                .map(|h| &h.term)
                .chain([&goal])
                .any(|term| mentions(term, &unfoldable));
        if mentioned {
            let tables = self.tables;
            let role = |name: &str| {
                if unfoldable.contains_key(name) || tables.rec_def_named(name).is_some() {
                    CallRole::Collect
                } else if defs.contains_key(name) {
                    CallRole::Defined
                } else {
                    CallRole::Other
                }
            };
            let mut analysis = Analysis::new(&role, &defs, INLINE_BUDGET)
                .with_ranges(&tables.ranged)
                .with_typings(&tables.typings)
                .with_type_context(self.ctx)
                .with_result_families(&tables.families);
            let seeds = analysis
                .seeds(&written, &written_goal)
                .map_err(|_| too_big())?;
            let facts = unfold(
                seeds.into_items(),
                &unfoldable,
                tables,
                &defs,
                &mut analysis,
                &mut budget,
            )
            .ok_or_else(too_big)?;
            let mut resolved = analysis.namer.resolve(facts, RELEVANCE_TERM_CAP);
            symbols.append(&mut resolved.symbols);
            for fact in resolved.facts.into_iter().chain(resolved.definitions) {
                let label = self.label("fu");
                hypotheses.push(Hypothesis {
                    label,
                    source: Source::Axiom,
                    term: fact,
                });
            }
        }

        // Facts about the applications that occur.
        let mut instances: Vec<Term> = Vec::new();
        let mut approximate = false;
        let mut order_unknown = false;
        for term in hypotheses.iter().map(|h| &h.term).chain([&goal]) {
            term.for_each_call(&mut |name, args| {
                order_unknown |= unknown.contains(name);
                if let Some(fact) = super::bitwise::range_fact(name, args) {
                    if !instances.contains(&fact) {
                        instances.push(fact);
                    }
                }
                let call = || Term::call(name, args.to_vec(), Sort::Int);
                let range = self
                    .tables
                    .ranged
                    .get(name)
                    .copied()
                    .or_else(|| registry.range(name));
                let typed = self
                    .tables
                    .typings
                    .get(name)
                    .and_then(|schema| schema.instantiate(args));
                let fact = if let Some(fact) = typed {
                    Some(fact)
                } else if let Some((lo, hi)) = range {
                    Some(call().within_type_bounds(lo, hi))
                } else {
                    approximate |= matches!(name, NL_MUL | NL_DIV | NL_MOD);
                    nonlinear_axiom(name, args)
                };
                if let Some(fact) = fact {
                    if !instances.contains(&fact) {
                        instances.push(fact);
                    }
                }
            });
        }
        for fact in instances {
            let label = self.label("ax");
            hypotheses.push(Hypothesis {
                label,
                source: Source::Axiom,
                term: fact,
            });
        }
        let roots: Vec<&Term> = hypotheses
            .iter()
            .map(|hypothesis| &hypothesis.term)
            .chain([&goal])
            .collect();
        let bridge_axioms = self
            .ctx
            .bridge_axioms(&roots, &mut budget)
            .ok_or_else(too_big)?;
        for fact in bridge_axioms {
            let label = self.label("bx");
            hypotheses.push(Hypothesis {
                label,
                source: Source::Axiom,
                term: fact,
            });
        }
        // The atoms and choices the query applies.
        let mut functions = self.tables.functions.clone();
        functions.extend(self.ctx.type_functions());
        let mut declared: BTreeSet<String> = BTreeSet::new();
        for term in hypotheses.iter().map(|h| &h.term).chain([&goal]) {
            term.for_each_call(&mut |name, _| {
                if !declared.contains(name) {
                    if let Some(function) = registry.function(name) {
                        declared.insert(name.to_string());
                        functions.push(function);
                    }
                }
            });
        }
        drop(registry);
        let group = match self.group {
            0 => QueryGroup::Body,
            // Provisional until the loop is done (`finish_groups`).
            n => QueryGroup::Loop {
                index: n,
                span: self.decl.span,
            },
        };
        self.checks.push(Check {
            site,
            kind,
            query: Query {
                architectures: None,
                bitvector: None,
                nominal_types: self.ctx.nominal_types(),
                symbols,
                functions,
                definitions: Vec::new(),
                hypotheses,
                goal,
            },
            approximate,
            order_unknown,
            group,
        });
        Ok(())
    }

    /// Check the exec checks an expression produced, in order, and assume
    /// each after its site.
    fn pending(&mut self, path: &Path, pending: Vec<PendingCheck>) -> R<()> {
        for check in pending {
            self.declare_diagnostic_symbols(&check.diagnostic_symbols, &path.guard, check.span)?;
            let kind = match check.kind {
                PendingKind::Overflow => CheckKind::Overflow { span: check.span },
                PendingKind::DivByZero => CheckKind::DivByZero { span: check.span },
                PendingKind::Recommendation { callee, clause } => CheckKind::Recommendation {
                    call: check.span,
                    callee,
                    clause,
                },
                PendingKind::ChoiceRecommendation => {
                    CheckKind::ChoiceRecommendation { span: check.span }
                }
            };
            self.check(
                path,
                &check.guard,
                check.cond.clone(),
                check.site,
                kind,
                Vec::new(),
            )?;
            if !matches!(
                check.kind,
                PendingKind::Recommendation { .. } | PendingKind::ChoiceRecommendation
            ) {
                let mut guard = path.guard.clone();
                guard.extend(check.guard);
                self.fact(&guard, Source::CheckAssumed, check.cond);
            }
        }
        Ok(())
    }

    /// Arbitrary quantifier/choice locals are query constants, as in a40
    /// check_pure_expr_bind. They provide only actual type facts, never the
    /// quantified body, choice condition or a recommendation as an assumption.
    fn declare_diagnostic_symbols(
        &mut self,
        symbols: &[(String, LeafTy)],
        guard: &[Term],
        span: SpanId,
    ) -> R<()> {
        if !symbols.is_empty() && !self.recommendations {
            return Err(refusal(
                "vcgen-internal",
                "diagnostic binders in a normal proof",
                span,
            ));
        }
        for (name, leaf) in symbols {
            if let Some(prior) = self.recommendation_symbols.get(name) {
                if prior != leaf {
                    return Err(refusal(
                        "recommends-binder",
                        "a diagnostic binder changes type",
                        span,
                    ));
                }
            } else {
                // These are the actual Registry::fresh_val("qb") names, disjoint
                // from Gen's v/recursive-result namespaces. The finite shared
                // grant prevents the native fresh counter from wrapping here.
                self.declare(name, *leaf, "arbitrary recommendation binder", guard)?;
                self.recommendation_symbols.insert(name.clone(), *leaf);
            }
        }
        Ok(())
    }

    // ------------------------------------------------------------------
    // Expressions
    // ------------------------------------------------------------------

    /// Refuse if any spec function called has no usable definition.
    fn called_ok(&self, called: &BTreeSet<FnId>) -> R<()> {
        for id in called {
            if self.in_proof_in_spec
                && !self.recommendations
                && self.ctx.same_group(self.owner, *id)
            {
                return Err(refusal(
                    "proof-in-spec-recursion",
                    "a recursive call in a spec expression inside a proof block",
                    self.decl.span,
                ));
            }
            if let Some(problem) = self.tables.sigs.get(id).and_then(|sig| sig.problem.clone()) {
                return Err(problem);
            }
        }
        Ok(())
    }

    /// A callee's already declared contract is not a caller-written
    /// evaluation. Upstream's auxiliary body pass does not recheck recommends
    /// inside another Exec/Proof function's requires/ensures at every call.
    fn contract_term(&self, reads: &Reads, e: &Expr) -> R<Term> {
        let mut tr = Tr::new(self.ctx, &self.tables.sigs, &self.tables.functions, reads);
        if self.recommendations {
            tr = tr.with_auxiliary_work(self.recommendation_work.clone());
        }
        let term = tr.bool(e)?;
        self.called_ok(&tr.called)?;
        if !tr.checks.is_empty() {
            return Err(refusal(
                "vcgen-internal",
                "an exec check in spec code",
                e.span,
            ));
        }
        Ok(term)
    }

    fn recommendation_measure(&mut self, path: &Path, reads: &Reads, e: &Expr) -> R<()> {
        let mut tr = Tr::new(self.ctx, &self.tables.sigs, &self.tables.functions, reads)
            .with_recommendations(true)
            .with_recommendation_work(self.recommendation_work.clone());
        tr.expr(e)?;
        self.called_ok(&tr.called)?;
        if tr.checks.iter().any(|check| {
            !matches!(
                check.kind,
                PendingKind::Recommendation { .. } | PendingKind::ChoiceRecommendation
            )
        }) {
            return Err(refusal(
                "recommends-expression",
                "an execution check in a diagnostic decreases expression",
                e.span,
            ));
        }
        self.pending(path, tr.checks)
    }

    /// A spec expression (no exec checks) as a term.
    fn spec_term(&mut self, path: &Path, reads: &Reads, e: &Expr) -> R<Term> {
        let mut tr = Tr::new(self.ctx, &self.tables.sigs, &self.tables.functions, reads)
            .with_recommendations(self.recommendations)
            .with_recommendation_work(self.recommendation_work.clone());
        let term = tr.bool(e)?;
        self.called_ok(&tr.called)?;
        if tr.checks.iter().any(|check| {
            !matches!(
                check.kind,
                PendingKind::Recommendation { .. } | PendingKind::ChoiceRecommendation
            )
        }) {
            return Err(refusal(
                "vcgen-internal",
                "an exec check in spec code",
                e.span,
            ));
        }
        self.pending(path, tr.checks)?;
        Ok(term)
    }

    /// Reads of body code on `path`.
    fn body_reads(&self, path: &Path) -> R<Reads> {
        self.price_ownership_path(path, 1, self.decl.span)?;
        Ok(Reads {
            read: path.env.clone(),
            local_types: Reads::decl_types(self.decl),
            moved: path.moved.clone(),
            borrowed: self.active_borrows(path)?,
            old: self.entry.clone(),
            types: self.types.clone(),
        })
    }

    /// Check outer requirements, prove only the explicit isolated question,
    /// then retain the ordinary mathematical conclusions on the current path.
    fn assert_bitvector(
        &mut self,
        path: &Path,
        span: SpanId,
        requires: &[crate::Clause],
        ensures: &[crate::Clause],
        architecture: crate::bitvector::Architecture,
        site: SiteId,
    ) -> R<()> {
        if ensures.is_empty() || requires.len().saturating_add(ensures.len()) > INLINE_BUDGET {
            return Err(refusal(
                "bit-vector-clauses",
                "an empty or oversized isolated BV clause inventory",
                span,
            ));
        }
        architecture
            .cases()
            .map_err(|detail| refusal("bit-vector-architecture", detail, span))?;
        if architecture != self.ctx.architecture {
            return Err(refusal(
                "bit-vector-architecture",
                "an isolated assertion with a different source architecture",
                span,
            ));
        }
        let reads = self.body_reads(path)?;
        for clause in requires {
            let goal = self.spec_term(path, &reads, &clause.expr)?;
            self.check(
                path,
                &[],
                goal.clone(),
                site,
                CheckKind::BitvectorRequires { span: clause.span },
                Vec::new(),
            )?;
            self.fact(&path.guard, Source::Assert, goal);
        }
        if self.recommendations {
            for clause in ensures {
                let conclusion = self.spec_term(path, &reads, &clause.expr)?;
                if !clause.attrs.is_labelled() {
                    self.fact(&path.guard, Source::Assert, conclusion);
                }
            }
            return Ok(());
        }
        let group = QueryGroup::Bitvector {
            index: self.next_bitvector_group,
            span,
        };
        self.next_bitvector_group = self
            .next_bitvector_group
            .checked_add(1)
            .ok_or_else(|| refusal("bit-vector-budget", "too many isolated BV assertions", span))?;
        let requirements: Vec<&Expr> = requires.iter().map(|clause| &clause.expr).collect();
        // Translate every source clause before constructing any check. Width
        // consumption in ANY requires/ensures specializes the WHOLE assertion,
        // including a sibling clause whose own translation is fixed-width.
        let mut questions = Vec::new();
        let mut width_consumed = false;
        for clause in ensures {
            let (question, consumed) = super::bitvector::lower_detailed(
                self.ctx,
                &requirements,
                &clause.expr,
                &reads,
                self.ctx.pointer_width,
                Some(self.owner),
            )?;
            width_consumed |= consumed;
            questions.push(question);
        }
        let architecture_specialized =
            width_consumed && architecture == crate::bitvector::Architecture::Either32Or64;
        for question in questions {
            self.checks.push(Check {
                site,
                kind: CheckKind::BitvectorAssert {
                    span,
                    architecture_specialized,
                },
                query: Query {
                    architectures: None,
                    bitvector: Some(vec![question]),
                    nominal_types: Vec::new(),
                    symbols: Vec::new(),
                    functions: Vec::new(),
                    definitions: Vec::new(),
                    hypotheses: Vec::new(),
                    goal: Term::Bool(false),
                },
                approximate: false,
                order_unknown: false,
                group,
            });
        }
        // No native BV axiom is exported. The ordinary translator retains
        // pinned Poly/Int UF-and-clip terms for subsequent mathematical VCs.
        for clause in ensures {
            let conclusion = self.spec_term(path, &reads, &clause.expr)?;
            if !clause.attrs.is_labelled() {
                self.fact(&path.guard, Source::Assert, conclusion);
            }
        }
        Ok(())
    }

    /// Is `local` a parameter of `&mut` type?
    fn is_mut_ref_param(&self, local: LocalId) -> bool {
        self.decl.params.contains(&local)
            && self
                .decl
                .local(local)
                .is_some_and(|decl| matches!(decl.ty, Ty::Ref { mutable: true, .. }))
    }

    /// An expression of body code, with its exec checks decided.
    fn body_expr(&mut self, path: &Path, e: &Expr) -> R<Val> {
        // Verus rejects `old` in code that runs.
        if self.decl.mode == Mode::Exec
            && self.ghost_depth == 0
            && any_expr(e, &|e| matches!(e.kind, ExprKind::Old(_)))
        {
            return Err(refusal("old-in-exec", "`old` in exec code", e.span));
        }
        let reads = self.body_reads(path)?;
        let mut tr = Tr::new(self.ctx, &self.tables.sigs, &self.tables.functions, &reads)
            .with_recommendations(self.recommendations)
            .with_recommendation_work(self.recommendation_work.clone());
        let value = tr.expr(e)?;
        self.called_ok(&tr.called)?;
        let pending = std::mem::take(&mut tr.checks);
        self.pending(path, pending)?;
        Ok(value)
    }

    fn body_bool(&mut self, path: &Path, e: &Expr) -> R<Term> {
        self.body_expr(path, e)?
            .into_leaf()
            .ok_or_else(|| refusal("vcgen-internal", "a condition that is not a scalar", e.span))
    }

    // ------------------------------------------------------------------
    // Statements
    // ------------------------------------------------------------------

    /// The statements Verus keeps of `block` ([`live_prefix`]). Those
    /// after the path ends there (after a `break` or `continue`, or an
    /// `if` whose branches all end) are walked on a dead path, whose guard
    /// is `false`: they have no checks and no facts, but a loop among them
    /// still has its body checked in a query of its own, as in Verus. On a
    /// dead path only the statements that lead to such a query are walked
    /// ([`needed_when_dead`]).
    fn block(&mut self, path: &mut Path, block: &'a Block) -> R<()> {
        self.stmts(path, live_prefix(block))?;
        let span = block.stmts.last().map_or(self.decl.span, |stmt| stmt.span);
        let points = self
            .resolution
            .block_points(block as *const Block as usize, span)?;
        self.resolve_places(path, &points, span)
    }

    /// The statements `stmts`, as [`Self::block`] walks them.
    fn stmts(&mut self, path: &mut Path, stmts: &'a [Stmt]) -> R<()> {
        let stmts = live_prefix_of(stmts);
        let mut dead: Option<Path> = None;
        for (index, stmt) in stmts.iter().enumerate() {
            let current = dead.as_ref().unwrap_or(&*path);
            if !current.live {
                self.price_ownership_path(current, 1, stmt.span)?;
                let mut next = current.clone();
                next.live = true;
                if !is_dead(&next.guard) {
                    next.guard.push(Term::Bool(false));
                }
                dead = Some(next);
            }
            let current = match dead.as_mut() {
                Some(dead) => dead,
                None => &mut *path,
            };
            if is_dead(&current.guard)
                && !self.independent.needed(stmt)
                && !needed_when_dead(stmt, &stmts[index + 1..])
            {
                // A skipped statement that never finishes (a `return`, say)
                // still ends the path.
                if diverges(stmt) {
                    current.live = false;
                }
                continue;
            }
            self.stmt(current, stmt)?;
        }
        Ok(())
    }

    fn local_shape(&self, local: LocalId, span: SpanId) -> R<(Shape, String)> {
        let decl = self
            .decl
            .local(local)
            .ok_or_else(|| refusal("vcgen-internal", "a missing local", span))?;
        Ok((
            self.ctx.shape(&decl.ty, self.types.owner(), span)?,
            decl.name.clone(),
        ))
    }

    fn stmt(&mut self, path: &mut Path, stmt: &'a Stmt) -> R<()> {
        let points = self
            .resolution
            .before_points(stmt as *const Stmt as usize, stmt.span)?;
        self.resolve_places(path, &points, stmt.span)?;
        if !is_header(stmt) && !self.started {
            self.started = true;
            self.header_visible = Some(self.visible.clone());
        }
        match &stmt.kind {
            StmtKind::Let { local, init } => {
                let (shape, name) = self.local_shape(*local, stmt.span)?;
                if init.is_none() && shape.has_poly() {
                    path.declared.insert(*local);
                    path.env.remove(local);
                    return Ok(());
                }
                let value = match init {
                    Some(init) => {
                        let value = self.body_expr(path, init)?;
                        if self
                            .decl
                            .local(*local)
                            .is_some_and(|local| local.mode != Mode::Spec)
                        {
                            self.consume(path, init)?;
                        }
                        self.name_value(path, value, &shape, &name)?
                    }
                    None => self.fresh(&shape, &name)?,
                };
                path.declared.insert(*local);
                path.moved.retain(|moved| moved.local != *local);
                path.env.insert(*local, value);
                Ok(())
            }
            StmtKind::Assign { place, value } => {
                let translated = self.body_expr(path, value)?;
                if self.kept_place(place, stmt.span)? {
                    self.consume(path, value)?;
                }
                self.assign(path, place, translated, stmt.span)
            }
            StmtKind::BorrowMut { dest, place } => self.borrow_mut(path, *dest, place, stmt.span),
            StmtKind::Call {
                callee,
                type_args,
                args,
                dest,
                site,
            } => self.call(
                path,
                stmt as *const Stmt as usize,
                stmt.span,
                *callee,
                type_args,
                args,
                dest.as_ref(),
                *site,
            ),
            StmtKind::Assert { expr, site, attrs } => {
                let reads = self.body_reads(path)?;
                let goal = self.spec_term(path, &reads, expr)?;
                self.check(
                    path,
                    &[],
                    goal.clone(),
                    *site,
                    CheckKind::Assert {
                        span: stmt.span,
                        attrs: attrs.clone(),
                    },
                    Vec::new(),
                )?;
                self.fact(&path.guard, Source::Assert, goal);
                Ok(())
            }
            StmtKind::AssertBitVector {
                requires,
                ensures,
                architecture,
                site,
            } => {
                // The shared SST live-prefix and independent-query index
                // retain ordinary-dead events but discard a Maybe::Never
                // suffix. Apply conversion syntax rules to exactly those
                // events, after whole-source Reader/WF/effect admission.
                // A source event receives its original one admission grant
                // per generation width, shared across all sibling clauses.
                // Revisited concrete occurrences still lower independently.
                if !self.independent.was_emitted(stmt) {
                    let mut work = 200_000usize;
                    for clause in requires.iter().chain(ensures) {
                        super::bitvector::admit_syntax(self.ctx, &clause.expr, &mut work)?;
                    }
                }
                self.assert_bitvector(path, stmt.span, requires, ensures, *architecture, *site)?;
                self.independent.emitted(stmt);
                Ok(())
            }
            StmtKind::Assume { expr, .. } => {
                let reads = self.body_reads(path)?;
                let term = self.spec_term(path, &reads, expr)?;
                self.fact(&path.guard, Source::Assume, term);
                Ok(())
            }
            StmtKind::If {
                cond,
                then_block,
                else_block,
            } => {
                // Both branches of a dead `if` are dead; its condition is
                // not needed.
                let c = if is_dead(&path.guard) {
                    Term::Bool(false)
                } else {
                    self.body_bool(path, cond)?
                };
                self.price_ownership_path(path, 2, stmt.span)?;
                let mut then_path = path.clone();
                then_path.guard.push(c.clone());
                let mut else_path = path.clone();
                else_path.guard.push(c.clone().not());
                // Both branches and whatever follows them sit behind the
                // split on `c`.
                self.split = true;
                // Fuel assumptions made in a branch belong to that branch.
                // Restore visibility even on a refusal, and start the other
                // branch with the definitions visible before the split.
                let visible = self.visible.clone();
                let then_result = self.block(&mut then_path, then_block);
                let then_visible = self.visible.clone();
                self.visible = visible.clone();
                then_result?;
                let else_result = self.block(&mut else_path, else_block);
                let else_visible = std::mem::replace(&mut self.visible, visible);
                else_result?;
                // Only continuing paths constrain the fuel available after
                // the join. For two continuing paths, their common fuel is
                // the smaller depth; a reveal in just one cannot escape.
                match (
                    then_path.live && !is_dead(&then_path.guard),
                    else_path.live && !is_dead(&else_path.guard),
                ) {
                    (true, false) => self.visible = then_visible,
                    (false, true) => self.visible = else_visible,
                    (true, true) => {
                        self.visible = then_visible
                            .into_iter()
                            .filter_map(|(id, fuel)| {
                                else_visible.get(&id).map(|other| (id, fuel.min(*other)))
                            })
                            .collect();
                    }
                    (false, false) => {}
                }
                self.join(path, &c, then_path, else_path, stmt.span)?;
                self.after_ownership_join(path, stmt as *const Stmt as usize, stmt.span)
            }
            StmtKind::Return { value, site } => self.ret(path, stmt.span, value.as_ref(), *site),
            StmtKind::BroadcastUse { callee } => {
                let declaration = self.ctx.fns.get(callee).copied().ok_or_else(|| {
                    refusal(
                        "broadcast-contract",
                        "an unknown local broadcast proof",
                        stmt.span,
                    )
                })?;
                let reads = Reads {
                    types: super::type_encoding::TypeEnv::new(*callee, Vec::new()),
                    ..Reads::default()
                };
                let mut tr = Tr::new(self.ctx, &self.tables.sigs, &self.tables.functions, &reads);
                let term = tr.broadcast_contract(declaration, stmt.span)?;
                self.called_ok(&tr.called)?;
                if !tr.checks.is_empty() {
                    return Err(refusal(
                        "broadcast-contract",
                        "an execution effect in a broadcast specification",
                        stmt.span,
                    ));
                }
                self.fact(&path.guard, Source::CalleeEnsures, term);
                Ok(())
            }
            StmtKind::Reveal { callee, fuel } => {
                if self
                    .ctx
                    .fns
                    .get(callee)
                    .is_some_and(|decl| decl.role == crate::FnRole::Imported)
                {
                    return Err(refusal(
                        "imported-reveal",
                        "revealing an imported signature without body authority",
                        stmt.span,
                    ));
                }
                self.reveal_allowed(stmt.span)?;
                // Verus accepts fuel above 1 only for a recursive function
                // (`ast_to_sst.rs`, `ExprX::Fuel`).
                if fuel.is_some_and(|n| n > 1) && self.ctx.group(*callee).is_none() {
                    return Err(refusal(
                        "reveal-with-fuel",
                        "reveal_with_fuel of a function that is not recursive",
                        stmt.span,
                    ));
                }
                if let Some(problem) = self.tables.sigs.get(callee).and_then(|s| s.problem.clone())
                {
                    return Err(problem);
                }
                // On a dead path the reveal is never reached. Fuel `n`
                // assumes `fuel_nat == succ^(n-1)(..)`, which stays with
                // a larger fuel assumed before.
                if !is_dead(&path.guard) {
                    let fuel = fuel.unwrap_or(1).max(1);
                    let entry = self.visible.entry(*callee).or_insert(fuel);
                    *entry = (*entry).max(fuel);
                }
                Ok(())
            }
            StmtKind::Hide { callee } => {
                if self
                    .ctx
                    .fns
                    .get(callee)
                    .is_some_and(|decl| decl.role == crate::FnRole::Imported)
                {
                    return Err(refusal(
                        "imported-reveal",
                        "hiding an imported signature without body authority",
                        stmt.span,
                    ));
                }
                // Verus reads `hide` as a header of the function: it holds for
                // the whole body. A `hide` after other statements would hold
                // from its position on here.
                if self.started {
                    return Err(refusal(
                        "hide-position",
                        "hide after the first statement of the body",
                        stmt.span,
                    ));
                }
                self.reveal_allowed(stmt.span)?;
                if !is_dead(&path.guard) {
                    self.visible.remove(callee);
                }
                Ok(())
            }
            StmtKind::Ghost(block) => {
                self.ghost_depth += 1;
                let result = self.block(path, block);
                self.ghost_depth -= 1;
                result
            }
            StmtKind::GhostTail { block, tail } => {
                self.ghost_depth += 1;
                let result = (|| {
                    self.block(path, block)?;
                    if !block.stmts.iter().any(diverges) {
                        let points = self
                            .resolution
                            .tail_points(stmt as *const Stmt as usize, tail.span)?;
                        if path.live {
                            self.resolve_places(path, &points, tail.span)?;
                            self.body_expr(path, tail)?;
                        } else {
                            self.price_ownership_path(path, 1, tail.span)?;
                            let mut dead = path.clone();
                            dead.live = true;
                            if !is_dead(&dead.guard) {
                                dead.guard.push(Term::Bool(false));
                            }
                            self.resolve_places(&mut dead, &points, tail.span)?;
                            self.body_expr(&dead, tail)?;
                        }
                    }
                    Ok(())
                })();
                self.ghost_depth -= 1;
                result
            }
            StmtKind::Block(block) => self.block(path, block),
            StmtKind::Loop(lp) => self.loop_stmt(path, lp, stmt.span),
            StmtKind::Break { target, site } => self.break_stmt(path, *target, *site, stmt.span),
            StmtKind::Continue { target, site } => {
                self.continue_stmt(path, *target, *site, stmt.span)
            }
            // Verus assumes `false` here.
            StmtKind::Unreachable => {
                path.live = false;
                Ok(())
            }
        }
    }

    /// Loop queries need their own fuel scope; until that is represented,
    /// refuse changes within an iteration. Conditional branches save and
    /// restore their definition visibility separately.
    fn reveal_allowed(&self, span: SpanId) -> R<()> {
        if self.loop_depth > 0 {
            return Err(refusal(
                "reveal-in-branch",
                "reveal or hide inside a loop iteration",
                span,
            ));
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn call(
        &mut self,
        path: &mut Path,
        statement: usize,
        span: SpanId,
        callee: FnId,
        type_args: &[Ty],
        args: &[Expr],
        dest: Option<&Place>,
        site: SiteId,
    ) -> R<()> {
        let target = *self
            .ctx
            .fns
            .get(&callee)
            .ok_or_else(|| refusal("vcgen-internal", "a call of an unknown function", span))?;
        if target.role == crate::FnRole::Imported {
            return Err(refusal(
                "imported-call",
                "an imported specification called as a statement",
                span,
            ));
        }
        if target.mode == Mode::Spec {
            return Err(refusal(
                "vcgen-internal",
                "a spec function called as a statement",
                span,
            ));
        }
        if type_args.iter().any(|ty| !matches!(ty, Ty::Param(_))) {
            return Err(refusal(
                "generic-clause",
                "a concrete generic contract without a native instance",
                span,
            ));
        }
        for param in &target.params {
            if let Some(local) = target.local(*param) {
                if matches!(local.ty, Ty::Ref { mutable: true, .. }) {
                    return Err(refusal(
                        "call-mut-ref",
                        format!(
                            "a call of `{}`, which takes a `&mut` parameter",
                            target.name
                        ),
                        span,
                    ));
                }
            }
        }
        if args.len() != target.params.len() {
            return Err(refusal(
                "vcgen-internal",
                "a call with the wrong arity",
                span,
            ));
        }

        // Arguments, left to right, with their exec checks.
        let reads = self.body_reads(path)?;
        let mut tr = Tr::new(self.ctx, &self.tables.sigs, &self.tables.functions, &reads)
            .with_recommendations(self.recommendations)
            .with_recommendation_work(self.recommendation_work.clone());
        let mut values = Vec::new();
        for arg in args {
            values.push(tr.expr(arg)?);
        }
        self.called_ok(&tr.called)?;
        let pending = std::mem::take(&mut tr.checks);
        self.pending(path, pending)?;

        // Name the arguments so the callee's clauses mention them once.
        let mut arg_vals = HashMap::new();
        for (param, value) in target.params.iter().zip(values) {
            let local = target
                .local(*param)
                .ok_or_else(|| refusal("vcgen-internal", "a missing parameter", span))?;
            let shape = self
                .ctx
                .shape(&local.ty.subst(type_args), self.types.owner(), span)?;
            let named = self.name_value(path, value, &shape, &local.name)?;
            arg_vals.insert(*param, named);
        }

        let callee_reads = Reads {
            read: arg_vals.clone(),
            old: arg_vals.clone(),
            types: type_terms(self.ctx, callee, type_args, &self.types, span)?,
            ..Reads::default()
        };
        // A recursive call terminates: checked before the call
        // (`recursion.rs`, `check_termination`), after its arguments' checks.
        // Verus asserts it without assuming it afterwards, so each failing
        // call is reported.
        if self.ctx.same_group(self.owner, callee) {
            if let Some(measure) = self.measure.clone() {
                let goal = self.decreases_goal(target, &callee_reads, &measure)?;
                self.check(
                    path,
                    &[],
                    goal,
                    site,
                    CheckKind::Termination { call: span, callee },
                    Vec::new(),
                )?;
            }
        }

        // Preconditions: each clause checked, earlier ones assumed.
        let mut earlier = Vec::new();
        for (clause, requires) in target.requires.iter().enumerate() {
            let goal = self.contract_term(&callee_reads, &requires.expr)?;
            self.check(
                path,
                &[],
                goal.clone(),
                site,
                CheckKind::Precondition {
                    call: span,
                    callee,
                    clause,
                },
                earlier.clone(),
            )?;
            earlier.push((Source::CallRequires, goal));
        }

        self.check_unwind_call(path, target, &callee_reads, (span, site), earlier)?;

        // The result and the postconditions.
        let ret_ty = target
            .ret_ty()
            .cloned()
            .unwrap_or(Ty::Unit)
            .subst(type_args);
        let ret_shape = self.ctx.shape(&ret_ty, self.types.owner(), span)?;
        let result = self.fresh_at(
            &ret_shape,
            &format!("{}(..)", short_name(&target.name)),
            &path.guard,
        )?;
        let mut ens_reads = callee_reads;
        ens_reads.read.insert(target.ret, result.clone());
        // A clause with a proof note or custom error is checked at the
        // callee's exits but never assumed here, as in Verus (see
        // `ClauseAttrs::is_labelled`).
        let mut clauses = Vec::new();
        for ensures in target.ensures.iter().filter(|c| !c.attrs.is_labelled()) {
            clauses.push(self.contract_term(&ens_reads, &ensures.expr)?);
        }
        // Verus's `ens%f` instance at the arguments: made during the search,
        // so behind a case split it may be built in merged classes.
        let gate = self.split.then(|| instance_gate(&clauses));
        for term in clauses {
            self.fact_gated(&path.guard, Source::CalleeEnsures, term, gate.clone());
        }
        for (argument, param) in args.iter().zip(&target.params) {
            if target
                .local(*param)
                .is_some_and(|local| local.mode != Mode::Spec)
            {
                self.consume(path, argument)?;
            }
        }
        if let Some(dest) = dest {
            self.assign(path, dest, result, span)?;
        } else {
            self.drop_identity_result(path, target, &ret_ty, &result, span)?;
        }
        // The CFG captured argument origins before the common move and
        // finalized only its normal result edge. Rebind that same state to
        // the actual result carriers; never recover an escape by subtracting
        // a possibly shared borrowed footprint.
        self.after_ownership_join(path, statement, span)
    }

    fn ret(&mut self, path: &mut Path, span: SpanId, value: Option<&Expr>, site: SiteId) -> R<()> {
        let decl = self.decl;
        let result = match value {
            Some(e) => self.body_expr(path, e)?,
            None => Val::unit(),
        };
        // In a postcondition a parameter reads its entry value, except
        // through a `&mut` parameter, which reads the current value; `old`
        // reads the entry value.
        let mut read = HashMap::new();
        for param in &decl.params {
            let is_mut_ref = decl
                .local(*param)
                .is_some_and(|local| matches!(local.ty, Ty::Ref { mutable: true, .. }));
            let source = if is_mut_ref { &path.env } else { &self.entry };
            if let Some(value) = source.get(param) {
                read.insert(*param, value.clone());
            }
        }
        read.insert(decl.ret, result);
        let reads = Reads {
            read,
            old: self.entry.clone(),
            types: self.types.clone(),
            ..Reads::default()
        };
        for (clause, ensures) in decl.ensures.iter().enumerate() {
            let goal = self.spec_term(path, &reads, &ensures.expr)?;
            self.check(
                path,
                &[],
                goal,
                site,
                CheckKind::Postcondition { exit: span, clause },
                Vec::new(),
            )?;
        }
        if let Some(value) = value.filter(|_| {
            decl.local(decl.ret)
                .is_some_and(|local| local.mode != Mode::Spec)
        }) {
            self.consume(path, value)?;
        }
        path.live = false;
        Ok(())
    }

    // ------------------------------------------------------------------
    // Loops
    // ------------------------------------------------------------------

    /// A loop (`ast_to_sst.rs` and `sst_to_air.rs`, `Loop`).
    fn loop_stmt(&mut self, path: &mut Path, lp: &'a Loop, span: SpanId) -> R<()> {
        let info = self
            .loop_info
            .get(&lp.id)
            .cloned()
            .ok_or_else(|| refusal("vcgen-internal", "a loop the pre-pass missed", span))?;
        // Which invariants hold where. Without isolation and with
        // `allow_complex_invariants`, an `invariant_except_break` is a plain
        // invariant and an `ensures` is dropped: every path out of the loop
        // is followed to the code after it.
        let mut entry_invs = Vec::new();
        let mut exit_invs = Vec::new();
        for (index, inv) in lp.invariants.iter().enumerate() {
            let (at_entry, at_exit) = match inv.kind {
                InvariantKind::Ensures if lp.allow_complex_invariants => continue,
                InvariantKind::ExceptBreak if lp.allow_complex_invariants => (true, true),
                InvariantKind::ExceptBreak => (true, false),
                InvariantKind::Always => (true, true),
                InvariantKind::Ensures => (false, true),
            };
            if at_entry {
                entry_invs.push(index);
            }
            if at_exit {
                exit_invs.push(index);
            }
        }
        let simple_invs = lp
            .invariants
            .iter()
            .all(|inv| inv.kind == InvariantKind::Always);
        // A `while` without `break` whose invariants all hold on entry and
        // exit keeps its condition; any other `while` becomes
        // `loop { cond; if !cond { break } body }`.
        let simple_while = !info.has_break && simple_invs && lp.cond.is_some() && lp.isolation;

        // The invariants hold on entry.
        let reads = self.body_reads(path)?;
        for index in &entry_invs {
            let inv = &lp.invariants[*index];
            let goal = self.spec_term(path, &reads, &inv.expr)?;
            self.check(
                path,
                &[],
                goal,
                lp.sites.entry,
                CheckKind::LoopInvariant {
                    at: InvariantAt::Entry,
                    invariant: inv.span,
                    kind: inv.kind,
                },
                Vec::new(),
            )?;
        }
        // The loop's exits join paths: what follows sits behind a split.
        self.split = true;

        if !lp.isolation {
            return self.joined_loop(path, lp, span, &info, entry_invs, exit_invs);
        }

        // The body, in a query of its own.
        let group = self.next_group;
        self.next_group = self.next_group.wrapping_add(1);
        let saved = Saved {
            facts: std::mem::take(&mut self.facts),
            split: self.split,
            entry: self.entry.clone(),
            visible: self.visible.clone(),
            measure: self.measure.clone(),
            loop_depth: self.loop_depth,
            group: self.group,
        };
        self.group = group;
        self.loop_depth = 0;
        self.split = false;
        if let Some(header) = &self.header_visible {
            self.visible = header.clone();
        }
        let result = self.isolated_body(
            path,
            lp,
            span,
            &info,
            simple_while,
            entry_invs.clone(),
            exit_invs.clone(),
            group,
        );
        self.facts = saved.facts;
        self.split = saved.split;
        self.entry = saved.entry;
        self.visible = saved.visible;
        self.measure = saved.measure;
        self.loop_depth = saved.loop_depth;
        self.group = saved.group;
        self.groups_done.push((group, span));
        result?;

        // After the loop: what it assigns is arbitrary, the exit invariants
        // hold, and a simple `while` has evaluated its condition to false.
        self.isolated_loop_exit(path, lp, &info, span)?;
        if !path.live {
            return Ok(());
        }
        let reads = self.body_reads(path)?;
        for index in &exit_invs {
            let term = self.spec_term(path, &reads, &lp.invariants[*index].expr)?;
            self.fact(&path.guard, Source::LoopInvariant, term);
        }
        if let (true, Some(cond)) = (simple_while, &lp.cond) {
            self.block(path, &cond.block)?;
            if path.live {
                let c = self.body_bool(path, &cond.expr)?;
                self.fact(&path.guard, Source::LoopExit, c.not());
            }
        }
        if lp.cond.is_none() && !info.has_break {
            path.live = false;
        }
        Ok(())
    }

    /// The body of an isolated loop, in its own query: every available value
    /// starts from an arbitrary value of its type, and only the invariants are
    /// known (`sst_to_air.rs`: the loop query has the type invariants of
    /// the locals, the "pre" snapshot with the parameters modified before
    /// or in the loop havocked after it, and the invariants).
    #[allow(clippy::too_many_arguments)]
    fn isolated_body(
        &mut self,
        path: &Path,
        lp: &'a Loop,
        span: SpanId,
        info: &LoopInfo,
        simple_while: bool,
        entry_invs: Vec<usize>,
        exit_invs: Vec<usize>,
        group: u32,
    ) -> R<()> {
        let mut inner = self.isolated_loop_path(path, lp, span)?;
        let mut entry = HashMap::new();
        for param in &self.decl.params {
            let value =
                if info.premodified.contains(param) {
                    let (shape, name) = self.local_shape(*param, span)?;
                    self.fresh(&shape, &format!("old({name})"))?
                } else {
                    inner.env.get(param).cloned().ok_or_else(|| {
                        refusal("vcgen-internal", "a parameter not in scope", span)
                    })?
                };
            entry.insert(*param, value);
        }
        self.entry = entry;
        // Verus assigns the measure at entry again at the start of the
        // loop's query, from the parameters' values there.
        if self.measure.is_some() {
            let entry_reads = Reads {
                read: self.entry.clone(),
                old: self.entry.clone(),
                types: self.types.clone(),
                ..Reads::default()
            };
            let decl = self.measure_decl()?;
            self.measure = self.entry_measure(decl, &entry_reads)?;
        }

        let reads = self.body_reads(&inner)?;
        for index in &entry_invs {
            let term = self.spec_term(&inner, &reads, &lp.invariants[*index].expr)?;
            self.fact(&[], Source::LoopInvariant, term);
        }
        let measure = self.measure(&inner, lp)?;
        self.loops.push(LoopFrame {
            lp,
            entry_invs,
            exit_invs,
            measure,
            group,
            breaks: Vec::new(),
        });
        let result = self.iteration(&mut inner, lp, span, !simple_while);
        self.loops.pop();
        result
    }

    /// A loop without isolation, walked in the enclosing query
    /// (`sst_to_air.rs`: a breakable block that havocs what the loop
    /// assigns, assumes the invariants and ends in `assume false`; a
    /// `break` jumps past it).
    fn joined_loop(
        &mut self,
        path: &mut Path,
        lp: &'a Loop,
        span: SpanId,
        info: &LoopInfo,
        entry_invs: Vec<usize>,
        exit_invs: Vec<usize>,
    ) -> R<()> {
        self.price_ownership_path(path, 2, span)?;
        let before = path.clone();
        let mut inner = path.clone();
        self.havoc(&mut inner, info, span)?;
        self.joined_loop_ownership(&mut inner, lp, span)?;
        let reads = self.body_reads(&inner)?;
        for index in &entry_invs {
            let term = self.spec_term(&inner, &reads, &lp.invariants[*index].expr)?;
            self.fact(&inner.guard, Source::LoopInvariant, term);
        }
        let measure = self.measure(&inner, lp)?;
        self.loops.push(LoopFrame {
            lp,
            entry_invs,
            exit_invs,
            measure,
            group: self.group,
            breaks: Vec::new(),
        });
        // Reveals inside the body would hold on some paths only.
        self.loop_depth += 1;
        let result = self.iteration(&mut inner, lp, span, true);
        self.loop_depth -= 1;
        let frame = self.loops.pop();
        result?;
        let breaks = frame.map(|f| f.breaks).unwrap_or_default();
        self.join_breaks(path, before, breaks, lp, span)
    }

    /// One iteration from its start: the condition (as `if !cond { break }`
    /// when `cond_breaks`), the body, and the checks at its end.
    fn iteration(
        &mut self,
        inner: &mut Path,
        lp: &'a Loop,
        span: SpanId,
        cond_breaks: bool,
    ) -> R<()> {
        if let Some(cond) = &lp.cond {
            self.block(inner, &cond.block)?;
            if !inner.live {
                return Ok(());
            }
            let c = self.body_bool(inner, &cond.expr)?;
            if cond_breaks {
                self.price_ownership_path(inner, 1, cond.expr.span)?;
                let mut exit = inner.clone();
                exit.guard.push(c.clone().not());
                self.leave(&mut exit, lp.id, lp.sites.exit, cond.expr.span)?;
            }
            inner.guard.push(c);
        }
        self.block(inner, &lp.body)?;
        if inner.live {
            self.restart(inner, lp.id, lp.sites.end, span, None)?;
        }
        Ok(())
    }

    /// The measure's value at the start of an iteration, one named term per
    /// component.
    fn measure(&mut self, path: &Path, lp: &Loop) -> R<Vec<Term>> {
        let reads = self.body_reads(path)?;
        let mut out = Vec::new();
        for component in &lp.decreases {
            let mut tr = Tr::new(self.ctx, &self.tables.sigs, &self.tables.functions, &reads)
                .with_recommendations(self.recommendations)
                .with_recommendation_work(self.recommendation_work.clone());
            let term = tr.expr(component)?.into_leaf().ok_or_else(|| {
                refusal(
                    "vcgen-internal",
                    "a measure that is not a scalar",
                    component.span,
                )
            })?;
            self.called_ok(&tr.called)?;
            if tr.checks.iter().any(|check| {
                !matches!(
                    check.kind,
                    PendingKind::Recommendation { .. } | PendingKind::ChoiceRecommendation
                )
            }) {
                return Err(refusal(
                    "vcgen-internal",
                    "an exec check in a decreases clause",
                    component.span,
                ));
            }
            self.pending(path, tr.checks)?;
            let named = self.name_value(
                path,
                Val::Leaf(term),
                &Shape::Leaf(super::val::LeafTy::Int(crate::ty::IntRange::Int)),
                "decreases",
            )?;
            out.push(named.into_leaf().ok_or_else(|| {
                refusal(
                    "vcgen-internal",
                    "a measure that is not a scalar",
                    component.span,
                )
            })?);
        }
        Ok(out)
    }

    // ------------------------------------------------------------------
    // Termination
    // ------------------------------------------------------------------

    /// The function whose measure recursive calls are checked against.
    fn measure_decl(&self) -> R<&'a FnDecl> {
        self.ctx
            .fns
            .get(&self.owner)
            .copied()
            .ok_or_else(|| refusal("vcgen-internal", "an unknown function", self.decl.span))
    }

    /// One measure component as a term.
    fn measure_term(&self, reads: &Reads, component: &Expr) -> R<Term> {
        let mut tr = Tr::new(self.ctx, &self.tables.sigs, &self.tables.functions, reads);
        if self.recommendations {
            tr = tr.with_auxiliary_work(self.recommendation_work.clone());
        }
        let term = tr.expr(component)?.into_leaf().ok_or_else(|| {
            refusal(
                "vcgen-internal",
                "a measure that is not a scalar",
                component.span,
            )
        })?;
        self.called_ok(&tr.called)?;
        if !tr.checks.is_empty() {
            return Err(refusal(
                "vcgen-internal",
                "an exec check in a decreases clause",
                component.span,
            ));
        }
        Ok(term)
    }

    /// `decl`'s measure at entry (its parameters read through `reads`),
    /// each component named, when its recursive calls are checked to
    /// terminate: a member of a group, unless an exec function without a
    /// measure that allows none (`ast_to_sst_func.rs`,
    /// `exec_with_no_termination_check`).
    fn entry_measure(&mut self, decl: &'a FnDecl, reads: &Reads) -> R<Option<Vec<Term>>> {
        if self.ctx.group(decl.id).is_none() {
            return Ok(None);
        }
        if decl.decreases.is_empty() {
            if decl.mode == Mode::Exec && decl.attrs.exec_allows_no_decreases {
                return Ok(None);
            }
            return Err(refusal(
                "recursion-without-decreases",
                format!("`{}` is recursive and has no decreases clause", decl.name),
                decl.span,
            ));
        }
        let entry = Path {
            guard: Vec::new(),
            declared: BTreeSet::new(),
            env: HashMap::new(),
            live: true,
            ..Path::default()
        };
        let mut out = Vec::new();
        for component in &decl.decreases {
            let term = self.measure_term(reads, component)?;
            let named = self.name_value(
                &entry,
                Val::Leaf(term),
                &Shape::Leaf(LeafTy::Int(crate::ty::IntRange::Int)),
                "decreases",
            )?;
            out.push(named.into_leaf().ok_or_else(|| {
                refusal(
                    "vcgen-internal",
                    "a measure that is not a scalar",
                    component.span,
                )
            })?);
        }
        Ok(Some(out))
    }

    /// The termination goal of a call of `callee` whose parameters read
    /// `reads`, against the caller's measure at entry.
    fn decreases_goal(&self, callee: &FnDecl, reads: &Reads, measure: &[Term]) -> R<Term> {
        let mut now = Vec::new();
        for component in &callee.decreases {
            now.push(self.measure_term(reads, component)?);
        }
        Ok(check_decrease(&now, measure))
    }

    /// Declare a symbol made elsewhere, with its range fact.
    fn declare(&mut self, name: &str, leaf: LeafTy, display: &str, guard: &[Term]) -> R<()> {
        self.symbols.push(Symbol {
            name: name.to_string(),
            sort: leaf.sort(),
            display: display.to_string(),
        });
        let range = self.ctx.type_fact(
            leaf,
            &self.types,
            &Term::var(name, leaf.sort()),
            self.decl.span,
        )?;
        if range != Term::Bool(true) {
            self.fact(
                if matches!(leaf, LeafTy::Poly(_)) {
                    guard
                } else {
                    &[]
                },
                Source::TypeFact,
                range,
            );
        }
        Ok(())
    }

    /// The source Spec body gets a fresh auxiliary state, its own authored
    /// domain and actual ordered proof events. No termination query is emitted.
    pub(crate) fn run_spec_recommendations(self) -> R<Vec<Check>> {
        let spec = self.decl;
        if !self.recommendations {
            return Err(refusal(
                "vcgen-internal",
                "Spec diagnostics in a normal proof",
                spec.span,
            ));
        }
        self.run_termination(spec)
    }

    /// The termination check of a recursive spec function `spec`
    /// (`ast_to_sst_func.rs`, `func_body_to_sst`, and `recursion.rs`,
    /// `check_termination_stm`). Its query assumes the parameters' types
    /// and the `when` condition, walks the body of its `decreases_by`
    /// function, if any, and then its body, flattened: every recursive call
    /// is checked to decrease the measure, under the conditions that lead
    /// to it, and its result is a fresh value of its type. The group's
    /// definitions are not visible; Verus emits them after this check.
    ///
    /// `self` was made for the `decreases_by` function when `spec` has one
    /// (its locals are that function's), and for `spec` otherwise.
    pub(crate) fn run_termination(mut self, spec: &'a FnDecl) -> R<Vec<Check>> {
        self.independent.extend(spec);
        self.owner = spec.id;
        let Body::Spec(body) = &spec.body else {
            return Err(refusal(
                "vcgen-internal",
                "a recursive spec function without a body",
                spec.span,
            ));
        };
        // The separate Spec-body auxiliary pass does not execute a
        // decreases_by proof or re-solve termination obligations.
        let via = if self.recommendations {
            None
        } else {
            match spec.decreases_by {
                Some(id) => Some(*self.ctx.fns.get(&id).ok_or_else(|| {
                    refusal(
                        "vcgen-internal",
                        "an unknown decreases_by function",
                        spec.span,
                    )
                })?),
                None => None,
            }
        };
        self.types = self.fresh_types(spec)?;
        // The parameters, shared with the `decreases_by` function's.
        let mut values = HashMap::new();
        for (index, param) in spec.params.iter().enumerate() {
            let local = spec
                .local(*param)
                .ok_or_else(|| refusal("vcgen-internal", "a missing parameter", spec.span))?;
            let shape = self.ctx.shape(&local.ty, self.types.owner(), local.span)?;
            let value = self.fresh(&shape, &local.name)?;
            if let Some(via) = via {
                let theirs = via.params.get(index).ok_or_else(|| {
                    refusal(
                        "vcgen-internal",
                        "a decreases_by function with other parameters",
                        spec.span,
                    )
                })?;
                self.entry.insert(*theirs, value.clone());
            }
            if self.recommendations {
                self.entry.insert(*param, value.clone());
            }
            values.insert(*param, value);
        }
        let reads = Reads {
            read: values.clone(),
            old: values,
            types: self.types.clone(),
            ..Reads::default()
        };
        let members: BTreeSet<FnId> = if self.recommendations {
            // No body expansion or fresh-value termination abstraction in the
            // diagnostic pass. Recursive calls remain actual Spec applications.
            BTreeSet::new()
        } else {
            self.ctx
                .group(spec.id)
                .map(|group| group.members.iter().map(|(id, _)| *id).collect())
                .unwrap_or_default()
        };
        let mut path = Path {
            guard: Vec::new(),
            declared: self.entry.keys().copied().collect(),
            env: self.entry.clone(),
            live: true,
            ..Path::default()
        };
        if self.recommendations {
            // The source declaration owns nested checks in its authored
            // domains. As a40 ast_to_sst_func935–940, assume each own domain
            // ONLY after checking its expression, in this auxiliary state.
            // This never changes normal VCs or makes a failed callee goal a fact.
            for clause in spec.requires.iter().chain(&spec.recommends) {
                let condition = self.spec_term(&path, &reads, &clause.expr)?;
                self.fact(&[], Source::Requires, condition);
            }
            for component in &spec.decreases {
                self.recommendation_measure(&path, &reads, component)?;
            }
        } else {
            if let Some(when) = &spec.decreases_when {
                // A recursive call in the condition is checked too in Verus;
                // that check is not generated.
                if any_expr(
                    when,
                    &|e| matches!(&e.kind, ExprKind::Call { callee, .. } if members.contains(callee)),
                ) {
                    return Err(refusal(
                        "termination-when",
                        "a recursive call in a decreases_when condition",
                        when.span,
                    ));
                }
                let term = self.spec_term(&path, &reads, when)?;
                self.fact(&[], Source::Requires, term);
            }
            self.measure = self.entry_measure(spec, &reads)?;
        }
        let measure = self.measure.clone().unwrap_or_default();
        if let Some(via) = via {
            let Body::Stmts(block) = &via.body else {
                return Err(refusal(
                    "vcgen-internal",
                    "a decreases_by function without a body",
                    via.span,
                ));
            };
            // The body ends in the implicit return of `()`; Verus rejects an
            // explicit one.
            let stmts = match block.stmts.split_last() {
                Some((last, rest)) if matches!(last.kind, StmtKind::Return { value: None, .. }) => {
                    rest
                }
                _ => &block.stmts[..],
            };
            let mut returns = false;
            for stmt in stmts {
                returns |= holds(stmt, &|kind| matches!(kind, StmtKind::Return { .. }));
            }
            if returns {
                return Err(refusal(
                    "decreases-by-return",
                    "a return in a decreases_by function",
                    via.span,
                ));
            }
            self.stmts(&mut path, stmts)?;
        }
        if path.live {
            let mut tr = Tr::new(self.ctx, &self.tables.sigs, &self.tables.functions, &reads)
                .with_recommendations(self.recommendations)
                .with_recommendation_work(self.recommendation_work.clone());
            tr.rec_calls = Some(super::expr::RecCalls {
                members,
                found: Vec::new(),
                proofs: 0,
            });
            tr.expr(body)?;
            self.called_ok(&tr.called)?;
            if tr.checks.iter().any(|check| {
                !matches!(
                    check.kind,
                    PendingKind::Recommendation { .. } | PendingKind::ChoiceRecommendation
                )
            }) {
                return Err(refusal(
                    "vcgen-internal",
                    "an exec check in spec code",
                    body.span,
                ));
            }
            let recommendations = std::mem::take(&mut tr.checks);
            let events = tr.rec_calls.take().map(|rec| rec.found).unwrap_or_default();
            for event in &events {
                if let RecEvent::Call(call) = event {
                    let callee = self
                        .ctx
                        .fns
                        .get(&call.callee)
                        .map_or("?", |f| f.name.as_str());
                    for (name, leaf) in &call.result {
                        self.declare(
                            name,
                            *leaf,
                            &format!("{}(..)", short_name(callee)),
                            &call.guard,
                        )?;
                    }
                }
            }
            let mut blocks = Vec::new();
            proof_blocks(body, &mut blocks);
            self.pending(&path, recommendations)?;
            for event in events {
                let call = match event {
                    RecEvent::Call(call) => call,
                    RecEvent::Diagnostic(check) => {
                        self.pending(&path, vec![check])?;
                        continue;
                    }
                    RecEvent::Proof(proof) => {
                        self.declare_diagnostic_symbols(
                            &proof.diagnostic_symbols,
                            &path.guard,
                            body.span,
                        )?;
                        // Its statements, under the conditions that lead to
                        // it, reading the parameters and the spec `let`s in
                        // scope.
                        if via.is_some() {
                            return Err(refusal(
                                "proof-in-spec-decreases-by",
                                "a proof block in a spec function with a decreases_by function",
                                body.span,
                            ));
                        }
                        let block = blocks.get(proof.ordinal).copied().ok_or_else(|| {
                            refusal("vcgen-internal", "a proof block out of order", body.span)
                        })?;
                        let mut env = reads.read.clone();
                        env.extend(proof.bound);
                        let mut guard = path.guard.clone();
                        guard.extend(proof.guard);
                        let mut inner = Path {
                            guard,
                            declared: env.keys().copied().collect(),
                            env,
                            live: true,
                            ..Path::default()
                        };
                        self.in_proof_in_spec = true;
                        let walked = self.stmts(&mut inner, &block.stmts);
                        self.in_proof_in_spec = false;
                        walked?;
                        continue;
                    }
                };
                let callee = *self.ctx.fns.get(&call.callee).ok_or_else(|| {
                    refusal("vcgen-internal", "a call of an unknown function", call.span)
                })?;
                let read: HashMap<LocalId, Val> =
                    callee.params.iter().copied().zip(call.args).collect();
                let callee_reads = Reads {
                    read: read.clone(),
                    old: read,
                    types: call.types,
                    ..Reads::default()
                };
                let goal = self.decreases_goal(callee, &callee_reads, &measure)?;
                let site = SiteId(self.next_spec_site);
                self.next_spec_site = self.next_spec_site.wrapping_sub(1);
                self.check(
                    &path,
                    &call.guard,
                    goal,
                    site,
                    CheckKind::Termination {
                        call: call.span,
                        callee: call.callee,
                    },
                    Vec::new(),
                )?;
            }
        }
        self.finish_groups()
    }

    /// Freshen available values the loop assigns. A write set alone cannot
    /// initialize declared abstract storage or create a membership witness.
    fn havoc(&mut self, path: &mut Path, info: &LoopInfo, span: SpanId) -> R<()> {
        for local in &info.modified {
            if path.env.contains_key(local) {
                let (shape, name) = self.local_shape(*local, span)?;
                let value = self.fresh_at(&shape, &name, &path.guard)?;
                path.env.insert(*local, value);
            }
        }
        Ok(())
    }

    /// The frame of loop `target`, and whether an isolated loop lies
    /// between it and the current statement.
    fn frame_index(&self, target: LoopId, span: SpanId) -> R<(usize, bool)> {
        let index = self
            .loops
            .iter()
            .rposition(|frame| frame.lp.id == target)
            .ok_or_else(|| {
                refusal(
                    "vcgen-internal",
                    "a break or continue outside its loop",
                    span,
                )
            })?;
        let crosses = self.loops[index + 1..]
            .iter()
            .any(|frame| frame.lp.isolation);
        Ok((index, crosses))
    }

    /// Leave loop `target` from `path` at `at`: its exit invariants are
    /// checked when it is isolated; without isolation the path joins the
    /// code after the loop. The path ends.
    fn leave(&mut self, path: &mut Path, target: LoopId, site: SiteId, at: SpanId) -> R<()> {
        let (index, crosses) = self.frame_index(target, at)?;
        let frame = &self.loops[index];
        if frame.lp.isolation {
            let lp = frame.lp;
            let exit_invs = frame.exit_invs.clone();
            let reads = self.body_reads(path)?;
            for inv_index in exit_invs {
                let inv = &lp.invariants[inv_index];
                let goal = self.spec_term(path, &reads, &inv.expr)?;
                self.check(
                    path,
                    &[],
                    goal,
                    site,
                    CheckKind::LoopInvariant {
                        at: InvariantAt::Break(at),
                        invariant: inv.span,
                        kind: inv.kind,
                    },
                    Vec::new(),
                )?;
            }
        } else {
            // Verus jumps to a label of the enclosing query; from inside an
            // isolated loop's query there is none.
            if crosses || self.loops[index].group != self.group {
                return Err(refusal(
                    "loop-break-isolation",
                    "a break out of an isolated loop to a loop without isolation",
                    at,
                ));
            }
            self.price_ownership_path(path, 1, at)?;
            self.loops[index].breaks.push(path.clone());
        }
        path.live = false;
        Ok(())
    }

    /// Restart loop `target` from `path` (the end of its body, or a
    /// `continue` at `continue_at`): its invariants and its measure are
    /// checked. The path ends.
    fn restart(
        &mut self,
        path: &mut Path,
        target: LoopId,
        site: SiteId,
        span: SpanId,
        continue_at: Option<SpanId>,
    ) -> R<()> {
        let (index, crosses) = self.frame_index(target, span)?;
        let lp = self.loops[index].lp;
        let entry_invs = self.loops[index].entry_invs.clone();
        let measure = self.loops[index].measure.clone();
        if continue_at.is_some() && !lp.decreases.is_empty() && crosses {
            // `sst_to_air.rs`: Verus's error for a labeled `continue` out of
            // an isolated loop to a loop with a measure.
            return Err(refusal(
                "loop-continue-label",
                "a continue with a measure check out of an isolated loop",
                span,
            ));
        }
        let at = match continue_at {
            Some(at) => InvariantAt::Continue(at),
            None => InvariantAt::End,
        };
        let reads = self.body_reads(path)?;
        for inv_index in entry_invs {
            let inv = &lp.invariants[inv_index];
            let goal = self.spec_term(path, &reads, &inv.expr)?;
            self.check(
                path,
                &[],
                goal,
                site,
                CheckKind::LoopInvariant {
                    at,
                    invariant: inv.span,
                    kind: inv.kind,
                },
                Vec::new(),
            )?;
        }
        if !lp.decreases.is_empty() {
            let mut now = Vec::new();
            for component in &lp.decreases {
                let reads = self.body_reads(path)?;
                let mut tr = Tr::new(self.ctx, &self.tables.sigs, &self.tables.functions, &reads)
                    .with_recommendations(self.recommendations)
                    .with_recommendation_work(self.recommendation_work.clone());
                let term = tr.expr(component)?.into_leaf().ok_or_else(|| {
                    refusal(
                        "vcgen-internal",
                        "a measure that is not a scalar",
                        component.span,
                    )
                })?;
                self.called_ok(&tr.called)?;
                if tr.checks.iter().any(|check| {
                    !matches!(
                        check.kind,
                        PendingKind::Recommendation { .. } | PendingKind::ChoiceRecommendation
                    )
                }) {
                    return Err(refusal(
                        "vcgen-internal",
                        "an exec check in a decreases clause",
                        component.span,
                    ));
                }
                self.pending(path, tr.checks)?;
                now.push(term);
            }
            let goal = decreased(&now, &measure);
            self.check(
                path,
                &[],
                goal,
                site,
                CheckKind::LoopDecreases {
                    span: continue_at.unwrap_or(span),
                    at_continue: continue_at.is_some(),
                },
                Vec::new(),
            )?;
        }
        path.live = false;
        Ok(())
    }

    fn break_stmt(&mut self, path: &mut Path, target: LoopId, site: SiteId, span: SpanId) -> R<()> {
        self.split = true;
        self.leave(path, target, site, span)
    }

    fn continue_stmt(
        &mut self,
        path: &mut Path,
        target: LoopId,
        site: SiteId,
        span: SpanId,
    ) -> R<()> {
        self.split = true;
        self.restart(path, target, site, span, Some(span))
    }

    /// The code after a loop without isolation: the paths that left it,
    /// joined. `before` is the path that entered the loop; the others
    /// extend its guard.
    fn join_breaks(
        &mut self,
        path: &mut Path,
        before: Path,
        breaks: Vec<Path>,
        lp: &Loop,
        span: SpanId,
    ) -> R<()> {
        if breaks.is_empty() {
            path.live = false;
            return Ok(());
        }
        let prefix = before.guard.len();
        let mut conds = Vec::new();
        for exit in &breaks {
            if exit.guard.len() < prefix || exit.guard[..prefix] != before.guard[..] {
                return Err(refusal(
                    "vcgen-internal",
                    "a loop exit that does not extend the loop's path",
                    span,
                ));
            }
            conds.push(Term::and(exit.guard[prefix..].to_vec()));
        }
        let mut guard = before.guard.clone();
        guard.push(Term::or(conds.clone()));
        let mut env = HashMap::new();
        let mut locals: Vec<LocalId> = before.declared.iter().copied().collect();
        locals.sort();
        for local in locals {
            let values: Option<Vec<&Val>> = breaks.iter().map(|b| b.env.get(&local)).collect();
            let Some(values) = values else {
                continue;
            };
            let Some(first) = values.first() else {
                continue;
            };
            if values.iter().all(|v| v == first) {
                env.insert(local, (*first).clone());
                continue;
            }
            let (shape, name) = self.local_shape(local, span)?;
            let merged = self.fresh_at(&shape, &name, &guard)?;
            for (value, cond) in values.iter().zip(&conds) {
                let eq = merged.equal(value).ok_or_else(|| {
                    refusal(
                        "vcgen-internal",
                        "loop exits give a local values of different shapes",
                        span,
                    )
                })?;
                let mut exit_guard = before.guard.clone();
                exit_guard.push(cond.clone());
                self.fact(&exit_guard, Source::Binding, eq);
            }
            env.insert(local, merged);
        }
        self.resolution.charge(breaks.len(), span)?;
        let ownership = self.joined_ownership(&breaks.iter().collect::<Vec<_>>(), span)?;
        *path = Path {
            guard,
            declared: before.declared,
            env,
            live: true,
            moved: ownership.moved,
            loans: ownership.loans,
            escaped_loans: ownership.escaped,
            resolved: ownership.resolved,
        };
        self.after_loop_breaks(path, lp, span)
    }

    /// Merge the two paths out of an `if` into `path`.
    fn join(
        &mut self,
        path: &mut Path,
        cond: &Term,
        then_path: Path,
        else_path: Path,
        span: SpanId,
    ) -> R<()> {
        match (then_path.live, else_path.live) {
            (false, false) => {
                path.live = false;
                Ok(())
            }
            (true, false) => {
                *path = then_path;
                Ok(())
            }
            (false, true) => {
                *path = else_path;
                Ok(())
            }
            (true, true) => {
                // Each branch's path condition extends the one before the
                // `if` by the branch condition and by the conditions of the
                // paths that went on in it; the paths that left the branch
                // (a `break` stored for after a loop without isolation, say)
                // are not on the joined path.
                let then_cond = extension(&path.guard, &then_path.guard, span)?;
                let else_cond = extension(&path.guard, &else_path.guard, span)?;
                let mut type_guard = path.guard.clone();
                type_guard.push(Term::or([then_cond.clone(), else_cond.clone()]));
                let mut env = HashMap::new();
                let mut locals: Vec<LocalId> = path.declared.iter().copied().collect();
                locals.sort();
                for local in locals {
                    let (Some(a), Some(b)) = (then_path.env.get(&local), else_path.env.get(&local))
                    else {
                        continue;
                    };
                    if a == b {
                        env.insert(local, a.clone());
                        continue;
                    }
                    let (shape, name) = self.local_shape(local, span)?;
                    let merged = self.fresh_at(&shape, &name, &type_guard)?;
                    let (Some(eq_then), Some(eq_else)) = (merged.equal(a), merged.equal(b)) else {
                        return Err(refusal(
                            "vcgen-internal",
                            "branches give a local values of different shapes",
                            span,
                        ));
                    };
                    self.fact(&then_path.guard, Source::Binding, eq_then);
                    self.fact(&else_path.guard, Source::Binding, eq_else);
                    env.insert(local, merged);
                }
                if then_cond != *cond || else_cond != cond.clone().not() {
                    path.guard.push(Term::or([then_cond, else_cond]));
                }
                let ownership = self.joined_ownership(&[&then_path, &else_path], span)?;
                path.moved = ownership.moved;
                path.loans = ownership.loans;
                path.escaped_loans = ownership.escaped;
                path.resolved = ownership.resolved;
                path.env = env;
                Ok(())
            }
        }
    }
}

/// The `proof { .. }` blocks of a spec expression, in the order [`Tr`]
/// evaluates it.
fn proof_blocks<'e>(e: &'e Expr, out: &mut Vec<&'e Block>) {
    if let ExprKind::ProofInSpec(block) | ExprKind::ProofInSpecTail { block, .. } = &e.kind {
        out.push(block);
    }
    e.for_each_child(&mut |child| proof_blocks(child, out));
}

/// Must `stmt` be walked on a dead path, with `rest` the statements after
/// it? Nothing on a dead path is checked or learnt, but a loop's body is
/// checked in a query of its own, so a statement holding a loop is walked,
/// and so is a `let` a later loop may see. A `break` or `continue` is
/// walked for the loop encoding's refusals.
fn needed_when_dead(stmt: &Stmt, rest: &[Stmt]) -> bool {
    holds(stmt, &|kind| {
        matches!(
            kind,
            StmtKind::Loop(_) | StmtKind::Break { .. } | StmtKind::Continue { .. }
        )
    }) || (matches!(stmt.kind, StmtKind::Let { .. })
        && rest
            .iter()
            .any(|later| holds(later, &|kind| matches!(kind, StmtKind::Loop(_)))))
}

/// Does `pred` hold for `stmt` or a statement nested in it?
fn holds(stmt: &Stmt, pred: &dyn Fn(&StmtKind) -> bool) -> bool {
    if pred(&stmt.kind) {
        return true;
    }
    let inner = |block: &Block| block.stmts.iter().any(|s| holds(s, pred));
    match &stmt.kind {
        StmtKind::If {
            then_block,
            else_block,
            ..
        } => inner(then_block) || inner(else_block),
        StmtKind::Ghost(block) | StmtKind::Block(block) => inner(block),
        StmtKind::GhostTail { block, tail } => {
            inner(block)
                || tail.any(&|e| match &e.kind {
                    ExprKind::ProofInSpec(block) | ExprKind::ProofInSpecTail { block, .. } => {
                        block.stmts.iter().any(|s| holds(s, pred))
                    }
                    _ => false,
                })
        }
        StmtKind::Loop(lp) => lp.cond.as_ref().is_some_and(|c| inner(&c.block)) || inner(&lp.body),
        _ => false,
    }
}

/// Is a path with the condition `guard` dead: is one of its conditions
/// `false`?
fn is_dead(guard: &[Term]) -> bool {
    guard.contains(&Term::Bool(false))
}

/// The conditions `guard` adds to `prefix`, as one term.
fn extension(prefix: &[Term], guard: &[Term], span: SpanId) -> R<Term> {
    match guard.strip_prefix(prefix) {
        Some(rest) => Ok(Term::and(rest.to_vec())),
        None => Err(refusal(
            "vcgen-internal",
            "a branch path that does not extend the path before the if",
            span,
        )),
    }
}

/// The last segment of a display path.
fn short_name(name: &str) -> &str {
    name.rsplit("::").next().unwrap_or(name)
}

/// The ground instance of Verus's prelude axiom for one nonlinear stand-in.
fn nonlinear_axiom(name: &str, args: &[Term]) -> Option<Term> {
    let [x, y] = args else {
        return None;
    };
    let call = Term::call(name, args.to_vec(), Sort::Int);
    let zero = || Term::Int(0);
    match name {
        // prelude_mul_nats
        NL_MUL => Some(Term::implies(
            Term::and([Term::le(zero(), x.clone()), Term::le(zero(), y.clone())]),
            Term::le(zero(), call),
        )),
        // prelude_div_unsigned_in_bounds
        NL_DIV => Some(Term::implies(
            Term::and([Term::le(zero(), x.clone()), Term::lt(zero(), y.clone())]),
            Term::and([Term::le(zero(), call.clone()), Term::le(call, x.clone())]),
        )),
        // prelude_mod_unsigned_in_bounds
        NL_MOD => Some(Term::implies(
            Term::and([Term::le(zero(), x.clone()), Term::lt(zero(), y.clone())]),
            Term::and([Term::le(zero(), call.clone()), Term::lt(call, y.clone())]),
        )),
        _ => None,
    }
}

/// Does `pred` hold for `e` or any of its subexpressions?
fn any_expr(e: &Expr, pred: &dyn Fn(&Expr) -> bool) -> bool {
    e.any(pred)
}

/// Does `ty` contain a mutable reference anywhere?
fn contains_mut_ref(ty: &Ty) -> bool {
    match ty {
        Ty::Bool | Ty::Int(_) | Ty::Unit => false,
        Ty::Tuple(elems) | Ty::Adt(_, elems) => elems.iter().any(contains_mut_ref),
        Ty::Ref { mutable, inner } => *mutable || contains_mut_ref(inner),
        Ty::Param(_) | Ty::MutRef(_) => false,
    }
}

/// Is `stmt` a header of the function in Verus's sense (`vir/src/headers.rs`,
/// `read_header`): a `hide`, or a plain block of nothing but `hide`s? Any
/// other statement, an empty block or a ghost block included, ends the
/// headers.
fn is_header(stmt: &Stmt) -> bool {
    match &stmt.kind {
        StmtKind::Hide { .. } => true,
        StmtKind::Block(block) => {
            !block.stmts.is_empty()
                && block
                    .stmts
                    .iter()
                    .all(|s| matches!(s.kind, StmtKind::Hide { .. }))
        }
        _ => false,
    }
}

/// Verus's `check_decrease` (`recursion.rs`) for integer measures: the
/// callee's measure `now` against the caller's at entry, `before`,
/// lexicographically over the caller's components. Where the shared
/// components are equal, the callee may be called only if it has more
/// components than the caller. As in [`decreased`], equal heights are
/// equal values here.
fn check_decrease(now: &[Term], before: &[Term]) -> Term {
    let mut goal = Term::Bool(before.len() < now.len());
    for (n, b) in now.iter().zip(before).rev() {
        let lower = Term::and([
            Term::le(Term::Int(0), n.clone()),
            Term::lt(n.clone(), b.clone()),
        ]);
        goal = Term::or([lower, Term::and([Term::eq(n.clone(), b.clone()), goal])]);
    }
    goal
}

/// Verus's `check_decrease_height` for integer measures, lexicographic:
/// the first component that differs is at least 0 and smaller than it was.
/// For integers Verus's `height_lt` is `0 <= now < before`, and equal
/// heights stand for equal values here, which only strengthens the goal.
fn decreased(now: &[Term], before: &[Term]) -> Term {
    let mut goal = Term::Bool(false);
    for (n, b) in now.iter().zip(before).rev() {
        let lower = Term::and([
            Term::le(Term::Int(0), n.clone()),
            Term::lt(n.clone(), b.clone()),
        ]);
        goal = Term::or([lower, Term::and([Term::eq(n.clone(), b.clone()), goal])]);
    }
    goal
}

/// Does `term` call one of the `unfoldable` functions?
fn mentions(term: &Term, unfoldable: &Unfoldable<'_>) -> bool {
    let mut found = false;
    term.for_each_call(&mut |name, _| found |= unfoldable.contains_key(name));
    found
}
