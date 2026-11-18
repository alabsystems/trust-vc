//! Where Verus's solver instantiates a spec function's definition.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Verus states every spec function's definition as a quantified axiom
//! that Z3 instantiates by E-matching on applications of the function (for
//! a recursive function, the `rec%f` fuel axioms). Z3 does not instantiate
//! on every application written in a query:
//!
//! * It rewrites the asserted formulas first (`asserted_formulas.cpp`). A
//!   local rewriter folds a comparison of a term with itself, `a == !a`,
//!   complementary literals of `&&` and `||`, `if` with equal branches and
//!   the like; `propagate_values` substitutes every top-level equation and
//!   literal of the formulas into the other formulas. Verus's arithmetic is
//!   the uninterpreted `Add`, `Sub`, ... there, so sums are not normalized.
//!   The applications in a subformula that folds away are gone.
//! * Verus keeps Z3's relevancy level 2, under which E-matching sees only
//!   relevant terms: a true `||` makes one true disjunct relevant, a false
//!   `&&` one false conjunct, an `if` its condition and the branch taken,
//!   and an atom its arguments. An instance makes the terms of its body
//!   relevant in the same way.
//!
//! The generator unfolds definitions itself (see `super::spec`), and an
//! unfolding Z3 never makes would prove what Verus does not. This module
//! gives each application a condition under which Z3 surely has it
//! relevant in the model it is working on:
//!
//! * [`Analysis::seeds`] rewrites a query's formulas with the rules of Z3's
//!   rewriter it knows: identity is decided modulo the congruence closure
//!   of the top-level equations and literals of the other formulas (Z3
//!   substitutes them, which identifies no more), and `x < y` is `!(y <=
//!   x)` throughout.
//! * Z3 has more rules than that list. Every one is an equivalence, so a
//!   subformula it rewrites into one without an application takes one value
//!   whatever the application's value is, in every interpretation of the
//!   facts Z3 substitutes. Those facts follow from the other top-level
//!   formulas. An application stays only where each enclosing subformula
//!   is shown to depend on it, by a witness (`super::witness`): an
//!   interpretation of the other formulas and two values of the
//!   application under which the subformula differs.
//! * Relevance then follows Z3's rules, where every choice Z3 may make has
//!   to keep the application relevant: an application in disjunct `i` of a
//!   true `||` is relevant where every true disjunct has it relevant, and
//!   one in the branch of an `if` only where the condition takes that
//!   branch.
//!
//! The conditions refer to the truth of subformulas through fresh boolean
//! symbols ([`Namer`]), each defined by the subformula it names. Unfolding
//! only where its condition holds keeps the generator's instances within
//! the ones Z3 has in every model it can stop at, so a query the generator
//! refutes, Z3 refutes too.
//!
//! Applications of a non-recursive spec function are instances too: the
//! analysis reads its body where an application is relevant, under the
//! definition's guard, as Z3 does. The query itself keeps those functions
//! inlined (`super::spec::inline`): the definitions are consistent, so a
//! model Z3 stops at extends to one where they hold everywhere. An
//! application found in such a body is carried by the application of the
//! function in the formula: an enclosing subformula has to depend on that.
//!
//! Z3 builds an instance at the representatives of its bindings'
//! congruence classes and rewrites it, so an instance made after a case
//! split has merged two classes may hold two of its body's terms as one
//! (`s(i) == s(1)` built as `s(1) == s(1)`, which folds). The applications
//! of such an instance are relevant only where its arguments keep its
//! body's terms apart ([`Analysis::gate`]). An instance Z3 makes before any
//! split is built after the merges the facts force: its body is read at
//! its arguments with the non-recursive definitions inlined, under the
//! facts with those inlined, with exact arithmetic and with the bounds of
//! the applications whose type bounds them (Z3 instantiates Verus's
//! arithmetic, definition and type axioms as it reads the terms).
//!
//! The analysis reads one query per check, with every earlier fact a
//! top-level formula. Verus's query for a function is one formula in which
//! whatever follows an assertion, a precondition check or a branch sits
//! behind that check's case split ([`Position`]): Z3 makes the instances such
//! a formula reaches after it has split, so none of them is early, and the
//! instance of a callee's `ensures` there is gated like a definition's.

use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::ops::Not;

use crate::ids::FnId;

use super::query::Symbol;
use super::spec::{inline, instantiate, SpecDef};
use super::term::{ArithOp, CmpOp, Sort, Term};
use super::witness::{self, Problem};

mod clip_origins;
mod fact_closure;

/// Where a formula of a query sits in Verus's query for the function.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct Position {
    /// Behind a case split of Verus's query: after an assertion or another
    /// check, or on a branch. No application in it is early ([`early`]).
    pub(crate) late: bool,
    /// For a formula of an instance Z3 makes behind such a split (a
    /// callee's `ensures`, Verus's `ens%f` at the call's arguments): where
    /// the arguments keep its terms apart ([`instance_gate`]). The
    /// applications in the formula are relevant only there.
    pub(crate) gate: Option<Term>,
}

/// How the analysis treats a called function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CallRole {
    /// Its relevant applications are collected with their conditions.
    Collect,
    /// A non-recursive spec function: its body is read where an application
    /// is relevant.
    Defined,
    /// Both: a non-recursive spec function whose relevant applications are
    /// collected and whose body is read there.
    CollectDefined,
    /// Uninterpreted.
    Other,
}

/// Applications and the conditions under which they are relevant, in the
/// order they were found.
#[derive(Debug, Clone, Default)]
pub(crate) struct Conds {
    index: HashMap<Term, usize>,
    items: Vec<Item>,
}

/// One application in [`Conds`].
#[derive(Debug, Clone)]
struct Item {
    call: Term,
    /// The terms of the subformula through which it is reached: the
    /// application itself, or applications of non-recursive spec functions
    /// whose instances reach it.
    carriers: Vec<Term>,
    cond: Term,
}

impl Conds {
    /// `call`, carried by `carriers`, is relevant where `cond` holds,
    /// besides where it was already.
    fn add(&mut self, call: Term, carriers: &[Term], cond: Term) {
        if let Some(&i) = self.index.get(&call) {
            let item = &mut self.items[i];
            let old = std::mem::replace(&mut item.cond, Term::Bool(false));
            item.cond = Term::or([old, cond]);
            for carrier in carriers {
                if !item.carriers.contains(carrier) {
                    item.carriers.push(carrier.clone());
                }
            }
        } else {
            self.index.insert(call.clone(), self.items.len());
            self.items.push(Item {
                call,
                carriers: carriers.to_vec(),
                cond,
            });
        }
    }

    fn merge(&mut self, other: Self) {
        for item in other.items {
            self.add(item.call, &item.carriers, item.cond);
        }
    }

    /// Every condition strengthened by `lit`.
    fn scale(self, lit: &Term) -> Self {
        let mut out = Self::default();
        for item in self.items {
            out.add(
                item.call,
                &item.carriers,
                Term::and([lit.clone(), item.cond]),
            );
        }
        out
    }

    /// The same applications, all carried by `carrier`.
    fn carried_by(self, carrier: &Term) -> Self {
        let mut out = Self::default();
        for item in self.items {
            out.add(item.call, std::slice::from_ref(carrier), item.cond);
        }
        out
    }

    fn get(&self, call: &Term) -> Option<&Item> {
        self.index.get(call).map(|&i| &self.items[i])
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    /// The applications with their conditions.
    pub(crate) fn into_items(self) -> Vec<(Term, Term)> {
        self.items
            .into_iter()
            .map(|item| (item.call, item.cond))
            .collect()
    }
}

/// Fresh boolean symbols of one query and their definitions.
#[derive(Debug, Default)]
pub(crate) struct Namer {
    /// Prefix of the symbols' names; `rv` when empty.
    prefix: &'static str,
    next: u64,
    /// The symbols made.
    symbols: Vec<Symbol>,
    /// Each defined symbol's name and definition.
    definitions: Vec<(String, Term)>,
}

/// Facts with the symbols they still use and those symbols' definitions.
pub(crate) struct Resolved {
    pub(crate) facts: Vec<Term>,
    pub(crate) symbols: Vec<Symbol>,
    pub(crate) definitions: Vec<Term>,
}

impl Namer {
    /// A fresh boolean symbol.
    pub(crate) fn fresh(&mut self) -> Term {
        let prefix = if self.prefix.is_empty() {
            "rv"
        } else {
            self.prefix
        };
        let name = format!("{prefix}{}", self.next);
        self.next = self.next.wrapping_add(1);
        self.symbols.push(Symbol {
            name: name.clone(),
            sort: Sort::Bool,
            display: "relevance".to_string(),
        });
        Term::var(name, Sort::Bool)
    }

    /// Define `symbol`, made by [`Self::fresh`], as `term`.
    pub(crate) fn define(&mut self, symbol: &Term, term: Term) {
        if let Term::Var { name, .. } = symbol {
            self.definitions.push((name.clone(), term));
        }
    }

    /// `facts` with every symbol whose definition expands to at most `cap`
    /// nodes replaced by that expansion; the other symbols stay, declared
    /// and defined. The definitions are acyclic: a relevance symbol refers
    /// to the symbols of the paths into its node, and a named subformula
    /// to none.
    pub(crate) fn resolve(self, facts: Vec<Term>, cap: usize) -> Resolved {
        let mut out = self.resolve_each(facts, cap);
        out.facts.retain(|fact| *fact != Term::Bool(true));
        out
    }

    /// [`Self::resolve`], keeping every fact in its place, `true` ones
    /// included.
    pub(crate) fn resolve_each(self, facts: Vec<Term>, cap: usize) -> Resolved {
        let definitions: HashMap<String, Term> = self.definitions.iter().cloned().collect();
        let mut expansion: HashMap<String, Option<Term>> = HashMap::new();
        let mut kept: HashMap<String, Term> = HashMap::new();
        for (name, _) in &self.definitions {
            expand(name, &definitions, cap, &mut expansion, &mut kept);
        }
        let map: HashMap<&str, Term> = expansion
            .iter()
            .filter_map(|(name, term)| Some((name.as_str(), term.clone()?)))
            .collect();
        let facts = facts.iter().map(|fact| fact.substitute(&map)).collect();
        let symbols = self
            .symbols
            .into_iter()
            .filter(|symbol| kept.contains_key(&symbol.name))
            .collect();
        let definitions = self
            .definitions
            .iter()
            .filter_map(|(name, _)| {
                let term = kept.get(name)?;
                Some(Term::eq(Term::var(name.clone(), Sort::Bool), term.clone()))
            })
            .collect();
        Resolved {
            facts,
            symbols,
            definitions,
        }
    }
}

/// The expansion of symbol `name` (`None` if it stays a symbol, whose
/// definition then goes to `kept`).
fn expand(
    name: &str,
    definitions: &HashMap<String, Term>,
    cap: usize,
    expansion: &mut HashMap<String, Option<Term>>,
    kept: &mut HashMap<String, Term>,
) -> Option<Term> {
    if let Some(done) = expansion.get(name) {
        return done.clone();
    }
    let definition = definitions.get(name)?;
    let mut used = Vec::new();
    vars(definition, &mut used);
    let mut map: HashMap<&str, Term> = HashMap::new();
    for var in &used {
        if definitions.contains_key(var.as_str()) {
            if let Some(term) = expand(var, definitions, cap, expansion, kept) {
                map.insert(var.as_str(), term);
            }
        }
    }
    let term = definition.substitute(&map);
    let out = if term.size() <= cap {
        Some(term)
    } else {
        kept.insert(name.to_string(), term);
        None
    };
    expansion.insert(name.to_string(), out.clone());
    out
}

/// The variables of `t`.
fn vars(t: &Term, out: &mut Vec<String>) {
    match t {
        Term::Var { name, .. } => {
            if !out.contains(name) {
                out.push(name.clone());
            }
        }
        Term::Bool(_) | Term::Int(_) => {}
        Term::Not(a) | Term::Neg(a) => vars(a, out),
        Term::And(cs) | Term::Or(cs) | Term::Call { args: cs, .. } => {
            for c in cs {
                vars(c, out);
            }
        }
        Term::Implies(a, b) | Term::Cmp(_, a, b) | Term::Arith(_, a, b) => {
            vars(a, out);
            vars(b, out);
        }
        Term::Ite(c, a, b, _) => {
            vars(c, out);
            vars(a, out);
            vars(b, out);
        }
    }
}

/// The value a formula takes where its relevance is asked.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Pol {
    True,
    False,
    Either,
}

impl Pol {
    const fn flip(self) -> Self {
        match self {
            Self::True => Self::False,
            Self::False => Self::True,
            Self::Either => Self::Either,
        }
    }
}

/// The relevance analysis of one query.
pub(crate) struct Analysis<'a> {
    role: &'a dyn Fn(&str) -> CallRole,
    defs: &'a HashMap<&'a str, &'a SpecDef>,
    pub(crate) namer: Namer,
    named: HashMap<Term, Term>,
    /// The applications found in the instance at an application, read
    /// from a formula, gated or not, under the inlined facts or not.
    instances: HashMap<(Option<usize>, Term, bool, bool), Conds>,
    budget: usize,
    typing_exhausted: bool,
    /// The query's top-level formulas, each with its index. Z3 substitutes
    /// the equations and literals among them, after its rewriting, into the
    /// others; whatever it substitutes follows from the formula it comes
    /// from, so a witness that satisfies the formulas satisfies it.
    facts: Vec<(usize, Term)>,
    /// `facts` and, where it differs, each one with the non-recursive spec
    /// functions inlined: the facts of an unfolding's body, whose
    /// arguments are inlined, and of an early instance's body ([`early`]).
    /// Built on the first such body.
    every: Option<Vec<(usize, Term)>>,
    /// Reading the body of an early instance, under `every`: Z3 makes the
    /// definitions' instances one at a time, so another definition's
    /// instance may have merged its arguments' classes before it.
    inlined: bool,
    /// The top-level formula being read, or [`EVERY`] in the body of an
    /// unfolding; `None` outside both.
    current: Option<usize>,
    /// Congruence closures of the equations and literals among the
    /// formulas: of all of them (`None`), and of all but a formula's own
    /// (`Some(i)`, for a formula that is one).
    graphs: HashMap<Option<usize>, EGraph>,
    /// Whether a subformula of a formula depends on an application, under
    /// the inlined facts or not.
    depends: HashMap<(Option<usize>, bool, Term, Term), bool>,
    /// The other formulas that bear on a subformula of a formula, among
    /// the inlined facts or not.
    relevant: HashMap<(usize, bool, Term), Vec<usize>>,
    /// Exact connectivity of the immutable original/inlined fact banks.
    fact_indices: [Option<fact_closure::Prepared>; 2],
    /// Evaluation steps left for the witness searches.
    witness_budget: usize,
    /// The collisions of each definition's body ([`collisions`]).
    collisions: HashMap<String, Option<Vec<Collision>>>,
    /// The applications of non-recursive spec functions in the formula
    /// being read that Z3 has relevant before it splits a case
    /// ([`early`]).
    early: HashSet<Term>,
    /// How many instance bodies deep the analysis is reading.
    depth: usize,
    /// The bounds of the functions whose type bounds their values, by name.
    /// The query states them for every application, after this analysis.
    ranged: Option<&'a Ranged>,
    typings: Option<&'a HashMap<String, super::spec::TypingSchema>>,
    type_context: Option<&'a super::val::Ctx<'a>>,
    /// Component functions of one source value, keyed by exact declaration
    /// identity and helper kind rather than by their generated spellings.
    families: Option<&'a HashMap<String, (FnId, bool)>>,
    /// Only exact arithmetic heads requested by typed quantifier templates.
    /// Their subterms must survive the same relevance/witness analysis.
    arithmetic_triggers: Option<&'a HashSet<ArithOp>>,
    clip_triggers: Option<&'a HashSet<crate::IntRange>>,
    clip_origin_sites: clip_origins::Sites,
    #[cfg(test)]
    arithmetic_searches: usize,
    #[cfg(test)]
    fact_closure_calls: usize,
    #[cfg(test)]
    fact_closure_exhaustions: usize,
    #[cfg(test)]
    fact_closure_cache_hits: usize,
    #[cfg(test)]
    fact_closure_input_rows: usize,
    #[cfg(test)]
    fact_closure_passes: usize,
    #[cfg(test)]
    fact_closure_scanned_rows: usize,
    #[cfg(test)]
    fact_closure_work: usize,
}

/// The smallest and largest value of each bounded function, by name.
pub(crate) type Ranged = HashMap<String, (Option<i128>, Option<u128>)>;

/// The analysis ran out of its size budget.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct TooBig;

type R<T> = Result<T, TooBig>;

/// Evaluation steps the witness searches of one query may take; past them
/// every remaining application counts as removed.
const WITNESS_BUDGET: usize = 40_000_000;

/// The `current` of a body read outside the formulas, with every formula a
/// fact.
const EVERY: usize = usize::MAX;

impl<'a> Analysis<'a> {
    pub(crate) fn new(
        role: &'a dyn Fn(&str) -> CallRole,
        defs: &'a HashMap<&'a str, &'a SpecDef>,
        budget: usize,
    ) -> Self {
        Self {
            role,
            defs,
            namer: Namer::default(),
            named: HashMap::new(),
            instances: HashMap::new(),
            budget,
            typing_exhausted: false,
            facts: Vec::new(),
            every: None,
            inlined: false,
            current: None,
            graphs: HashMap::new(),
            depends: HashMap::new(),
            relevant: HashMap::new(),
            fact_indices: [None, None],
            witness_budget: WITNESS_BUDGET,
            collisions: HashMap::new(),
            early: HashSet::new(),
            depth: 0,
            ranged: None,
            typings: None,
            type_context: None,
            families: None,
            arithmetic_triggers: None,
            clip_triggers: None,
            clip_origin_sites: clip_origins::Sites::default(),
            #[cfg(test)]
            arithmetic_searches: 0,
            #[cfg(test)]
            fact_closure_calls: 0,
            #[cfg(test)]
            fact_closure_exhaustions: 0,
            #[cfg(test)]
            fact_closure_cache_hits: 0,
            #[cfg(test)]
            fact_closure_input_rows: 0,
            #[cfg(test)]
            fact_closure_passes: 0,
            #[cfg(test)]
            fact_closure_scanned_rows: 0,
            #[cfg(test)]
            fact_closure_work: 0,
        }
    }

    /// The analysis with its fresh symbols named `<prefix><n>`, apart from
    /// another analysis's in the same query.
    #[must_use]
    pub(crate) const fn with_prefix(mut self, prefix: &'static str) -> Self {
        self.namer.prefix = prefix;
        self
    }

    /// The analysis with the bounds of the functions whose type bounds
    /// their values.
    #[must_use]
    pub(crate) const fn with_ranges(mut self, ranged: &'a Ranged) -> Self {
        self.ranged = Some(ranged);
        self
    }

    #[must_use]
    pub(crate) const fn with_typings(
        mut self,
        typings: &'a HashMap<String, super::spec::TypingSchema>,
    ) -> Self {
        self.typings = Some(typings);
        self
    }

    #[must_use]
    pub(crate) const fn with_type_context(mut self, context: &'a super::val::Ctx<'a>) -> Self {
        self.type_context = Some(context);
        self
    }

    #[must_use]
    pub(crate) const fn with_result_families(
        mut self,
        families: &'a HashMap<String, (FnId, bool)>,
    ) -> Self {
        self.families = Some(families);
        self
    }

    #[must_use]
    pub(crate) const fn with_arithmetic_triggers(mut self, heads: &'a HashSet<ArithOp>) -> Self {
        self.arithmetic_triggers = Some(heads);
        self
    }

    #[must_use]
    pub(crate) const fn with_clip_triggers(mut self, ranges: &'a HashSet<crate::IntRange>) -> Self {
        self.clip_triggers = Some(ranges);
        self
    }

    fn same_application(&self, a: &Term, b: &Term) -> bool {
        if a == b {
            return true;
        }
        let (
            Term::Call {
                name: a, args: aa, ..
            },
            Term::Call {
                name: b, args: ba, ..
            },
        ) = (a, b)
        else {
            return false;
        };
        let Some(families) = self.families else {
            return false;
        };
        aa == ba
            && families
                .get(a)
                .is_some_and(|family| families.get(b) == Some(family))
    }

    /// Where an instance of `def` at `args` keeps the terms of its body
    /// apart: no two subterms that Z3 may build as one term in the instance
    /// are made one ([`collisions`]). Z3 instantiates a definition at the
    /// representatives of its bindings' congruence classes and rewrites the
    /// instance, so where an argument equals a numeral or another argument
    /// when the instance is made, `s(i) == s(1)` may be built as `s(1) ==
    /// s(1)` and fold with its terms. The applications found in the body
    /// are relevant only where this holds; `false` where the body has more
    /// pairs than are worth writing out.
    pub(crate) fn gate(&mut self, def: &SpecDef, args: &[Term]) -> R<Term> {
        let pairs = self
            .collisions
            .entry(def.function.clone())
            .or_insert_with(|| collisions(def))
            .clone();
        let Some(pairs) = pairs else {
            return Ok(Term::Bool(false));
        };
        let map =
            super::substitution::bindings(&def.params, args, &mut self.budget).ok_or(TooBig)?;
        let mut apart = Vec::with_capacity(pairs.len());
        for positions in pairs {
            let mut same = Vec::new();
            for (a, b) in positions {
                same.push(Term::eq(
                    super::substitution::apply(&a, &map, &mut self.budget).ok_or(TooBig)?,
                    super::substitution::apply(&b, &map, &mut self.budget).ok_or(TooBig)?,
                ));
            }
            apart.push(Term::and(same).not());
        }
        Ok(Term::and(apart))
    }

    pub(crate) fn typing_exhausted(&self) -> bool {
        self.typing_exhausted
    }

    fn instantiated(&mut self, definition: &SpecDef, args: &[Term]) -> R<(Term, Term)> {
        let result = instantiate(definition, args, &mut self.budget).and_then(|(guard, body)| {
            match self.type_context {
                Some(context) => Some((
                    context.canonical_type_terms(guard, &mut self.budget)?,
                    context.canonical_type_terms(body, &mut self.budget)?,
                )),
                None => Some((guard, body)),
            }
        });
        match result {
            Some(result) => Ok(result),
            None => {
                self.typing_exhausted = true;
                Err(TooBig)
            }
        }
    }

    pub(super) fn charge(&mut self, cost: usize) -> R<()> {
        self.budget = self.budget.checked_sub(cost).ok_or(TooBig)?;
        Ok(())
    }

    /// The collected applications relevant in the query `hypotheses ==>
    /// goal`, each formula with its place in Verus's query, with their
    /// conditions. The terms are not inlined.
    pub(crate) fn seeds(
        &mut self,
        hypotheses: &[(Term, Position)],
        goal: &(Term, Position),
    ) -> R<Conds> {
        self.fact_indices = [None, None];
        let negated = goal.0.clone().not();
        let all = hypotheses
            .iter()
            .map(|(term, place)| (term, place))
            .chain([(&negated, &goal.1)]);
        let mut formulas = Vec::new();
        let mut places = Vec::new();
        let mut originals = Vec::new();
        let ranges = self.clip_triggers.filter(|ranges| !ranges.is_empty());
        for (k, (term, place)) in all.enumerate() {
            self.charge(term.size())?;
            if ranges.is_some() {
                self.charge(originals.capacity().saturating_add(2))?;
                originals.push((k, term));
            } else {
                let mut parts = Vec::new();
                split(Simp::local().go(term), &mut parts);
                formulas.extend(parts.into_iter().map(|part| (part, k)));
            }
            places.push(place);
        }
        let mut out = Conds::default();
        let formulas = if let Some(ranges) = ranges {
            let mut remaining = self.budget;
            let tracked =
                clip_origins::prepare(originals.into_iter(), ranges, &mut |cost| match remaining
                    .checked_sub(cost)
                {
                    Some(next) => {
                        remaining = next;
                        true
                    }
                    None => {
                        remaining = 0;
                        false
                    }
                });
            self.budget = if tracked.is_err() { 0 } else { remaining };
            let Some(tracked) = tracked? else {
                return Ok(out);
            };
            tracked
        } else {
            let Some(formulas) = propagate(formulas) else {
                return Ok(out);
            };
            formulas
                .into_iter()
                .map(|(term, tag)| clip_origins::Formula::plain(term, tag))
                .collect()
        };
        if formulas
            .iter()
            .any(|formula| formula.term == Term::Bool(false))
        {
            return Ok(out);
        }
        self.facts = formulas
            .iter()
            .map(|formula| formula.term.clone())
            .enumerate()
            .collect();
        for (i, formula) in formulas.iter().enumerate() {
            let place = places[formula.tag];
            let root = &formula.term;
            if place.gate == Some(Term::Bool(false)) {
                continue;
            }
            self.current = Some(i);
            self.early.clear();
            if !place.late {
                early(root, Some(Pol::True), self.role, &mut self.early);
            }
            let mut remaining = self.budget;
            let sites = formula.sites(&mut |cost| match remaining.checked_sub(cost) {
                Some(next) => {
                    remaining = next;
                    true
                }
                None => {
                    remaining = 0;
                    false
                }
            });
            self.budget = if sites.is_err() { 0 } else { remaining };
            self.clip_origin_sites = match sites {
                Ok(sites) => sites,
                Err(problem) => {
                    self.current = None;
                    return Err(problem);
                }
            };
            let found = self.rel(root, Pol::True);
            self.clip_origin_sites = clip_origins::Sites::default();
            self.current = None;
            let mut found = found?;
            if let Some(gate) = &place.gate {
                if !found.is_empty() && *gate != Term::Bool(true) {
                    let named = self.name(gate)?;
                    found = found.scale(&named);
                }
            }
            out.merge(found);
        }
        if self.typing_exhausted {
            return Err(TooBig);
        }
        Ok(out)
    }

    /// The collected applications relevant in an instance `app == body`
    /// of a definition, where the instance is relevant and its guard holds.
    ///
    /// Z3 instantiates at the application after substituting the other
    /// formulas' equations and literals into its arguments, and rewrites
    /// the instance: `w(x)` is `w(1)` where another formula gives `x == 1`,
    /// and `s(1) == s(1)` folds in its instance. So the body's subformulas
    /// are read under the same facts as the formula the application is in;
    /// an unfolding's body, reached from any formula, under all of them.
    /// More facts only leave fewer witnesses, and fewer instances.
    pub(crate) fn body(&mut self, body: &Term) -> R<Conds> {
        self.charge(body.size())?;
        let body = Simp::local().go(body);
        let current = self.current;
        if (current.is_none() || self.inlined) && self.every.is_none() {
            let mut every = self.facts.clone();
            for (i, fact) in &self.facts {
                let mut budget = self.budget;
                let inlined = inline(fact, self.defs, &mut budget).ok_or(TooBig)?;
                self.budget = budget;
                if inlined != *fact {
                    every.push((*i, inlined));
                }
            }
            self.every = Some(every);
        }
        self.current = Some(current.unwrap_or(EVERY));
        self.depth += 1;
        // A seed's occurrence receipts never authorize an expansion body.
        let origins = std::mem::take(&mut self.clip_origin_sites);
        let found = if body.sort() == Sort::Bool {
            self.rel(&body, Pol::Either)
        } else {
            self.term(&body)
        };
        self.clip_origin_sites = origins;
        self.depth -= 1;
        self.current = current;
        if self.typing_exhausted {
            Err(TooBig)
        } else {
            found
        }
    }

    /// A term for the truth of `formula` in the query: a fresh symbol
    /// defined by it, inlined.
    fn name(&mut self, formula: &Term) -> R<Term> {
        match formula {
            Term::Bool(_) | Term::Var { .. } => return Ok(formula.clone()),
            Term::Not(inner) => return Ok(self.name(inner)?.not()),
            _ => {}
        }
        if let Some(symbol) = self.named.get(formula) {
            return Ok(symbol.clone());
        }
        let mut budget = self.budget;
        let inlined = inline(formula, self.defs, &mut budget).ok_or(TooBig)?;
        self.budget = budget;
        self.charge(inlined.size())?;
        let symbol = self.namer.fresh();
        self.namer.define(&symbol, inlined);
        self.named.insert(formula.clone(), symbol.clone());
        Ok(symbol)
    }

    /// Relevance in `f`, where `f` is relevant and takes the value `pol`.
    fn rel(&mut self, f: &Term, pol: Pol) -> R<Conds> {
        self.charge(1)?;
        let found = match f {
            Term::Bool(_) | Term::Int(_) | Term::Var { .. } => return Ok(Conds::default()),
            Term::Not(inner) => return self.rel(inner, pol.flip()),
            Term::Implies(a, b) => {
                let disjunction = Term::Or(vec![(**a).clone().not(), (**b).clone()]);
                return self.rel(&disjunction, pol);
            }
            Term::Call { .. } | Term::Arith(..) | Term::Neg(_) => return self.term(f),
            Term::And(children) => match pol {
                Pol::True => self.union(children, Pol::True)?,
                Pol::False => self.one_of(children, false)?,
                Pol::Either => self.either(f)?,
            },
            Term::Or(children) => match pol {
                Pol::False => self.union(children, Pol::False)?,
                Pol::True => self.one_of(children, true)?,
                Pol::Either => self.either(f)?,
            },
            Term::Cmp(CmpOp::Eq, a, b) if a.sort() == Sort::Bool => {
                let mut out = self.rel(a, Pol::Either)?;
                out.merge(self.rel(b, Pol::Either)?);
                out
            }
            Term::Cmp(_, a, b) => {
                let mut out = self.term(a)?;
                out.merge(self.term(b)?);
                out
            }
            Term::Ite(c, a, b, _) => self.ite(c, a, b, Some(pol))?,
        };
        Ok(self.filter(f, found))
    }

    /// The applications of `found`, found inside `node`, that `node` is
    /// shown to depend on through every one of their carriers.
    fn filter(&mut self, node: &Term, found: Conds) -> Conds {
        if found.is_empty() {
            return found;
        }
        let mut out = Conds::default();
        for item in found.items {
            let kept = item
                .carriers
                .iter()
                .all(|carrier| self.depends_on(node, carrier));
            if kept {
                out.add(item.call, &item.carriers, item.cond);
            }
        }
        out
    }

    /// Whether `node` depends on `carrier`, an application in it, in a way
    /// no rewriting of Z3's removes.
    fn depends_on(&mut self, node: &Term, carrier: &Term) -> bool {
        let mut remaining = self.budget;
        let admitted = (|| -> R<_> {
            let mut pay = |cost| match remaining.checked_sub(cost) {
                Some(next) => {
                    remaining = next;
                    true
                }
                None => {
                    remaining = 0;
                    false
                }
            };
            // Before equality, owned key clones and both cache hashes. These
            // are the same structural operations for calls and arithmetic.
            fact_closure::term_work(node, &mut pay)?;
            fact_closure::term_work(node, &mut pay)?;
            fact_closure::term_work(carrier, &mut pay)?;
            fact_closure::term_work(carrier, &mut pay)?;
            if node == carrier {
                return Ok(None);
            }
            let key = (self.current, self.inlined, node.clone(), carrier.clone());
            let known = self.depends.get(&key).copied();
            Ok(Some((key, known)))
        })();
        self.budget = remaining;
        let key = match admitted {
            Err(_) => return false,
            Ok(None) => return true,
            Ok(Some((_, Some(known)))) => return known,
            Ok(Some((key, None))) => key,
        };
        let found = self.search(node, carrier);
        let mut remaining = self.budget;
        let stored = (|| -> R<()> {
            let mut pay = |cost| match remaining.checked_sub(cost) {
                Some(next) => {
                    remaining = next;
                    true
                }
                None => {
                    remaining = 0;
                    false
                }
            };
            fact_closure::reserve_cache(
                &mut self.depends,
                &mut pay,
                &mut |key: &(Option<usize>, bool, Term, Term), pay| {
                    fact_closure::term_work(&key.2, pay)?;
                    fact_closure::term_work(&key.3, pay)?;
                    Ok(())
                },
            )?;
            if !pay(1) {
                return Err(TooBig);
            }
            self.depends.insert(key, found);
            Ok(())
        })();
        self.budget = remaining;
        stored.is_ok() && found
    }

    fn search(&mut self, node: &Term, carrier: &Term) -> bool {
        if matches!(carrier, Term::Arith(..)) {
            return self.search_arithmetic(node, carrier);
        }
        let Term::Call { name, args, sort } = carrier else {
            return false;
        };
        let facts = match self.relevant_facts(node) {
            Ok(facts) => facts,
            Err(_) => return false,
        };
        // The terms Z3 may identify with the carrier: its copies, calls of
        // its function congruent to it under the other formulas' equations,
        // and calls whose arguments take its arguments' values.
        let mut candidates: Vec<Term> = Vec::new();
        same_calls(node, name, args.len(), &mut candidates);
        let list = self.fact_list();
        for &k in &facts {
            same_calls(&list[k].1, name, args.len(), &mut candidates);
        }
        let mut members: Vec<Term> = vec![carrier.clone()];
        let others = candidates.iter().any(|candidate| candidate != carrier);
        if let (Some(current), true) = (self.current, others) {
            let graph = self.graph(current);
            let id = graph.intern(carrier);
            let class = graph.find(id);
            for candidate in &candidates {
                if !members.contains(candidate) {
                    let id = graph.intern(candidate);
                    if graph.find(id) == class {
                        members.push(candidate.clone());
                    }
                }
            }
        }
        // Calls whose arguments take the carrier's values read its point in
        // the witness already; they only count for the facts left out below.
        let varied = members.len();
        for candidate in candidates {
            if members.contains(&candidate) {
                continue;
            }
            if let Term::Call { args: other, .. } = &candidate {
                if witness::same_values(args, other) {
                    members.push(candidate);
                }
            }
        }
        // A formula that is an equation with a member as a side, or a member
        // as a literal, is left out. Z3 keeps the member a side of some
        // top-level equation or literal (it substitutes only the other side
        // of one, or the member where another formula provides it), where
        // the member is relevant everywhere, so the condition found here
        // adds no instance Z3 lacks. If Z3 folds the formula instead, it
        // holds in every interpretation anyway.
        let pins = |fact: &Term| match fact {
            Term::Cmp(CmpOp::Eq, a, b) => members.contains(&**a) || members.contains(&**b),
            Term::Not(inner) => members.contains(&**inner),
            other => members.contains(other),
        };
        let list = match &self.every {
            Some(every) if self.inlined || self.current == Some(EVERY) => every,
            _ => &self.facts,
        };
        let mut chosen: Vec<&Term> = facts
            .iter()
            .map(|&k| &list[k].1)
            .filter(|fact| !pins(fact))
            .collect();
        // In an early instance's body the witness reads arithmetic exactly
        // and keeps every bounded application within its bounds.
        let exact = self.inlined;
        let bounds = if exact {
            match bounds_of(
                node,
                &chosen,
                self.ranged,
                self.typings,
                self.type_context,
                &mut self.budget,
            ) {
                Ok(bounds) => bounds,
                Err(TooBig) => {
                    self.budget = 0;
                    self.typing_exhausted = true;
                    return false;
                }
            }
        } else {
            Vec::new()
        };
        chosen.extend(bounds.iter());
        let mut roots = chosen.clone();
        roots.push(node);
        let mut bridge_budget = self.budget;
        let bridges = match self.type_context {
            Some(context) => match context.bridge_axioms(&roots, &mut bridge_budget) {
                Some(facts) => facts,
                None => {
                    self.budget = 0;
                    return false;
                }
            },
            None => Vec::new(),
        };
        chosen.extend(bridges.iter());
        let problem = Problem {
            node,
            members: members[..varied].iter().collect(),
            sort: *sort,
            facts: chosen,
            exact,
        };
        let mut budget = self.witness_budget;
        let found = witness::depends(&problem, &mut budget);
        self.budget = bridge_budget;
        self.witness_budget = budget;
        found
    }

    /// Conservative arithmetic-carrier relevance. Unlike the UF path,
    /// retain EVERY relevant fact; do not omit arithmetic pins, invent a
    /// congruence class or apply the UF same-values exclusion. The existing
    /// witness models nonexact arithmetic as its actual operation point and
    /// preserves exact arithmetic when this is an early inlined instance.
    fn search_arithmetic(&mut self, node: &Term, carrier: &Term) -> bool {
        let Term::Arith(_, left, right) = carrier else {
            return false;
        };
        if left.sort() != Sort::Int || right.sort() != Sort::Int {
            return false;
        }
        #[cfg(test)]
        {
            self.arithmetic_searches += 1;
        }
        let facts = match self.relevant_facts(node) {
            Ok(facts) => facts,
            Err(_) => return false,
        };
        if self
            .charge(facts.len().saturating_mul(4).saturating_add(4))
            .is_err()
        {
            return false;
        }
        let list = self.fact_list();
        let mut chosen: Vec<&Term> = facts.iter().map(|&k| &list[k].1).collect();
        let exact = self.inlined;
        let mut bridge_budget = self.budget;
        let mut pay = |cost| match bridge_budget.checked_sub(cost) {
            Some(next) => {
                bridge_budget = next;
                true
            }
            None => false,
        };
        if !super::closed_templates::charge_term(node, &mut pay)
            || !chosen
                .iter()
                .all(|fact| super::closed_templates::charge_term(fact, &mut pay))
        {
            self.budget = 0;
            return false;
        }
        // Typed schema expansion has a separate structured payload. Rather
        // than scan/copy it without admission, conservatively omit this new
        // arithmetic seed where the exact early lane would need it. Existing
        // Call relevance remains untouched.
        if exact && self.typings.is_some_and(|schemas| !schemas.is_empty()) {
            self.budget = bridge_budget;
            return false;
        }
        let bounds = if exact {
            match bounds_of(
                node,
                &chosen,
                self.ranged,
                None,
                self.type_context,
                &mut bridge_budget,
            ) {
                Ok(bounds) => bounds,
                Err(TooBig) => {
                    self.budget = 0;
                    self.typing_exhausted = true;
                    return false;
                }
            }
        } else {
            Vec::new()
        };
        chosen.extend(bounds.iter());
        let mut roots = chosen.clone();
        roots.push(node);
        let bridges = match self.type_context {
            Some(context) => match context.bridge_axioms(&roots, &mut bridge_budget) {
                Some(facts) => facts,
                None => {
                    self.budget = 0;
                    return false;
                }
            },
            None => Vec::new(),
        };
        chosen.extend(bridges.iter());
        let problem = Problem {
            node,
            members: vec![carrier],
            sort: Sort::Int,
            facts: chosen,
            exact,
        };
        let mut budget = self.witness_budget;
        let found = witness::depends(&problem, &mut budget);
        self.budget = bridge_budget;
        self.witness_budget = budget;
        found
    }

    /// The facts the formula being read is checked under.
    fn fact_list(&self) -> &[(usize, Term)] {
        match &self.every {
            Some(every) if self.inlined || self.current == Some(EVERY) => every,
            _ => &self.facts,
        }
    }

    /// The other formulas that bear on `node`, directly or through other
    /// such formulas (the shared prepaid fact_closure helper).
    fn relevant_facts(&mut self, node: &Term) -> R<Vec<usize>> {
        let mut remaining = self.budget;
        let result = (|| -> R<Vec<usize>> {
            let mut pay = |cost| match remaining.checked_sub(cost) {
                Some(next) => {
                    remaining = next;
                    true
                }
                None => {
                    remaining = 0;
                    false
                }
            };
            if !pay(4) {
                return Err(TooBig);
            }
            let Some(current) = self.current else {
                return Ok(Vec::new());
            };
            // Pre-admit the key census/copy/get/hash/equality and later
            // insertion before cloning the structural query term.
            for _ in 0..3 {
                fact_closure::term_work(node, &mut pay)?;
            }
            let key = (current, self.inlined, node.clone());
            if let Some(known) = self.relevant.get(&key) {
                let cost = known
                    .len()
                    .checked_mul(3)
                    .and_then(|n| n.checked_add(1))
                    .ok_or(TooBig)?;
                if !pay(cost) {
                    return Err(TooBig);
                }
                #[cfg(test)]
                {
                    self.fact_closure_cache_hits += 1;
                }
                return Ok(known.clone());
            }
            #[cfg(test)]
            {
                self.fact_closure_calls += 1;
            }
            let closed = {
                #[cfg(test)]
                let mut input_rows = 0usize;
                #[cfg(test)]
                let mut passes = 0usize;
                #[cfg(test)]
                let mut scanned_rows = 0usize;
                #[cfg(test)]
                let mut work = 0usize;
                let mut closure_pay = |cost| {
                    let admitted = pay(cost);
                    #[cfg(test)]
                    if admitted {
                        work += cost;
                    }
                    admitted
                };
                #[cfg(not(test))]
                let mut observer = |_| {};
                #[cfg(test)]
                let mut observer = |event| match event {
                    fact_closure::Event::InputFact => input_rows += 1,
                    fact_closure::Event::Pass => passes += 1,
                    fact_closure::Event::FactRow => scanned_rows += 1,
                };
                let cohort = usize::from(
                    self.every.is_some() && (self.inlined || self.current == Some(EVERY)),
                );
                let closed = (|| {
                    if self.fact_indices[cohort].is_none() {
                        self.fact_indices[cohort] = Some(fact_closure::Prepared::new(
                            self.fact_list(),
                            &mut closure_pay,
                            &mut observer,
                        )?);
                    }
                    self.fact_indices[cohort].as_ref().ok_or(TooBig)?.close(
                        current,
                        node,
                        &mut closure_pay,
                        &mut observer,
                    )
                })();
                #[cfg(test)]
                {
                    self.fact_closure_input_rows += input_rows;
                    self.fact_closure_passes += passes;
                    self.fact_closure_scanned_rows += scanned_rows;
                    self.fact_closure_work += work;
                }
                closed
            };
            let found = match closed {
                Ok(found) => found,
                Err(problem) => {
                    #[cfg(test)]
                    {
                        self.fact_closure_exhaustions += 1;
                    }
                    return Err(problem);
                }
            };
            let cost = found
                .len()
                .checked_mul(3)
                .and_then(|n| n.checked_add(1))
                .ok_or(TooBig)?;
            if !pay(cost) {
                return Err(TooBig);
            }
            fact_closure::reserve_cache(
                &mut self.relevant,
                &mut pay,
                &mut |key: &(usize, bool, Term), pay| {
                    fact_closure::term_work(&key.2, pay)?;
                    Ok(())
                },
            )?;
            self.relevant.insert(key, found.clone());
            Ok(found)
        })();
        self.budget = if result.is_err() { 0 } else { remaining };
        result
    }

    /// The congruence closure of the equations and literals among the
    /// formulas other than formula `current`.
    fn graph(&mut self, current: usize) -> &mut EGraph {
        let own = self
            .facts
            .iter()
            .any(|(i, fact)| *i == current && is_fact(fact));
        let key = own.then_some(current);
        let facts = &self.facts;
        self.graphs.entry(key).or_insert_with(|| {
            let mut graph = EGraph::default();
            for (i, fact) in facts {
                if Some(*i) != key && is_fact(fact) {
                    graph.assert(fact);
                }
            }
            graph
        })
    }

    /// Every child is relevant with the value `pol`.
    fn union(&mut self, children: &[Term], pol: Pol) -> R<Conds> {
        let mut out = Conds::default();
        for child in children {
            out.merge(self.rel(child, pol)?);
        }
        Ok(out)
    }

    /// One child with the value `truth` is relevant (a true `||`, a false
    /// `&&`): an application is relevant where every such child has it
    /// relevant.
    fn one_of(&mut self, children: &[Term], truth: bool) -> R<Conds> {
        let pol = if truth { Pol::True } else { Pol::False };
        let mut maps = Vec::new();
        for child in children {
            maps.push(self.rel(child, pol)?);
        }
        let mut calls: Vec<Term> = Vec::new();
        for map in &maps {
            for item in &map.items {
                if !calls.contains(&item.call) {
                    calls.push(item.call.clone());
                }
            }
        }
        let mut out = Conds::default();
        if calls.is_empty() {
            return Ok(out);
        }
        let mut lits = Vec::new();
        for child in children {
            let named = self.name(child)?;
            lits.push(if truth { named } else { named.not() });
        }
        let mut groups: Vec<Vec<Term>> = Vec::new();
        for call in calls {
            if let Some(group) = groups
                .iter_mut()
                .find(|group| self.same_application(&group[0], &call))
            {
                group.push(call);
            } else {
                groups.push(vec![call]);
            }
        }
        for group in groups {
            self.charge(children.len().saturating_mul(group.len()))?;
            let mut parts = Vec::new();
            for (map, lit) in maps.iter().zip(&lits) {
                // Different projections of one source application still use
                // that application in every selectable child. Requiring each
                // projection separately would make their unfoldings circular.
                let cond = Term::or(
                    group
                        .iter()
                        .filter_map(|call| map.get(call).map(|item| item.cond.clone())),
                );
                parts.push(Term::implies(lit.clone(), cond));
            }
            let condition = Term::and(parts);
            for call in group {
                let mut carriers = Vec::new();
                for map in &maps {
                    if let Some(item) = map.get(&call) {
                        for carrier in &item.carriers {
                            if !carriers.contains(carrier) {
                                carriers.push(carrier.clone());
                            }
                        }
                    }
                }
                out.add(call, &carriers, condition.clone());
            }
        }
        Ok(out)
    }

    /// `f` is relevant with either value.
    fn either(&mut self, f: &Term) -> R<Conds> {
        let when_true = self.rel(f, Pol::True)?;
        let when_false = self.rel(f, Pol::False)?;
        if when_true.is_empty() && when_false.is_empty() {
            return Ok(Conds::default());
        }
        let named = self.name(f)?;
        let mut out = Conds::default();
        for item in when_true.items {
            out.add(
                item.call,
                &item.carriers,
                Term::and([named.clone(), item.cond]),
            );
        }
        for item in when_false.items {
            let cond = Term::and([named.clone().not(), item.cond]);
            out.add(item.call, &item.carriers, cond);
        }
        Ok(out)
    }

    /// `if c { a } else { b }`: the condition is relevant, and the branch
    /// it takes. `pol` is the value of a boolean `if` in a formula; `None`
    /// for one in a term.
    fn ite(&mut self, c: &Term, a: &Term, b: &Term, pol: Option<Pol>) -> R<Conds> {
        let mut out = self.rel(c, Pol::Either)?;
        let (then, other) = match pol {
            Some(pol) => (self.rel(a, pol)?, self.rel(b, pol)?),
            None => (self.term(a)?, self.term(b)?),
        };
        if !then.is_empty() || !other.is_empty() {
            let named = self.name(c)?;
            out.merge(then.scale(&named));
            out.merge(other.scale(&named.not()));
        }
        Ok(out)
    }

    /// Relevance in a term that is relevant.
    fn term(&mut self, e: &Term) -> R<Conds> {
        self.charge(1)?;
        match e {
            Term::Bool(_) | Term::Int(_) | Term::Var { .. } => Ok(Conds::default()),
            // Z3 rewrites an application of an uninterpreted function, and
            // Verus's arithmetic, only in its arguments.
            Term::Call { name, args, .. } => {
                let mut out = Conds::default();
                for arg in args {
                    out.merge(self.term(arg)?);
                }
                match (self.role)(name) {
                    CallRole::Collect => {
                        out.add(e.clone(), std::slice::from_ref(e), Term::Bool(true));
                    }
                    CallRole::Defined => out.merge(self.instance(e, name, args)?.carried_by(e)),
                    CallRole::CollectDefined => {
                        out.add(e.clone(), std::slice::from_ref(e), Term::Bool(true));
                        out.merge(self.instance(e, name, args)?.carried_by(e));
                    }
                    CallRole::Other => {}
                }
                // Mint at this exact still-live occurrence BEFORE any parent
                // merges identical fallback calls from different branches.
                if !self.clip_origin_sites.is_empty() {
                    let mut remaining = self.budget;
                    let minted =
                        clip_origins::mint(&self.clip_origin_sites, e, &mut out, &mut |cost| {
                            match remaining.checked_sub(cost) {
                                Some(next) => {
                                    remaining = next;
                                    true
                                }
                                None => {
                                    remaining = 0;
                                    false
                                }
                            }
                        });
                    self.budget = if minted.is_err() { 0 } else { remaining };
                    minted?;
                }
                Ok(out)
            }
            Term::Arith(op, a, b) => {
                let mut out = self.term(a)?;
                out.merge(self.term(b)?);
                if self
                    .arithmetic_triggers
                    .is_some_and(|heads| heads.contains(op))
                {
                    if !super::closed_templates::charge_term(e, &mut |cost| {
                        self.charge(cost).is_ok()
                    }) {
                        return Err(TooBig);
                    }
                    out.add(e.clone(), std::slice::from_ref(e), Term::Bool(true));
                }
                Ok(out)
            }
            Term::Neg(inner) => self.term(inner),
            Term::Ite(c, a, b, _) => {
                let found = self.ite(c, a, b, None)?;
                let mut out = self.filter(e, found);
                if let Some(ranges) = self.clip_triggers {
                    for range in ranges {
                        let Some(fallback) = super::spec::clip_fallback(e, *range, &mut |cost| {
                            self.charge(cost).is_ok()
                        }) else {
                            continue;
                        };
                        // Both branches are actual children of this exact
                        // canonical ITE and were filtered against the WHOLE
                        // ITE above. A surviving UF value branch can witness
                        // its in-range case too. Bare calls and collapsed Var
                        // images still cannot mint any clip metadata.
                        for (branch, in_range) in [(fallback, false), (a.as_ref(), true)] {
                            if in_range && !matches!(branch, Term::Call { .. }) {
                                continue;
                            }
                            // HashMap lookup reads the whole branch even on
                            // a miss. Charge that walk before borrowing an
                            // item; the clone/add reservation below is separate.
                            if !super::closed_templates::charge_term(branch, &mut |cost| {
                                self.charge(cost).is_ok()
                            }) {
                                self.budget = 0;
                                return Err(TooBig);
                            }
                            let Some(item) = out.get(branch) else {
                                continue;
                            };
                            let mut left = self.budget;
                            let mut pay = |cost| match left.checked_sub(cost) {
                                Some(next) => {
                                    left = next;
                                    true
                                }
                                None => false,
                            };
                            if !super::closed_templates::charge_term(e, &mut pay)
                                || !super::closed_templates::charge_term(&item.cond, &mut pay)
                                || !super::closed_templates::charge_term(c, &mut pay)
                                || !item.carriers.iter().all(|value| {
                                    super::closed_templates::charge_term(value, &mut pay)
                                })
                                || !pay(3)
                            {
                                self.budget = 0;
                                return Err(TooBig);
                            }
                            let selected = if in_range {
                                (**c).clone()
                            } else {
                                (**c).clone().not()
                            };
                            let condition = Term::And(vec![item.cond.clone(), selected]);
                            let carriers = item.carriers.clone();
                            self.budget = left;
                            out.add(e.clone(), &carriers, condition);
                        }
                    }
                }
                Ok(out)
            }
            // A formula in a term, as an argument: its value is unknown.
            Term::Not(_) | Term::And(_) | Term::Or(_) | Term::Implies(..) | Term::Cmp(..) => {
                self.rel(e, Pol::Either)
            }
        }
    }

    /// The instance of a non-recursive definition at a relevant
    /// application `app` (`guard ==> app == body`): the body is relevant
    /// where the guard holds. The guard's own applications are not counted.
    ///
    /// Verus's axiom for a non-recursive definition has no guard but the
    /// function's fuel, so Z3 instantiates at an application of a
    /// top-level formula that is relevant without a case split before it
    /// splits the query's cases. It makes the instances one at a time,
    /// though, and earlier ones may have merged classes already: another
    /// definition's (`v(x) == (x == 1)`, or `u(1) == 1` for an argument
    /// `u(1)`), Verus's arithmetic (`x + 1 == 2` makes `x` 1) or a type's
    /// bounds. The body of such an early instance is read at the arguments
    /// with every definition inlined, under the facts with every definition
    /// inlined, where the witnesses read arithmetic exactly and keep bounded
    /// applications within their bounds, so they account for each class
    /// those force. Every other instance may be made after a split has
    /// merged classes, and is relevant only where its arguments keep its
    /// body's terms apart ([`Self::gate`]).
    fn instance(&mut self, app: &Term, name: &str, args: &[Term]) -> R<Conds> {
        let gated = self.depth > 0 || self.current == Some(EVERY) || !self.early.contains(app);
        let inlined = self.inlined || !gated;
        let key = (self.current, app.clone(), gated, inlined);
        if let Some(done) = self.instances.get(&key) {
            return Ok(done.clone());
        }
        let Some(def) = self.defs.get(name).copied() else {
            return Ok(Conds::default());
        };
        if def.params.len() != args.len() {
            return Ok(Conds::default());
        }
        self.charge(def.body.size().saturating_add(def.guard.size()))?;
        let (guard, body) = if gated {
            self.instantiated(def, args)?
        } else {
            // The instances of the definitions applied in the arguments
            // may come first and merge them with their values.
            let mut budget = self.budget;
            let inlined: Option<Vec<Term>> = args
                .iter()
                .map(|arg| inline(arg, self.defs, &mut budget))
                .collect();
            self.budget = budget;
            self.instantiated(def, &inlined.ok_or(TooBig)?)?
        };
        let outer = std::mem::replace(&mut self.inlined, inlined);
        let found = self.body(&body);
        self.inlined = outer;
        let mut out = found?;
        if !out.is_empty() {
            let gate = if gated {
                self.gate(def, args)?
            } else {
                Term::Bool(true)
            };
            let guard = Term::and([guard, gate]);
            if guard != Term::Bool(true) {
                let named = self.name(&guard)?;
                out = out.scale(&named);
            }
        }
        self.instances.insert(key, out.clone());
        Ok(out)
    }
}

/// The bounds of the applications of bounded functions in `node` and
/// `facts`, each `lo <= f(..) <= hi`.
fn bounds_of(
    node: &Term,
    facts: &[&Term],
    ranged: Option<&Ranged>,
    typings: Option<&HashMap<String, super::spec::TypingSchema>>,
    context: Option<&super::val::Ctx<'_>>,
    budget: &mut usize,
) -> R<Vec<Term>> {
    let mut seen: HashSet<&Term> = HashSet::new();
    subterms(node, &mut seen);
    for fact in facts {
        subterms(fact, &mut seen);
    }
    let mut out = Vec::new();
    for t in seen {
        let fact = match t {
            Term::Call { name, args, .. } => {
                if let Some(schema) = typings.and_then(|schemas| schemas.get(name)) {
                    schema
                        .instantiate(args, budget, context)
                        .map_err(|_| TooBig)?
                } else if let Some(&(lo, hi)) = ranged.and_then(|ranges| ranges.get(name)) {
                    Some(t.within_type_bounds(lo, hi))
                } else {
                    None
                }
            }
            _ => None,
        };
        if let Some(fact) = fact.filter(|fact| *fact != Term::Bool(true)) {
            out.push(fact);
        }
    }
    out.sort_by_key(order_key);
    Ok(out)
}

/// Add to `out` the applications of non-recursive spec functions in `t`
/// that Z3 has relevant without splitting a case, where `t` is relevant
/// with the value `pol` (`None` for a term). A top-level formula holds, so
/// a conjunction's conjuncts do, the arguments of a relevant atom or
/// application are relevant, and so is an `if`'s condition; a disjunct, or
/// a branch, is relevant only once a case is chosen.
fn early(t: &Term, pol: Option<Pol>, role: &dyn Fn(&str) -> CallRole, out: &mut HashSet<Term>) {
    match t {
        Term::Bool(_) | Term::Int(_) | Term::Var { .. } => {}
        Term::Call { name, args, .. } => {
            if matches!(role(name), CallRole::Defined | CallRole::CollectDefined) {
                out.insert(t.clone());
            }
            for arg in args {
                early(arg, None, role, out);
            }
        }
        Term::Arith(_, a, b) => {
            early(a, None, role, out);
            early(b, None, role, out);
        }
        Term::Neg(a) => early(a, None, role, out),
        Term::Not(a) => early(a, pol.map(Pol::flip), role, out),
        Term::And(cs) | Term::Or(cs) => {
            let every = if matches!(t, Term::And(_)) {
                Pol::True
            } else {
                Pol::False
            };
            if pol == Some(every) {
                for c in cs {
                    early(c, pol, role, out);
                }
            }
        }
        Term::Implies(a, b) => {
            if pol == Some(Pol::False) {
                early(a, Some(Pol::True), role, out);
                early(b, Some(Pol::False), role, out);
            }
        }
        Term::Cmp(_, a, b) => {
            let side = if a.sort() == Sort::Bool {
                Some(Pol::Either)
            } else {
                None
            };
            early(a, side, role, out);
            early(b, side, role, out);
        }
        Term::Ite(c, ..) => early(c, Some(Pol::Either), role, out),
    }
}

/// Pairs of subterms of a body that an instance may hold as one term: the
/// positions where the two differ, each a parameter on at least one side.
type Collision = Vec<(Term, Term)>;

/// The most subterm pairs of one body [`collisions`] compares.
const COLLISION_PAIRS: usize = 20_000;

/// The pairs of distinct subterms of `def`'s body that are one term in an
/// instance whose bindings are replaced by their classes' representatives,
/// where those take the values that make them so. Two parameters are one
/// representative where their values are equal. A parameter that is an
/// argument of an application (a boxed `Poly` in Verus's encoding) may be
/// represented by any equal term, such as the box of a numeral the body
/// writes; elsewhere it occurs unboxed (`%I i`), which no rewrite makes a
/// numeral. `None` past [`COLLISION_PAIRS`].
fn collisions(def: &SpecDef) -> Option<Vec<Collision>> {
    let params: HashSet<&str> = def.params.iter().map(|(p, _)| p.as_str()).collect();
    let mut with_params: HashSet<&Term> = HashSet::new();
    parametric(&def.body, &params, &mut with_params);
    let mut all: HashSet<&Term> = HashSet::new();
    subterms(&def.body, &mut all);
    let mut buckets: HashMap<String, Vec<&Term>> = HashMap::new();
    for t in all {
        if !matches!(t, Term::Var { .. }) {
            buckets.entry(head(t)).or_default().push(t);
        }
    }
    let mut out = Vec::new();
    let mut compared = 0usize;
    for bucket in buckets.values_mut() {
        bucket.sort_by_key(|t| order_key(t));
        for (i, u) in bucket.iter().enumerate() {
            for v in &bucket[i + 1..] {
                // Two closed terms are one term only where they are equal.
                if !with_params.contains(u) && !with_params.contains(v) {
                    continue;
                }
                compared += 1;
                if compared > COLLISION_PAIRS {
                    return None;
                }
                let mut positions = Vec::new();
                if unify(u, v, &params, false, &mut positions) && !positions.is_empty() {
                    out.push(positions);
                }
            }
        }
    }
    Some(out)
}

/// Where an instance Z3 makes behind a case split, whose formulas at the
/// instance's arguments are `clauses`, keeps their terms apart: no two
/// subterms that may be one term in the instance are made one. Each
/// variable of the clauses stands for one of the instance's bindings (the
/// call's arguments are named, or numerals). `false` where the clauses
/// have more pairs than are worth writing out.
pub(crate) fn instance_gate(clauses: &[Term]) -> Term {
    let body = Term::and(clauses.to_vec());
    let mut params = Vec::new();
    free_vars(&body, &mut params);
    let def = SpecDef {
        function: String::new(),
        params,
        guard: Term::Bool(true),
        body,
    };
    let Some(pairs) = collisions(&def) else {
        return Term::Bool(false);
    };
    let apart: Vec<Term> = pairs
        .into_iter()
        .map(|positions| {
            let same: Vec<Term> = positions.into_iter().map(|(a, b)| Term::eq(a, b)).collect();
            Term::and(same).not()
        })
        .collect();
    Term::and(apart)
}

/// The variables of `t` with their sorts.
fn free_vars(t: &Term, out: &mut Vec<(String, Sort)>) {
    match t {
        Term::Var { name, sort } => {
            if !out.iter().any(|(seen, _)| seen == name) {
                out.push((name.clone(), *sort));
            }
        }
        Term::Bool(_) | Term::Int(_) => {}
        Term::Not(a) | Term::Neg(a) => free_vars(a, out),
        Term::And(cs) | Term::Or(cs) | Term::Call { args: cs, .. } => {
            for c in cs {
                free_vars(c, out);
            }
        }
        Term::Implies(a, b) | Term::Cmp(_, a, b) | Term::Arith(_, a, b) => {
            free_vars(a, out);
            free_vars(b, out);
        }
        Term::Ite(c, a, b, _) => {
            free_vars(c, out);
            free_vars(a, out);
            free_vars(b, out);
        }
    }
}

/// The subterms of `t` that contain a parameter, other than parameters.
fn parametric<'t>(t: &'t Term, params: &HashSet<&str>, out: &mut HashSet<&'t Term>) -> bool {
    let found = match t {
        Term::Bool(_) | Term::Int(_) => false,
        Term::Var { name, .. } => return params.contains(name.as_str()),
        Term::Not(a) | Term::Neg(a) => parametric(a, params, out),
        Term::And(cs) | Term::Or(cs) | Term::Call { args: cs, .. } => {
            let mut any = false;
            for c in cs {
                any |= parametric(c, params, out);
            }
            any
        }
        Term::Implies(a, b) | Term::Cmp(_, a, b) | Term::Arith(_, a, b) => {
            let x = parametric(a, params, out);
            parametric(b, params, out) || x
        }
        Term::Ite(c, a, b, _) => {
            let x = parametric(c, params, out);
            let y = parametric(a, params, out);
            parametric(b, params, out) || x || y
        }
    };
    if found {
        out.insert(t);
    }
    found
}

/// The operator of `t` with its arity.
fn head(t: &Term) -> String {
    match t {
        Term::Bool(_) | Term::Int(_) | Term::Var { .. } => "leaf".to_string(),
        Term::Not(_) => "not".to_string(),
        Term::Neg(_) => "neg".to_string(),
        Term::And(cs) => format!("and/{}", cs.len()),
        Term::Or(cs) => format!("or/{}", cs.len()),
        Term::Implies(..) => "implies".to_string(),
        Term::Cmp(op, ..) => format!("cmp/{op:?}"),
        Term::Arith(op, ..) => format!("arith/{op:?}"),
        Term::Ite(..) => "ite".to_string(),
        Term::Call { name, args, .. } => format!("call/{name}/{}", args.len()),
    }
}

/// Whether `u` and `v` may be one term in an instance, adding to `out`
/// the positions where they differ. `boxed`: they are arguments of an
/// application.
fn unify(u: &Term, v: &Term, params: &HashSet<&str>, boxed: bool, out: &mut Collision) -> bool {
    if u == v {
        return true;
    }
    let param = |t: &Term| matches!(t, Term::Var { name, .. } if params.contains(name.as_str()));
    match (param(u), param(v)) {
        (true, true) => {
            out.push((u.clone(), v.clone()));
            return true;
        }
        (true, false) | (false, true) => {
            let (p, t) = if param(u) { (u, v) } else { (v, u) };
            let mut used = Vec::new();
            vars(t, &mut used);
            let Term::Var { name, .. } = p else {
                return false;
            };
            if boxed && !used.contains(name) {
                out.push((p.clone(), t.clone()));
                return true;
            }
            return false;
        }
        (false, false) => {}
    }
    let mark = out.len();
    let ok = match (u, v) {
        (Term::Not(a), Term::Not(b)) | (Term::Neg(a), Term::Neg(b)) => {
            unify(a, b, params, false, out)
        }
        (Term::And(xs), Term::And(ys)) | (Term::Or(xs), Term::Or(ys)) => {
            xs.len() == ys.len()
                && xs
                    .iter()
                    .zip(ys)
                    .all(|(x, y)| unify(x, y, params, false, out))
        }
        (Term::Implies(a1, b1), Term::Implies(a2, b2)) => {
            unify(a1, a2, params, false, out) && unify(b1, b2, params, false, out)
        }
        (Term::Arith(o1, a1, b1), Term::Arith(o2, a2, b2)) if o1 == o2 => {
            unify(a1, a2, params, false, out) && unify(b1, b2, params, false, out)
        }
        (Term::Cmp(o1, a1, b1), Term::Cmp(o2, a2, b2)) if o1 == o2 => {
            let straight = unify(a1, a2, params, false, out) && unify(b1, b2, params, false, out);
            // Z3 orders the sides of an equation.
            if !straight && *o1 == CmpOp::Eq {
                out.truncate(mark);
                unify(a1, b2, params, false, out) && unify(b1, a2, params, false, out)
            } else {
                straight
            }
        }
        (Term::Ite(c1, a1, b1, _), Term::Ite(c2, a2, b2, _)) => {
            unify(c1, c2, params, false, out)
                && unify(a1, a2, params, false, out)
                && unify(b1, b2, params, false, out)
        }
        (
            Term::Call {
                name: n1, args: x1, ..
            },
            Term::Call {
                name: n2, args: x2, ..
            },
        ) => {
            n1 == n2
                && x1.len() == x2.len()
                && x1
                    .iter()
                    .zip(x2)
                    .all(|(x, y)| unify(x, y, params, true, out))
        }
        _ => false,
    };
    if !ok {
        out.truncate(mark);
    }
    ok
}

/// Whether `formula`, a top-level formula, is an equation or a literal,
/// which Z3 substitutes into the others.
fn is_fact(formula: &Term) -> bool {
    let atom = match formula {
        Term::Not(inner) => &**inner,
        other => other,
    };
    match atom {
        Term::Cmp(..) => true,
        Term::Var { sort, .. } | Term::Call { sort, .. } => *sort == Sort::Bool,
        _ => false,
    }
}

/// The calls of `name` with `arity` arguments in `t`, added to `out` once.
fn same_calls(t: &Term, name: &str, arity: usize, out: &mut Vec<Term>) {
    match t {
        Term::Bool(_) | Term::Int(_) | Term::Var { .. } => {}
        Term::Not(a) | Term::Neg(a) => same_calls(a, name, arity, out),
        Term::And(cs) | Term::Or(cs) => {
            for c in cs {
                same_calls(c, name, arity, out);
            }
        }
        Term::Implies(a, b) | Term::Cmp(_, a, b) | Term::Arith(_, a, b) => {
            same_calls(a, name, arity, out);
            same_calls(b, name, arity, out);
        }
        Term::Ite(c, a, b, _) => {
            same_calls(c, name, arity, out);
            same_calls(a, name, arity, out);
            same_calls(b, name, arity, out);
        }
        Term::Call { name: f, args, .. } => {
            for arg in args {
                same_calls(arg, name, arity, out);
            }
            if f == name && args.len() == arity && !out.contains(t) {
                out.push(t.clone());
            }
        }
    }
}

/// The subterms of `t` other than literals.
fn subterms<'t>(t: &'t Term, out: &mut HashSet<&'t Term>) {
    if matches!(t, Term::Bool(_) | Term::Int(_)) || !out.insert(t) {
        return;
    }
    match t {
        Term::Bool(_) | Term::Int(_) | Term::Var { .. } => {}
        Term::Not(a) | Term::Neg(a) => subterms(a, out),
        Term::And(cs) | Term::Or(cs) | Term::Call { args: cs, .. } => {
            for c in cs {
                subterms(c, out);
            }
        }
        Term::Implies(a, b) | Term::Cmp(_, a, b) | Term::Arith(_, a, b) => {
            subterms(a, out);
            subterms(b, out);
        }
        Term::Ite(c, a, b, _) => {
            subterms(c, out);
            subterms(a, out);
            subterms(b, out);
        }
    }
}

/// Split asserted formulas into Z3's top-level conjuncts.
fn split(f: Term, out: &mut Vec<Term>) {
    match f {
        Term::Bool(true) => {}
        Term::And(children) => {
            for child in children {
                split(child, out);
            }
        }
        Term::Not(inner) => match *inner {
            Term::Or(children) => {
                for child in children {
                    split(Simp::local().go(&child.not()), out);
                }
            }
            Term::Implies(a, b) => {
                split(*a, out);
                split(Simp::local().go(&(*b).not()), out);
            }
            other => out.push(Term::Not(Box::new(other))),
        },
        other => out.push(other),
    }
}

/// Z3's `propagate_values`, by congruence: each formula is rewritten with
/// the equations and literals of the formulas before it, then with those
/// after it, until nothing changes. A formula is never rewritten with
/// itself. Each formula keeps its tag `P`; `None` where the formulas
/// contradict each other.
fn propagate<P: Copy>(mut formulas: Vec<(Term, P)>) -> Option<Vec<(Term, P)>> {
    for _ in 0..8 {
        let mut changed = false;
        for backward in [false, true] {
            let mut graph = EGraph::default();
            let order: Vec<usize> = if backward {
                (0..formulas.len()).rev().collect()
            } else {
                (0..formulas.len()).collect()
            };
            for i in order {
                let new = Simp::with(&mut graph).go(&formulas[i].0);
                if new != formulas[i].0 {
                    changed = true;
                    formulas[i].0 = new;
                }
                graph.assert(&formulas[i].0);
                if graph.inconsistent {
                    return None;
                }
            }
        }
        let mut again = Vec::new();
        for (formula, tag) in formulas {
            let mut parts = Vec::new();
            split(formula, &mut parts);
            again.extend(parts.into_iter().map(|part| (part, tag)));
        }
        formulas = again;
        if !changed {
            break;
        }
    }
    Some(formulas)
}

/// A node operator of the congruence graph.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Op {
    Lit(Term),
    Var(String),
    Not,
    And,
    Or,
    Implies,
    Cmp(CmpOp),
    Arith(ArithOp),
    Neg,
    Ite,
    Call(String),
}

/// The operator and children of a term.
fn parts(t: &Term) -> (Op, Vec<&Term>) {
    match t {
        Term::Bool(_) | Term::Int(_) => (Op::Lit(t.clone()), Vec::new()),
        Term::Var { name, .. } => (Op::Var(name.clone()), Vec::new()),
        Term::Not(a) => (Op::Not, vec![&**a]),
        Term::And(cs) => (Op::And, cs.iter().collect()),
        Term::Or(cs) => (Op::Or, cs.iter().collect()),
        Term::Implies(a, b) => (Op::Implies, vec![&**a, &**b]),
        Term::Cmp(op, a, b) => (Op::Cmp(*op), vec![&**a, &**b]),
        Term::Arith(op, a, b) => (Op::Arith(*op), vec![&**a, &**b]),
        Term::Neg(a) => (Op::Neg, vec![&**a]),
        Term::Ite(c, a, b, _) => (Op::Ite, vec![&**c, &**a, &**b]),
        Term::Call { name, args, .. } => (Op::Call(name.clone()), args.iter().collect()),
    }
}

/// Congruence closure over terms, with the literal of each class.
#[derive(Debug, Default)]
struct EGraph {
    parent: Vec<usize>,
    nodes: Vec<(Op, Vec<usize>)>,
    table: HashMap<(Op, Vec<usize>), usize>,
    uses: Vec<Vec<usize>>,
    lit: Vec<Option<Term>>,
    memo: HashMap<Term, usize>,
    inconsistent: bool,
}

impl EGraph {
    fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            let up = self.parent[self.parent[x]];
            self.parent[x] = up;
            x = up;
        }
        x
    }

    fn intern(&mut self, t: &Term) -> usize {
        if let Some(&id) = self.memo.get(t) {
            return id;
        }
        let (op, children) = parts(t);
        let kids: Vec<usize> = children.into_iter().map(|c| self.intern(c)).collect();
        let id = self.make(op, kids);
        self.memo.insert(t.clone(), id);
        id
    }

    fn make(&mut self, op: Op, kids: Vec<usize>) -> usize {
        let canon: Vec<usize> = kids.iter().map(|&k| self.find(k)).collect();
        let key = (op, canon);
        if let Some(&id) = self.table.get(&key) {
            return id;
        }
        let id = self.nodes.len();
        self.parent.push(id);
        self.uses.push(Vec::new());
        self.lit.push(match &key.0 {
            Op::Lit(t) => Some(t.clone()),
            _ => None,
        });
        for &k in &key.1 {
            if !self.uses[k].contains(&id) {
                self.uses[k].push(id);
            }
        }
        self.nodes.push(key.clone());
        self.table.insert(key, id);
        id
    }

    fn union(&mut self, a: usize, b: usize) {
        let mut pending = vec![(a, b)];
        while let Some((a, b)) = pending.pop() {
            let (ra, rb) = (self.find(a), self.find(b));
            if ra == rb {
                continue;
            }
            let (big, small) = if self.uses[ra].len() >= self.uses[rb].len() {
                (ra, rb)
            } else {
                (rb, ra)
            };
            self.parent[small] = big;
            match (self.lit[big].clone(), self.lit[small].take()) {
                (Some(x), Some(y)) if x != y => self.inconsistent = true,
                (None, Some(y)) => self.lit[big] = Some(y),
                _ => {}
            }
            let moved = std::mem::take(&mut self.uses[small]);
            for user in moved {
                let (op, kids) = self.nodes[user].clone();
                let canon: Vec<usize> = kids.iter().map(|&k| self.find(k)).collect();
                let key = (op, canon);
                match self.table.get(&key) {
                    Some(&other) => {
                        if self.find(other) != self.find(user) {
                            pending.push((user, other));
                        }
                    }
                    None => {
                        self.table.insert(key, user);
                    }
                }
                self.uses[big].push(user);
            }
        }
    }

    /// Record that the formula `f` holds.
    fn assert(&mut self, f: &Term) {
        let truth = self.intern(&Term::Bool(true));
        match f {
            Term::Bool(true) => {}
            Term::Bool(false) => self.inconsistent = true,
            Term::Cmp(CmpOp::Eq, a, b) => {
                let (x, y) = (self.intern(a), self.intern(b));
                self.union(x, y);
                let node = self.intern(f);
                self.union(node, truth);
            }
            Term::Not(inner) => {
                let falsity = self.intern(&Term::Bool(false));
                let node = self.intern(inner);
                self.union(node, falsity);
            }
            _ => {
                let node = self.intern(f);
                self.union(node, truth);
            }
        }
    }
}

/// Z3's local rewriting, optionally modulo a congruence graph.
struct Simp<'g> {
    graph: Option<&'g mut EGraph>,
}

impl<'g> Simp<'g> {
    const fn local() -> Self {
        Self { graph: None }
    }

    fn with(graph: &'g mut EGraph) -> Self {
        Self { graph: Some(graph) }
    }

    fn class(&mut self, t: &Term) -> Option<usize> {
        let graph = self.graph.as_deref_mut()?;
        let id = graph.intern(t);
        Some(graph.find(id))
    }

    fn same(&mut self, a: &Term, b: &Term) -> bool {
        if a == b {
            return true;
        }
        match (self.class(a), self.class(b)) {
            (Some(x), Some(y)) => x == y,
            _ => false,
        }
    }

    fn class_lit(&mut self, t: &Term) -> Option<Term> {
        let class = self.class(t)?;
        self.graph.as_deref()?.lit[class].clone()
    }

    fn go(&mut self, t: &Term) -> Term {
        self.go_observed(t, None, &mut |_| true)
            .expect("an unobserved scalar rewrite has no fallible observer")
    }

    fn go_observed(
        &mut self,
        t: &Term,
        mut trace: Option<&mut clip_origins::Trace<'_>>,
        work: &mut dyn FnMut(usize) -> bool,
    ) -> R<Term> {
        if let Some(observer) = trace.as_deref_mut() {
            observer.enter(t, work)?
        }
        let literal = matches!(t, Term::Bool(_) | Term::Int(_));
        let out = match t {
            Term::Bool(_) | Term::Int(_) => t.clone(),
            Term::Var { .. } => t.clone(),
            Term::Not(a) => self.go_observed(a, trace.as_deref_mut(), work)?.not(),
            Term::And(cs) => {
                let cs = cs
                    .iter()
                    .map(|c| self.go_observed(c, trace.as_deref_mut(), work))
                    .collect::<R<Vec<_>>>()?;
                self.junction(cs, true)
            }
            Term::Or(cs) => {
                let cs = cs
                    .iter()
                    .map(|c| self.go_observed(c, trace.as_deref_mut(), work))
                    .collect::<R<Vec<_>>>()?;
                self.junction(cs, false)
            }
            Term::Implies(a, b) => {
                let a = self.go_observed(a, trace.as_deref_mut(), work)?.not();
                let b = self.go_observed(b, trace.as_deref_mut(), work)?;
                self.junction(vec![a, b], false)
            }
            Term::Cmp(op, a, b) => {
                let (a, b) = (
                    self.go_observed(a, trace.as_deref_mut(), work)?,
                    self.go_observed(b, trace.as_deref_mut(), work)?,
                );
                self.cmp(*op, a, b)
            }
            Term::Arith(op, a, b) => Term::arith(
                *op,
                self.go_observed(a, trace.as_deref_mut(), work)?,
                self.go_observed(b, trace.as_deref_mut(), work)?,
            ),
            Term::Neg(a) => -self.go_observed(a, trace.as_deref_mut(), work)?,
            Term::Ite(c, a, b, _) => {
                let (c, a, b) = (
                    self.go_observed(c, trace.as_deref_mut(), work)?,
                    self.go_observed(a, trace.as_deref_mut(), work)?,
                    self.go_observed(b, trace.as_deref_mut(), work)?,
                );
                self.ite(c, a, b)
            }
            Term::Call { name, args, sort } => {
                let args = args
                    .iter()
                    .map(|a| self.go_observed(a, trace.as_deref_mut(), work))
                    .collect::<R<Vec<_>>>()?;
                Term::call(name.clone(), args, *sort)
            }
        };
        // Observe the FINAL return, after congruence literal replacement.
        let out = if literal {
            out
        } else {
            self.class_lit(&out).unwrap_or(out)
        };
        if let Some(observer) = trace {
            observer.exit(t, &out, work)?
        }
        Ok(out)
    }

    /// `&&` (`is_and`) or `||` of simplified children: flattened, units
    /// dropped, duplicates merged, and folded on a complementary pair.
    fn junction(&mut self, children: Vec<Term>, is_and: bool) -> Term {
        let (unit, absorbing) = (is_and, !is_and);
        let mut flat = Vec::new();
        for child in children {
            match child {
                Term::Bool(value) if value == unit => {}
                Term::Bool(_) => return Term::Bool(absorbing),
                Term::And(inner) if is_and => flat.extend(inner),
                Term::Or(inner) if !is_and => flat.extend(inner),
                other => flat.push(other),
            }
        }
        let mut seen: Vec<(bool, Term)> = Vec::new();
        let mut out = Vec::new();
        for child in flat {
            let (positive, atom) = match &child {
                Term::Not(inner) => (false, (**inner).clone()),
                other => (true, other.clone()),
            };
            let mut duplicate = false;
            for (earlier_positive, earlier) in &seen {
                if self.same(earlier, &atom) {
                    if *earlier_positive == positive {
                        duplicate = true;
                    } else {
                        return Term::Bool(absorbing);
                    }
                }
            }
            if !duplicate {
                seen.push((positive, atom));
                out.push(child);
            }
        }
        match out.len() {
            0 => Term::Bool(unit),
            1 => out.pop().unwrap_or(Term::Bool(unit)),
            _ if is_and => Term::And(out),
            _ => Term::Or(out),
        }
    }

    fn cmp(&mut self, op: CmpOp, a: Term, b: Term) -> Term {
        if op == CmpOp::Eq && a.sort() == Sort::Bool {
            return self.bool_eq(a, b);
        }
        // Z3 keeps a numeral on the right of an equation.
        let (a, b) = if op == CmpOp::Eq && a.as_int().is_some() && b.as_int().is_none() {
            (b, a)
        } else {
            (a, b)
        };
        if let (Some(x), Some(y)) = (a.as_int(), b.as_int()) {
            return Term::Bool(match op {
                CmpOp::Eq => x == y,
                CmpOp::Lt => x < y,
                CmpOp::Le => x <= y,
            });
        }
        // An `if` whose leaves are numerals, compared with numerals, is
        // compared leaf by leaf: Z3 folds it where every leaf agrees.
        if is_value_tree(&a) && is_value_tree(&b) {
            if let Term::Ite(c, x, y, _) = a {
                let x = self.cmp(op, *x, b.clone());
                let y = self.cmp(op, *y, b);
                return self.ite(*c, x, y);
            }
            if let Term::Ite(c, x, y, _) = b {
                let x = self.cmp(op, a.clone(), *x);
                let y = self.cmp(op, a, *y);
                return self.ite(*c, x, y);
            }
        }
        let same = self.same(&a, &b);
        match op {
            CmpOp::Eq | CmpOp::Le if same => Term::Bool(true),
            CmpOp::Lt if same => Term::Bool(false),
            // Z3 reads `a < b` as `!(b <= a)`.
            CmpOp::Lt => {
                let le = Term::Cmp(CmpOp::Le, Box::new(b), Box::new(a));
                self.class_lit(&le).unwrap_or(le).not()
            }
            _ => Term::Cmp(op, Box::new(a), Box::new(b)),
        }
    }

    fn bool_eq(&mut self, a: Term, b: Term) -> Term {
        if self.same(&a, &b) {
            return Term::Bool(true);
        }
        match (a.as_bool(), b.as_bool()) {
            (Some(x), Some(y)) => return Term::Bool(x == y),
            (Some(true), _) => return b,
            (Some(false), _) => return b.not(),
            (_, Some(true)) => return a,
            (_, Some(false)) => return a.not(),
            _ => {}
        }
        let (pa, xa) = strip_not(&a);
        let (pb, xb) = strip_not(&b);
        if self.same(&xa, &xb) {
            return Term::Bool(pa == pb);
        }
        // Z3 takes the negations out of an equation of booleans and orders
        // its sides, so equations that differ in either are one term.
        let (x, y) = if order_key(&xa) <= order_key(&xb) {
            (xa, xb)
        } else {
            (xb, xa)
        };
        let eq = Term::Cmp(CmpOp::Eq, Box::new(x), Box::new(y));
        let eq = self.class_lit(&eq).unwrap_or(eq);
        if pa == pb {
            eq
        } else {
            eq.not()
        }
    }

    fn ite(&mut self, c: Term, a: Term, b: Term) -> Term {
        match c.as_bool() {
            Some(true) => return a,
            Some(false) => return b,
            None => {}
        }
        if let Term::Not(inner) = c {
            return self.ite(*inner, b, a);
        }
        let a = match a {
            Term::Ite(c2, a2, _, _) if self.same(&c, &c2) => *a2,
            other => other,
        };
        let b = match b {
            Term::Ite(c2, _, b2, _) if self.same(&c, &c2) => *b2,
            other => other,
        };
        if self.same(&a, &b) {
            return a;
        }
        if a.sort() == Sort::Bool {
            // `if c { t } else { !t }` is `c == t`.
            let (pa, xa) = strip_not(&a);
            let (pb, xb) = strip_not(&b);
            if pa != pb && self.same(&xa, &xb) {
                return self.bool_eq(c, a);
            }
            match (a.as_bool(), b.as_bool()) {
                (Some(true), Some(false)) => return c,
                (Some(false), Some(true)) => return c.not(),
                (Some(true), _) => return self.junction(vec![c, b], false),
                (Some(false), _) => return self.junction(vec![c.not(), b], true),
                (_, Some(true)) => return self.junction(vec![c.not(), a], false),
                (_, Some(false)) => return self.junction(vec![c, a], true),
                _ => {}
            }
        }
        let sort = a.sort();
        Term::Ite(Box::new(c), Box::new(a), Box::new(b), sort)
    }
}

/// `(true, t)` for a term `t`, `(false, t)` for `!t`.
fn strip_not(t: &Term) -> (bool, Term) {
    match t {
        Term::Not(inner) => (false, (**inner).clone()),
        other => (true, other.clone()),
    }
}

/// A numeral, or an `if` whose leaves are numerals.
fn is_value_tree(t: &Term) -> bool {
    match t {
        Term::Int(_) => true,
        Term::Ite(_, a, b, _) => is_value_tree(a) && is_value_tree(b),
        _ => false,
    }
}

/// A fixed order on terms, for the sides of a symmetric operator.
fn order_key(t: &Term) -> u64 {
    let mut hasher = DefaultHasher::new();
    t.hash(&mut hasher);
    hasher.finish()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s(n: i128) -> Term {
        Term::call("sf0", vec![Term::Int(n)], Sort::Int)
    }

    fn b(name: &str) -> Term {
        Term::var(name, Sort::Bool)
    }

    fn x() -> Term {
        Term::var("x", Sort::Int)
    }

    fn collect(name: &str) -> CallRole {
        if name == "sf0" {
            CallRole::Collect
        } else {
            CallRole::Other
        }
    }

    fn early_all(hypotheses: &[Term], goal: &Term) -> (Vec<(Term, Position)>, (Term, Position)) {
        let hypotheses = hypotheses
            .iter()
            .map(|h| (h.clone(), Position::default()))
            .collect();
        (hypotheses, (goal.clone(), Position::default()))
    }

    fn seeds(hypotheses: &[Term], goal: &Term) -> Vec<(String, String)> {
        let defs = HashMap::new();
        let mut analysis = Analysis::new(&collect, &defs, 100_000);
        let (hypotheses, goal) = early_all(hypotheses, goal);
        let found = analysis.seeds(&hypotheses, &goal).unwrap();
        found
            .into_items()
            .into_iter()
            .map(|(call, cond)| (call.to_string(), cond.to_string()))
            .collect()
    }

    #[test]
    fn trivial_comparisons_fold() {
        let mut simp = Simp::local();
        assert_eq!(simp.go(&Term::le(s(0), s(0))), Term::Bool(true));
        assert_eq!(simp.go(&Term::lt(s(0), s(0))), Term::Bool(false));
        let p = Term::call("bf", vec![Term::Int(0)], Sort::Bool);
        let eqneg = Term::Cmp(CmpOp::Eq, Box::new(p.clone()), Box::new(p.clone().not()));
        assert_eq!(simp.go(&eqneg), Term::Bool(false));
        // `s(0) >= 0 || s(0) < 0`
        let tautology = Term::or([Term::le(Term::Int(0), s(0)), Term::lt(s(0), Term::Int(0))]);
        assert_eq!(simp.go(&tautology), Term::Bool(true));
        // Arithmetic is not normalized: Verus's `Add` is uninterpreted.
        let add = Term::arith(ArithOp::Add, s(0), Term::Int(1));
        assert!(matches!(simp.go(&Term::lt(s(0), add)), Term::Not(_)));
    }

    #[test]
    fn rewritten_applications_are_not_seeds() {
        let both = Term::and([Term::le(s(0), s(0)), Term::le(s(1), s(1))]);
        let goal = Term::eq(s(2), Term::Int(3));
        let found = seeds(&[both], &goal);
        assert_eq!(found, vec![("(sf0 2)".to_string(), "true".to_string())]);
    }

    #[test]
    fn equations_propagate() {
        // `x == 0` makes `s(x) <= s(0)` true.
        let hyps = [
            Term::eq(x(), Term::Int(0)),
            Term::le(Term::call("sf0", vec![x()], Sort::Int), s(0)),
        ];
        let found = seeds(&hyps, &Term::eq(s(2), Term::Int(3)));
        assert_eq!(found.len(), 1);
        assert_eq!(found[0].0, "(sf0 2)");
    }

    #[test]
    fn a_disjunct_is_relevant_where_the_others_are_false() {
        let hyp = Term::or([b("c"), Term::eq(s(1), Term::Int(1))]);
        let found = seeds(&[hyp], &Term::eq(s(2), Term::Int(3)));
        assert_eq!(found[0], ("(sf0 1)".to_string(), "(not c)".to_string()));
        // A guarded fact is relevant where its guard holds.
        let fact = Term::implies(b("c"), Term::eq(s(1), Term::Int(1)));
        let found = seeds(&[fact], &Term::eq(s(2), Term::Int(3)));
        assert_eq!(found[0], ("(sf0 1)".to_string(), "c".to_string()));
    }

    #[test]
    fn a_branch_is_relevant_where_it_is_taken() {
        let value = Term::ite(b("c"), s(1), s(0));
        let hyp = Term::eq(x(), value);
        let found = seeds(&[hyp], &Term::Bool(false));
        assert_eq!(found[0], ("(sf0 1)".to_string(), "c".to_string()));
        assert_eq!(found[1], ("(sf0 0)".to_string(), "(not c)".to_string()));
    }

    fn gt7(t: Term) -> Term {
        Term::lt(Term::Int(7), t)
    }

    fn values(c: Term) -> Term {
        Term::ite(c, Term::Int(1), Term::Int(2))
    }

    #[test]
    fn numeral_ifs_compared_with_numerals_fold() {
        let mut simp = Simp::local();
        let ne3 = Term::eq(values(gt7(s(1))), Term::Int(3)).not();
        assert_eq!(simp.go(&ne3), Term::Bool(true));
        let le3 = Term::le(values(gt7(s(1))), Term::Int(3));
        assert_eq!(simp.go(&le3), Term::Bool(true));
        let nested = Term::ite(b("c"), values(gt7(s(1))), Term::Int(3));
        assert_eq!(simp.go(&Term::le(nested, Term::Int(3))), Term::Bool(true));
        // Where the branches disagree, the condition is what is left.
        let eq1 = Term::eq(values(b("c")), Term::Int(1));
        assert_eq!(simp.go(&eq1), b("c"));
    }

    #[test]
    fn complementary_branches_fold() {
        let mut simp = Simp::local();
        let p = gt7(s(1));
        let ite = Term::Ite(
            Box::new(p.clone()),
            Box::new(p.clone()),
            Box::new(p.clone().not()),
            Sort::Bool,
        );
        assert_eq!(simp.go(&ite), Term::Bool(true));
    }

    #[test]
    fn boolean_equations_are_one_term() {
        let mut simp = Simp::local();
        let p = gt7(s(1));
        let eq = |a: Term, c: Term| Term::Cmp(CmpOp::Eq, Box::new(a), Box::new(c));
        let commuted = eq(eq(p.clone(), b("b")), eq(b("b"), p.clone()));
        assert_eq!(simp.go(&commuted), Term::Bool(true));
        let negated = eq(eq(p.clone(), b("b")).not(), eq(p, b("b").not()));
        assert_eq!(simp.go(&negated), Term::Bool(true));
    }

    #[test]
    fn numerals_go_right() {
        let mut simp = Simp::local();
        let eq = |a: Term, c: Term| Term::Cmp(CmpOp::Eq, Box::new(a), Box::new(c));
        let sides = eq(eq(s(1), Term::Int(1)), eq(Term::Int(1), s(1)));
        assert_eq!(simp.go(&sides), Term::Bool(true));
    }

    #[test]
    fn a_term_a_subformula_does_not_depend_on_is_dropped() {
        // `(s(1) > 7 && c) || (!(s(1) > 7) && c)` is `c`, whatever `s(1)`.
        let p = gt7(s(1));
        let hyp = Term::Or(vec![
            Term::And(vec![p.clone(), b("c")]),
            Term::And(vec![p.not(), b("c")]),
        ]);
        let found = seeds(&[hyp], &Term::eq(s(2), Term::Int(3)));
        assert_eq!(found, vec![("(sf0 2)".to_string(), "true".to_string())]);
        // With a disjunct that tells the cases apart, `s(1)` stays.
        let p = gt7(s(1));
        let hyp = Term::Or(vec![
            Term::And(vec![p.clone(), b("c")]),
            Term::And(vec![p.not(), b("d")]),
        ]);
        let found = seeds(&[hyp], &Term::eq(s(2), Term::Int(3)));
        assert_eq!(found.len(), 2);
    }

    #[test]
    fn substituted_facts_bound_the_witness() {
        // With `x == 1`, `if s(1) > 7 { 1 } else { x } == 1` holds whatever
        // `s(1)` is; `x == 2` leaves it depending on `s(1)`.
        let value = Term::ite(gt7(s(1)), Term::Int(1), x());
        let hyp = Term::eq(value, Term::Int(1));
        let goal = Term::eq(s(2), Term::Int(3));
        let found = seeds(&[Term::eq(x(), Term::Int(1)), hyp.clone()], &goal);
        assert_eq!(found.len(), 1);
        let found = seeds(&[Term::eq(x(), Term::Int(2)), hyp], &goal);
        assert_eq!(found.len(), 2);
        // `1 <= x` makes `0 < x` true, though the two are written apart.
        let hyp = Term::or([Term::lt(Term::Int(0), x()), Term::eq(s(1), Term::Int(1))]);
        let found = seeds(&[Term::le(Term::Int(1), x()), hyp.clone()], &goal);
        assert_eq!(found.len(), 1);
        let found = seeds(&[Term::le(Term::Int(0), x()), hyp], &goal);
        assert_eq!(found.len(), 2);
    }

    #[test]
    fn equations_that_fix_an_application_leave_it_relevant() {
        // `r1 == s(1)` and `r2 == s(1)` each fix `s(1)`; Z3 keeps it as a
        // side of one of them.
        let r = |name: &str| Term::var(name, Sort::Int);
        let hyps = [Term::eq(r("r1"), s(1)), Term::eq(r("r2"), s(1))];
        let found = seeds(&hyps, &Term::eq(s(2), Term::Int(3)));
        assert_eq!(found.len(), 2);
        assert!(found.iter().all(|(_, cond)| cond == "true"));
        // They leave a witness for `s(0)`, whatever value they give `s(1)`.
        let found = seeds(&hyps, &Term::eq(s(0), Term::Int(0)));
        assert!(found.contains(&("(sf0 0)".to_string(), "true".to_string())));
    }

    #[test]
    fn guarded_facts_leave_a_witness() {
        // The facts hold with `c` false and `y == 2`, where `s(0) == 0`
        // still depends on `s(0)`.
        let y = Term::var("y", Sort::Int);
        let hyps = [
            Term::implies(b("c"), Term::eq(s(1), x())),
            Term::le(Term::Int(0), y.clone()),
            Term::implies(b("c"), Term::eq(y.clone(), Term::Int(1))),
            Term::implies(b("c").not(), Term::eq(y, Term::Int(2))),
        ];
        let found = seeds(&hyps, &Term::eq(s(0), Term::Int(0)));
        assert!(found.contains(&("(sf0 0)".to_string(), "true".to_string())));
    }

    fn def(function: &str, body: Term) -> SpecDef {
        SpecDef {
            function: function.to_string(),
            params: vec![("a0".to_string(), Sort::Int), ("a1".to_string(), Sort::Int)],
            guard: Term::Bool(true),
            body,
        }
    }

    #[test]
    fn instances_keep_terms_apart_where_their_arguments_do() {
        let a0 = Term::var("a0", Sort::Int);
        let a1 = Term::var("a1", Sort::Int);
        let call = |arg: Term| Term::call("sf0", vec![arg], Sort::Int);
        let defs = HashMap::new();
        let mut analysis = Analysis::new(&collect, &defs, 100_000);
        // `s(a0) == s(1)` is `s(1) == s(1)` in an instance at 1.
        let body = Term::eq(call(a0.clone()), s(1));
        let gate = analysis
            .gate(&def("rf1", body), &[x(), Term::Int(0)])
            .unwrap();
        assert_eq!(gate.to_string(), "(not (= x 1))");
        // Two parameters are one representative where they are equal.
        let body = Term::le(call(a0.clone()), call(a1.clone()));
        let gate = analysis
            .gate(&def("rf2", body), &[x(), Term::var("y", Sort::Int)])
            .unwrap();
        assert_eq!(gate.to_string(), "(not (= x y))");
        // `s(a0 - 1)` and `s(a0 - 2)` never meet, and an unboxed parameter
        // is never a numeral.
        let minus = |n: i128| Term::arith(ArithOp::Sub, a0.clone(), Term::Int(n));
        let body = Term::and([
            Term::le(call(minus(1)), call(minus(2))),
            Term::eq(a0.clone(), Term::Int(1)),
            Term::eq(Term::Int(1), Term::Int(2)).not(),
            Term::le(call(a0.clone()), Term::Int(3)),
        ]);
        let gate = analysis.gate(&def("rf3", body), &[x(), x()]).unwrap();
        assert_eq!(gate, Term::Bool(true));
        // `a0 == 1` and `!(a1 == 1)` are `p && !p` where the two are equal.
        let body = Term::and([Term::eq(a0, Term::Int(1)), Term::eq(a1, Term::Int(1)).not()]);
        let gate = analysis.gate(&def("rf4", body), &[x(), x()]).unwrap();
        assert_eq!(gate, Term::Bool(false));
    }

    #[test]
    fn early_applications_need_no_case_split() {
        let role = |name: &str| {
            if name == "w" {
                CallRole::Defined
            } else {
                CallRole::Other
            }
        };
        let w = |n: i128| Term::call("w", vec![Term::Int(n)], Sort::Bool);
        let formula = Term::And(vec![
            w(1),
            Term::or([b("c"), w(2)]),
            Term::ite(w(3), w(4), w(5)),
        ]);
        let mut out = HashSet::new();
        early(&formula, Some(Pol::True), &role, &mut out);
        let mut found: Vec<String> = out.iter().map(ToString::to_string).collect();
        found.sort();
        assert_eq!(found, vec!["(w 1)", "(w 3)"]);
    }

    /// `v(i) = i == 1` and `w(i) = s(i) == s(1)`.
    fn wrappers() -> (SpecDef, SpecDef) {
        let a0 = Term::var("a0", Sort::Int);
        let one = |function: &str, body: Term| SpecDef {
            function: function.to_string(),
            params: vec![("a0".to_string(), Sort::Int)],
            guard: Term::Bool(true),
            body,
        };
        let v = one("v", Term::eq(a0.clone(), Term::Int(1)));
        let w = one("w", Term::eq(Term::call("sf0", vec![a0], Sort::Int), s(1)));
        (v, w)
    }

    fn wrapper_role(name: &str) -> CallRole {
        match name {
            "sf0" => CallRole::Collect,
            "v" | "w" => CallRole::Defined,
            _ => CallRole::Other,
        }
    }

    /// The seeds of `hypotheses ==> s(2) == 3` with the wrappers defined.
    fn wrapper_seeds(hypotheses: &[(Term, Position)]) -> Vec<(String, String)> {
        let (v, w) = wrappers();
        let defs = HashMap::from([("v", &v), ("w", &w)]);
        let mut analysis = Analysis::new(&wrapper_role, &defs, 100_000);
        let goal = (Term::eq(s(2), Term::Int(3)), Position::default());
        let found = analysis.seeds(hypotheses, &goal).unwrap();
        found
            .into_items()
            .into_iter()
            .map(|(call, cond)| (call.to_string(), cond.to_string()))
            .collect()
    }

    fn at(term: Term, late: bool) -> (Term, Position) {
        (term, Position { late, gate: None })
    }

    #[test]
    fn early_instances_see_other_definitions_merge() {
        let app = |f: &str| Term::call(f, vec![x()], Sort::Bool);
        // `v(x)` makes `x` 1 before `w(x)` is instantiated: `s(x) == s(1)`
        // is built as `s(1) == s(1)`.
        let found = wrapper_seeds(&[at(app("v"), false), at(app("w"), false)]);
        assert!(found.iter().all(|(call, _)| call != "(sf0 1)"), "{found:?}");
        // Without it `s(1)` stays.
        let found = wrapper_seeds(&[at(app("w"), false)]);
        assert!(found.contains(&("(sf0 1)".to_string(), "true".to_string())));
    }

    #[test]
    fn early_instances_see_arithmetic_and_argument_merges() {
        let w = |arg: Term| at(Term::call("w", vec![arg], Sort::Bool), false);
        let plus = |a: Term, n: i128| Term::arith(ArithOp::Add, a, Term::Int(n));
        // `x + 1 == 2` makes `x` 1 before `w(x)` is instantiated.
        let found = wrapper_seeds(&[at(Term::eq(plus(x(), 1), Term::Int(2)), false), w(x())]);
        assert!(found.iter().all(|(call, _)| call != "(sf0 1)"), "{found:?}");
        let found = wrapper_seeds(&[at(Term::eq(plus(x(), 1), Term::Int(3)), false), w(x())]);
        assert!(found.contains(&("(sf0 1)".to_string(), "true".to_string())));
        // `u(1)` is 1 before `w(u(1))` is instantiated; `u(x)` is not.
        let (v, w_def) = wrappers();
        let a0 = Term::var("a0", Sort::Int);
        let u = SpecDef {
            function: "u".to_string(),
            params: vec![("a0".to_string(), Sort::Int)],
            guard: Term::Bool(true),
            body: a0,
        };
        let defs = HashMap::from([("v", &v), ("w", &w_def), ("u", &u)]);
        let role = |name: &str| match name {
            "u" => CallRole::Defined,
            other => wrapper_role(other),
        };
        let goal = (Term::eq(s(2), Term::Int(3)), Position::default());
        let u_of = |arg: Term| Term::call("u", vec![arg], Sort::Int);
        let mut found = Vec::new();
        for arg in [Term::Int(1), x()] {
            let mut analysis = Analysis::new(&role, &defs, 100_000);
            let seeds = analysis.seeds(&[w(u_of(arg))], &goal).unwrap();
            found.push(seeds.into_items().iter().any(|(call, _)| *call == s(1)));
        }
        assert_eq!(found, vec![false, true]);
    }

    #[test]
    fn early_instances_keep_bounded_applications_in_bounds() {
        // `k(x) <= 1` with `k` bounded below by 1 makes `k(x)` 1.
        let kx = Term::call("k", vec![x()], Sort::Int);
        let hypotheses = [
            at(Term::le(kx.clone(), Term::Int(1)), false),
            at(Term::call("w", vec![kx], Sort::Bool), false),
        ];
        let (v, w) = wrappers();
        let defs = HashMap::from([("v", &v), ("w", &w)]);
        let goal = (Term::eq(s(2), Term::Int(3)), Position::default());
        let ranged = HashMap::from([("k".to_string(), (Some(1), None))]);
        let mut analysis = Analysis::new(&wrapper_role, &defs, 100_000).with_ranges(&ranged);
        let seeds = analysis.seeds(&hypotheses, &goal).unwrap().into_items();
        assert!(seeds.iter().all(|(call, _)| *call != s(1)), "{seeds:?}");
        let mut analysis = Analysis::new(&wrapper_role, &defs, 100_000);
        let seeds = analysis.seeds(&hypotheses, &goal).unwrap().into_items();
        assert!(seeds.iter().any(|(call, _)| *call == s(1)), "{seeds:?}");
    }

    #[test]
    fn late_formulas_gate_their_instances() {
        let app = Term::call("w", vec![x()], Sort::Bool);
        let split = Term::or([Term::eq(x(), Term::Int(1)), Term::eq(x(), Term::Int(2))]);
        // Early, `w(x)` is made before the split on `x`.
        let found = wrapper_seeds(&[at(split.clone(), false), at(app.clone(), false)]);
        assert!(found.contains(&("(sf0 1)".to_string(), "true".to_string())));
        // Behind a split, it holds `s(1)` only where `x` is not 1.
        let found = wrapper_seeds(&[at(split, false), at(app, true)]);
        let one = found.iter().find(|(call, _)| call == "(sf0 1)");
        assert!(one.is_some_and(|(_, cond)| cond != "true"), "{found:?}");
    }

    #[test]
    fn late_callee_ensures_are_gated() {
        let sx = Term::call("sf0", vec![x()], Sort::Int);
        let clause = Term::eq(sx, s(1));
        let gate = instance_gate(std::slice::from_ref(&clause));
        assert_eq!(gate.to_string(), "(not (= x 1))");
        // Numerals never meet.
        assert_eq!(instance_gate(&[Term::eq(s(2), s(1))]), Term::Bool(true));
        let split = Term::or([Term::eq(x(), Term::Int(1)), Term::eq(x(), Term::Int(2))]);
        let ensures = Position {
            late: true,
            gate: Some(gate),
        };
        let found = wrapper_seeds(&[at(split, false), (clause, ensures)]);
        let one = found.iter().find(|(call, _)| call == "(sf0 1)");
        assert!(one.is_some_and(|(_, cond)| cond != "true"), "{found:?}");
    }

    #[test]
    fn congruence_identifies_more_than_substitution() {
        let mut graph = EGraph::default();
        graph.assert(&Term::eq(x(), Term::var("y", Sort::Int)));
        let mut simp = Simp::with(&mut graph);
        let fx = Term::call("sf0", vec![x()], Sort::Int);
        let fy = Term::call("sf0", vec![Term::var("y", Sort::Int)], Sort::Int);
        assert_eq!(simp.go(&Term::le(fx, fy)), Term::Bool(true));
    }
}

#[cfg(test)]
#[path = "trigger_relevance_tests.rs"]
mod trigger_tests;

#[cfg(test)]
#[path = "fact_closure_tests.rs"]
mod fact_closure_tests;

#[cfg(test)]
#[path = "clip_origin_tests.rs"]
mod clip_origin_tests;

#[cfg(test)]
pub(super) mod e18_completion_tests;
