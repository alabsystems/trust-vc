//! Witnesses that a subformula depends on a term.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Z3 rewrites a query before it matches, and an application the rewriting
//! removes is never instantiated on. Its rewrites are equivalences of the
//! theory it reads the query in, after it has substituted the equations and
//! literals of the other top-level formulas. So where Z3 rewrites a
//! subformula into one without some application, the subformula takes one
//! value whatever the application's value is, in every interpretation that
//! satisfies those substituted facts.
//!
//! [`depends`] searches for the converse: an interpretation satisfying the
//! facts, and two values of the application, under which the subformula
//! takes different values. Such a witness shows that no rewrite removes the
//! application from the subformula. Without one, the caller treats it as
//! removed; the search being incomplete only costs instances.
//!
//! The interpretation reads the query the way Z3 reads Verus's encoding:
//! Verus writes integer arithmetic as the uninterpreted `Add`, `Sub`, `Mul`,
//! `EucDiv` and `EucMod`, so an arithmetic operation is a function here,
//! like a call, whose value at a point may be chosen. Where none is chosen
//! it is the integer operation, which is one such function. Negation,
//! comparisons, `if` and the connectives are interpreted.
//!
//! A problem may ask for exact arithmetic instead (`Problem::exact`): every
//! arithmetic operation, the nonlinear ones Verus writes as calls among
//! them, is the integer operation (an integer division or remainder by zero
//! stays a function). Z3 instantiates Verus's arithmetic axioms as soon as
//! it reads an operation, so every class its arithmetic merges before it
//! builds an instance is one that exact arithmetic forces.
//!
//! The application stands for a class of terms (`Problem::members`): its
//! copies, and the terms Z3 identifies with it. Each search evaluates the
//! subformula in two worlds that share the interpretation and give the
//! class two different values. The class's value sits at the points its
//! members read, so any other term that reads one of those points takes
//! it too: both worlds are interpretations, where `s(x)` and `s(1)` are
//! equal wherever `x` is 1, and a rewrite that substitutes `x == 1` and
//! folds `s(x) == s(1)` is matched by the search finding no difference.

use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

use super::spec::{NL_DIV, NL_MOD, NL_MUL};
use super::term::{ArithOp, CmpOp, Sort, Term};

/// The function a point belongs to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Fun<'t> {
    Var(&'t str),
    Call(&'t str),
    Arith(ArithOp),
}

/// A function at argument values.
type Point<'t> = (Fun<'t>, Vec<i128>);

/// Values chosen at points, each with whether it is held (see
/// `Search::fixed`).
type Choices<'t> = HashMap<Point<'t>, (i128, bool)>;

enum Repair<'t> {
    Force(&'t Term, bool),
    Equal { side: &'t Term, other: &'t Term },
}

/// The most evaluation steps one search takes.
const SEARCH_STEPS: usize = 400_000;

/// The pairs of values tried for the class.
const MAX_PAIRS: usize = 10;

/// The interpretations [`same_values`] compares in. A boolean point takes
/// one random bit in each, so unrelated boolean terms meet in all of them
/// once in `2^SAME_VALUE_SEEDS` pairs.
const SAME_VALUE_SEEDS: u64 = 24;

/// One question: does `node` depend on the terms in `members`?
pub(crate) struct Problem<'t> {
    /// The subformula or term.
    pub(crate) node: &'t Term,
    /// The application and the terms identified with it: the class's value
    /// is the value at the points they read.
    pub(crate) members: Vec<&'t Term>,
    /// Their sort.
    pub(crate) sort: Sort,
    /// Facts every witness satisfies in both worlds.
    pub(crate) facts: Vec<&'t Term>,
    /// Whether arithmetic is exact rather than a function whose values may
    /// be chosen.
    pub(crate) exact: bool,
}

/// Whether a witness exists that `problem.node` depends on its members.
/// `budget` is the evaluation steps left for the whole analysis; once it is
/// spent the answer is `false`.
pub(crate) fn depends(problem: &Problem<'_>, budget: &mut usize) -> bool {
    let limit = SEARCH_STEPS.min(*budget);
    let mut search = Search::new(problem, limit);
    let found = search.run();
    *budget = budget.saturating_sub(search.steps);
    found
}

/// Whether the two argument lists take the same values in a few
/// interpretations with values spread over a wide range, where unrelated
/// terms almost never meet: whether Z3 may read the two lists as equal.
pub(crate) fn same_values(a: &[Term], b: &[Term]) -> bool {
    if a.len() != b.len() || a.iter().zip(b).any(|(a, b)| a.sort() != b.sort()) {
        return false;
    }
    let problem = Problem {
        node: &Term::Bool(true),
        members: Vec::new(),
        sort: Sort::Int,
        facts: Vec::new(),
        exact: false,
    };
    for seed in 0..SAME_VALUE_SEEDS {
        let mut search = Search::new(&problem, SEARCH_STEPS);
        search.wide = true;
        search.seed = seed;
        for (x, y) in a.iter().zip(b) {
            match (search.eval(x, 0), search.eval(y, 0)) {
                (Some(u), Some(v)) if u == v => {}
                _ => return false,
            }
        }
    }
    true
}

struct Search<'p, 't> {
    p: &'p Problem<'t>,
    /// Addresses of the subterms of the node and the facts that contain a
    /// member or another application of a member's function.
    has: HashSet<usize>,
    /// The functions the members apply.
    class_funs: Vec<Fun<'t>>,
    /// Whether a member's arguments apply one of `class_funs`, so that the
    /// class's points depend on the class's own value.
    nested: bool,
    /// The class's points in a world while they are being computed: what
    /// an application inside a member's arguments reads meanwhile.
    pending: [Option<Vec<Point<'t>>>; 2],
    /// Whether the node or a fact applies a member's function outside the
    /// members, at arguments that may take a member's values.
    aliased: bool,
    /// How far inside a bound a forced comparison puts a value: a bound
    /// such as `x <= 1` met at `x == 1` may put an application on the
    /// class's point, where it no longer differs.
    margin: i128,
    /// Whether a forced disjunction or `if` tries its alternatives last
    /// first, for the same reason.
    flip: bool,
    /// The class's value in each world.
    k: [i128; 2],
    /// Values a point takes where nothing is chosen.
    pool: Vec<i128>,
    /// Defaults spread over a wide range instead of the pool.
    wide: bool,
    /// A small initial interpretation, before the existing hashed defaults.
    zero_defaults: bool,
    seed: u64,
    /// Values chosen at points, and whether a later choice may replace
    /// them: values chosen to satisfy the facts may be, values the search
    /// for a difference relies on may not.
    fixed: Choices<'t>,
    /// Choosing values to satisfy the facts.
    soft: bool,
    /// Replacing no earlier choice at all.
    strict: bool,
    steps: usize,
    limit: usize,
}

fn address(t: &Term) -> usize {
    std::ptr::from_ref(t) as usize
}

/// The function a variable, call or arithmetic operation reads.
fn fun_of(t: &Term) -> Option<Fun<'_>> {
    match t {
        Term::Var { name, .. } => Some(Fun::Var(name)),
        Term::Call { name, .. } => Some(Fun::Call(name)),
        Term::Arith(op, ..) => Some(Fun::Arith(*op)),
        _ => None,
    }
}

/// Whether `t` reads a point of one of `funs`.
fn applies(t: &Term, funs: &[Fun<'_>]) -> bool {
    if fun_of(t).is_some_and(|f| funs.contains(&f)) {
        return true;
    }
    match t {
        Term::Bool(_) | Term::Int(_) | Term::Var { .. } => false,
        Term::Not(a) | Term::Neg(a) => applies(a, funs),
        Term::And(cs) | Term::Or(cs) | Term::Call { args: cs, .. } => {
            cs.iter().any(|c| applies(c, funs))
        }
        Term::Implies(a, b) | Term::Cmp(_, a, b) | Term::Arith(_, a, b) => {
            applies(a, funs) || applies(b, funs)
        }
        Term::Ite(c, a, b, _) => applies(c, funs) || applies(a, funs) || applies(b, funs),
    }
}

/// Whether two lists hold the same points.
fn same_points(a: &[Point<'_>], b: &[Point<'_>]) -> bool {
    a.len() == b.len() && a.iter().all(|p| b.contains(p))
}

fn mix(seed: u64, value: &impl Hash) -> u64 {
    let mut hasher = DefaultHasher::new();
    seed.hash(&mut hasher);
    value.hash(&mut hasher);
    hasher.finish()
}

/// The integer operation, where it is defined and exact.
fn integer_op(op: ArithOp, x: i128, y: i128) -> Option<i128> {
    match op {
        ArithOp::Add => x.checked_add(y),
        ArithOp::Sub => x.checked_sub(y),
        ArithOp::Mul => x.checked_mul(y),
        ArithOp::Div => (y != 0).then(|| x.checked_div_euclid(y)).flatten(),
        ArithOp::Mod => (y != 0).then(|| x.checked_rem_euclid(y)).flatten(),
    }
}

/// The integer operation and operands of `t` where arithmetic is exact: an
/// arithmetic term, or a call of one of the nonlinear operations.
fn exact_op(t: &Term) -> Option<(ArithOp, &Term, &Term)> {
    match t {
        Term::Arith(op, a, b) => Some((*op, a, b)),
        Term::Call { name, args, .. } => {
            let op = match name.as_str() {
                NL_MUL => ArithOp::Mul,
                NL_DIV => ArithOp::Div,
                NL_MOD => ArithOp::Mod,
                _ => return None,
            };
            match &args[..] {
                [a, b] => Some((op, a, b)),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Values of one operand of `op` under which the operation takes `value`,
/// where the other operand is `other`: the left one if `left`. Integer
/// division and remainder are Euclidean; a divisor is not solved for.
fn operand_values(op: ArithOp, left: bool, other: i128, value: i128) -> Vec<i128> {
    let found = match (op, left) {
        (ArithOp::Add, _) => vec![value.checked_sub(other)],
        // side - other == value
        (ArithOp::Sub, true) => vec![value.checked_add(other)],
        // other - side == value
        (ArithOp::Sub, false) => vec![other.checked_sub(value)],
        (ArithOp::Mul, _) => {
            let exact = other != 0 && value.checked_rem(other) == Some(0);
            vec![exact.then(|| value / other)]
        }
        // side div other == value: side in [value * other, .. + |other|).
        (ArithOp::Div, true) => match other.checked_abs() {
            Some(size) if size != 0 => {
                let low = value.checked_mul(other);
                vec![low, low.and_then(|low| low.checked_add(size - 1))]
            }
            _ => Vec::new(),
        },
        // side mod other == value
        (ArithOp::Mod, true) => match other.checked_abs() {
            Some(size) if (0..size).contains(&value) => vec![
                Some(value),
                value.checked_add(size),
                value.checked_sub(size),
            ],
            _ => Vec::new(),
        },
        _ => Vec::new(),
    };
    found.into_iter().flatten().collect()
}

fn literals(t: &Term, out: &mut Vec<i128>) {
    match t {
        Term::Int(n) => {
            if !out.contains(n) {
                out.push(*n);
            }
        }
        Term::Bool(_) | Term::Var { .. } => {}
        Term::Not(a) | Term::Neg(a) => literals(a, out),
        Term::And(cs) | Term::Or(cs) | Term::Call { args: cs, .. } => {
            for c in cs {
                literals(c, out);
            }
        }
        Term::Implies(a, b) | Term::Cmp(_, a, b) | Term::Arith(_, a, b) => {
            literals(a, out);
            literals(b, out);
        }
        Term::Ite(c, a, b, _) => {
            literals(c, out);
            literals(a, out);
            literals(b, out);
        }
    }
}

impl<'p, 't> Search<'p, 't> {
    fn new(p: &'p Problem<'t>, limit: usize) -> Self {
        let mut class_funs = Vec::new();
        for member in &p.members {
            if let Some(fun) = fun_of(member) {
                if !class_funs.contains(&fun) {
                    class_funs.push(fun);
                }
            }
        }
        let nested = p.members.iter().any(|member| match member {
            Term::Call { args, .. } => args.iter().any(|arg| applies(arg, &class_funs)),
            Term::Arith(_, left, right) => {
                applies(left, &class_funs) || applies(right, &class_funs)
            }
            _ => false,
        });
        let mut search = Self {
            p,
            has: HashSet::new(),
            class_funs,
            nested,
            pending: [None, None],
            aliased: false,
            margin: 0,
            flip: false,
            k: [0, 1],
            pool: Vec::new(),
            wide: false,
            zero_defaults: false,
            seed: 0,
            fixed: HashMap::new(),
            soft: false,
            strict: false,
            steps: 0,
            limit,
        };
        search.mark(p.node);
        for fact in &p.facts {
            search.mark(fact);
        }
        let mut lits = Vec::new();
        literals(p.node, &mut lits);
        for fact in &p.facts {
            literals(fact, &mut lits);
        }
        let mut pool = vec![0, 1, -1, 2];
        for &n in &lits {
            for v in [Some(n), n.checked_sub(1), n.checked_add(1)]
                .into_iter()
                .flatten()
            {
                if !pool.contains(&v) {
                    pool.push(v);
                }
            }
            if pool.len() > 48 {
                break;
            }
        }
        pool.extend([1_000_003, -1_000_033]);
        search.pool = pool;
        search
    }

    /// Record which subterms of `t` contain a member, or an application of
    /// a member's function, which reads the class's value where its
    /// arguments take a member's.
    fn mark(&mut self, t: &'t Term) -> bool {
        let alias = !self.is_member(t) && fun_of(t).is_some_and(|f| self.class_funs.contains(&f));
        self.aliased |= alias;
        let mut found = alias || self.is_member(t);
        match t {
            Term::Bool(_) | Term::Int(_) | Term::Var { .. } => {}
            Term::Not(a) | Term::Neg(a) => found |= self.mark(a),
            Term::And(cs) | Term::Or(cs) | Term::Call { args: cs, .. } => {
                for c in cs {
                    found |= self.mark(c);
                }
            }
            Term::Implies(a, b) | Term::Cmp(_, a, b) | Term::Arith(_, a, b) => {
                found |= self.mark(a);
                found |= self.mark(b);
            }
            Term::Ite(c, a, b, _) => {
                found |= self.mark(c);
                found |= self.mark(a);
                found |= self.mark(b);
            }
        }
        if found {
            self.has.insert(address(t));
        }
        found
    }

    fn has(&self, t: &Term) -> bool {
        self.has.contains(&address(t))
    }

    fn is_member(&self, t: &Term) -> bool {
        matches!(t, Term::Call { .. } | Term::Var { .. }) && self.p.members.contains(&t)
    }

    fn exhausted(&self) -> bool {
        self.steps >= self.limit
    }

    /// The pairs of class values to try: around the numerals that occur,
    /// then small and far values.
    fn pairs(&self) -> Vec<[i128; 2]> {
        if self.p.sort == Sort::Bool {
            return vec![[0, 1]];
        }
        let mut lits = Vec::new();
        literals(self.p.node, &mut lits);
        for fact in &self.p.facts {
            literals(fact, &mut lits);
        }
        let mut out: Vec<[i128; 2]> = Vec::new();
        for n in lits.into_iter().take(4) {
            let around = [
                n.checked_add(1).map(|m| [n, m]),
                n.checked_sub(1).map(|m| [m, n]),
            ];
            for pair in around.into_iter().flatten() {
                if !out.contains(&pair) {
                    out.push(pair);
                }
            }
        }
        for pair in [[0, 1], [2, 1_000_003]] {
            if !out.contains(&pair) {
                out.push(pair);
            }
        }
        out.truncate(MAX_PAIRS);
        out
    }

    fn run(&mut self) -> bool {
        self.try_zero_defaults() || self.run_hashed()
    }

    fn try_zero_defaults(&mut self) -> bool {
        // Large hashed defaults can trap guarded return bindings in repairs
        // unrelated to the carrier. Try the simplest interpretation first.
        // This candidate still needs all facts in both worlds and a genuine
        // difference. Its work comes from the original cap: steps never reset.
        let limit = self.limit;
        self.limit = limit.min(SEARCH_STEPS / 40);
        self.zero_defaults = true;
        self.k = [0, 1];
        let found = self.prepare_scalar_atoms()
            && self.sens(self.p.node)
            && self.satisfy_facts()
            && self.differs(self.p.node);
        self.limit = limit;
        if found {
            return true;
        }
        self.zero_defaults = false;
        self.fixed.clear();
        false
    }

    /// Build local choices from the query's elementary scalar premises.
    /// Keep them soft until the whole selected set agrees, then protect
    /// those choices while conditional bindings are repaired. This exports
    /// no fact; the candidate still needs every original premise in both worlds.
    fn prepare_scalar_atoms(&mut self) -> bool {
        fn leaf(term: &Term) -> bool {
            matches!(term, Term::Var { .. } | Term::Int(_) | Term::Bool(_))
        }
        fn atom(term: &Term) -> bool {
            let inner = match term {
                Term::Not(inner) => &**inner,
                other => other,
            };
            match inner {
                Term::Cmp(_, left, right) => leaf(left) && leaf(right),
                Term::Var {
                    sort: Sort::Bool, ..
                }
                | Term::Bool(_) => true,
                _ => false,
            }
        }
        let mut atoms = Vec::new();
        for fact in &self.p.facts {
            if self.exhausted() {
                return false;
            }
            self.steps += 1;
            if atom(fact) {
                atoms.push(*fact);
            }
        }
        let soft = self.soft;
        self.soft = true;
        let mut all = false;
        for _ in 0..8 {
            all = true;
            for fact in &atoms {
                if !self.holds(fact, true) {
                    all = false;
                    self.force(fact, true);
                }
            }
            if all || self.exhausted() {
                break;
            }
        }
        let valid = all || atoms.iter().all(|fact| self.holds(fact, true));
        self.soft = soft;
        if !valid {
            return false;
        }
        for ((function, _), (_, held)) in &mut self.fixed {
            if self.steps >= self.limit {
                return false;
            }
            self.steps += 1;
            if matches!(function, Fun::Var(_)) {
                *held = true;
            }
        }
        true
    }

    fn run_hashed(&mut self) -> bool {
        let passes: &[(i128, bool)] = if self.aliased {
            &[(0, false), (1, false), (0, true), (1, true)]
        } else {
            &[(0, false)]
        };
        for &(margin, flip) in passes {
            self.margin = margin;
            self.flip = flip;
            for pair in self.pairs() {
                for seed in 0..2 {
                    for facts_first in [false, true] {
                        if self.exhausted() {
                            return false;
                        }
                        self.k = pair;
                        self.seed = seed;
                        self.fixed.clear();
                        let ok = if facts_first {
                            self.satisfy_facts() && self.sens(self.p.node)
                        } else {
                            self.sens(self.p.node)
                        };
                        if ok && self.satisfy_facts() && self.differs(self.p.node) {
                            return true;
                        }
                    }
                }
            }
        }
        false
    }

    /// Force every fact; true if all hold in both worlds afterwards. A
    /// value chosen for one fact may be replaced for a later one, and the
    /// facts are gone through again, in both orders, until all hold.
    fn satisfy_facts(&mut self) -> bool {
        let mut facts = self.p.facts.clone();
        self.soft = true;
        let mut all = false;
        for _ in 0..8 {
            all = true;
            for fact in &facts {
                if !self.holds(fact, true) {
                    all = false;
                    self.repair(fact, &facts);
                }
            }
            if all || self.exhausted() {
                break;
            }
            facts.reverse();
        }
        self.soft = false;
        all || facts.iter().all(|fact| self.holds(fact, true))
    }

    /// Make the fact `fact` hold, by whichever of its disjuncts leaves the
    /// fewest of `facts` broken.
    fn repair(&mut self, fact: &'t Term, facts: &[&'t Term]) {
        let options: Vec<(&'t Term, bool)> = match fact {
            Term::Or(cs) => cs.iter().map(|c| (c, true)).collect(),
            Term::Implies(a, b) => vec![(&**a, false), (&**b, true)],
            Term::Not(inner) => match &**inner {
                Term::And(cs) => cs.iter().map(|c| (c, false)).collect(),
                _ => vec![(fact, true)],
            },
            _ => vec![(fact, true)],
        };
        let options = self.ordered(options);
        let mut repairs = Vec::new();
        for (part, want) in options {
            if self.exhausted() {
                return;
            }
            self.steps += 1;
            if let (Term::Cmp(CmpOp::Eq, left, right), true) = (part, want) {
                // Preserve the original right-side-first tie order, but
                // score both assignments against the OTHER query facts.
                // Repairing only the first side can merge two call arguments
                // by changing an arithmetic point instead of its bound local.
                repairs.push(Repair::Equal {
                    side: right,
                    other: left,
                });
                if self.exhausted() {
                    return;
                }
                self.steps += 1;
                repairs.push(Repair::Equal {
                    side: left,
                    other: right,
                });
            } else {
                repairs.push(Repair::Force(part, want));
            }
        }
        // Scoring chooses between alternatives. A sole candidate has the
        // same choice whatever its broken-fact count, and the caller still
        // validates every fact in both worlds before accepting a witness.
        if let [repair] = repairs.as_slice() {
            let saved = self.fixed.clone();
            if !(self.apply_repair(repair) && self.holds(fact, true)) {
                self.fixed = saved;
            }
            return;
        }
        let mut best: Option<(usize, Choices<'t>)> = None;
        for repair in repairs {
            let saved = self.fixed.clone();
            if self.apply_repair(&repair) && self.holds(fact, true) {
                let broken = facts.iter().filter(|f| !self.holds(f, true)).count();
                if best.as_ref().is_none_or(|(least, _)| broken < *least) {
                    best = Some((broken, self.fixed.clone()));
                }
            }
            self.fixed = saved;
        }
        if let Some((_, fixed)) = best {
            self.fixed = fixed;
        }
    }

    fn apply_repair(&mut self, repair: &Repair<'t>) -> bool {
        match repair {
            Repair::Force(term, want) => self.force(term, *want),
            Repair::Equal { side, other } => {
                if self.exhausted() {
                    return false;
                }
                self.prefer_preserved(|search| {
                    let Some((first, second)) = search.both(other) else {
                        return false;
                    };
                    first == second && search.set(side, first)
                })
            }
        }
    }

    /// Alternatives in the order this pass tries them.
    fn ordered<T>(&self, mut options: Vec<T>) -> Vec<T> {
        if self.flip {
            options.reverse();
        }
        options
    }

    // ------------------------------------------------------------------
    // Evaluation
    // ------------------------------------------------------------------

    /// The value of a point where nothing is chosen.
    fn default(&self, point: &Point<'t>, sort: Sort) -> i128 {
        if let Fun::Arith(op) = point.0 {
            if let [x, y] = point.1[..] {
                if let Some(value) = integer_op(op, x, y) {
                    return value;
                }
            }
        }
        if self.zero_defaults {
            return 0;
        }
        let h = mix(self.seed, point);
        if sort == Sort::Bool {
            return i128::from(h & 1);
        }
        if self.wide {
            return i128::from(i64::from_ne_bytes(h.to_ne_bytes()));
        }
        let len = u64::try_from(self.pool.len()).unwrap_or(1).max(1);
        let index = usize::try_from(h % len).unwrap_or(0);
        self.pool.get(index).copied().unwrap_or(0)
    }

    fn value_at(&self, point: &Point<'t>, sort: Sort) -> i128 {
        match self.fixed.get(point) {
            Some(&(value, _)) => value,
            None => self.default(point, sort),
        }
    }

    /// The value at `point` in world `w`: the class's value where the point
    /// is one of the class's.
    fn read(&mut self, point: &Point<'t>, w: usize, sort: Sort) -> Option<i128> {
        if self.in_class(point, w)? {
            return Some(self.k[w]);
        }
        Some(self.value_at(point, sort))
    }

    /// Whether `point` is one of the points the members read in world `w`;
    /// `None` when those cannot be computed.
    fn in_class(&mut self, point: &Point<'t>, w: usize) -> Option<bool> {
        if !self.class_funs.contains(&point.0) {
            return Some(false);
        }
        Some(self.class_points(w)?.contains(point))
    }

    /// The points the members read in world `w`. Where a member's
    /// arguments apply a member's function, they are read with the
    /// class's points as computed so far until those settle, and the
    /// class has to read the same points in both worlds: otherwise the two
    /// worlds would differ in more than the class's value.
    fn class_points(&mut self, w: usize) -> Option<Vec<Point<'t>>> {
        if let Some(points) = &self.pending[w] {
            return Some(points.clone());
        }
        if !self.nested {
            return self.member_points(w);
        }
        let first = self.settle(0)?;
        let second = self.settle(1)?;
        if !same_points(&first, &second) {
            return None;
        }
        Some(if w == 0 { first } else { second })
    }

    fn settle(&mut self, w: usize) -> Option<Vec<Point<'t>>> {
        let mut points = Vec::new();
        for _ in 0..4 {
            self.pending[w] = Some(points.clone());
            let next = self.member_points(w);
            self.pending[w] = None;
            let next = next?;
            if same_points(&next, &points) {
                return Some(points);
            }
            points = next;
        }
        None
    }

    fn member_points(&mut self, w: usize) -> Option<Vec<Point<'t>>> {
        let members = self.p.members.clone();
        let mut out = Vec::with_capacity(members.len());
        for member in members {
            let point = self.point_of(member, w)?;
            if !out.contains(&point) {
                out.push(point);
            }
        }
        Some(out)
    }

    /// The point a variable, call or arithmetic operation reads in world
    /// `w`.
    fn point_of(&mut self, t: &'t Term, w: usize) -> Option<Point<'t>> {
        match t {
            Term::Var { name, .. } => Some((Fun::Var(name), Vec::new())),
            Term::Call { name, args, .. } => {
                let mut values = Vec::with_capacity(args.len());
                for arg in args {
                    values.push(self.eval(arg, w)?);
                }
                Some((Fun::Call(name), values))
            }
            Term::Arith(op, a, b) => {
                let x = self.eval(a, w)?;
                let y = self.eval(b, w)?;
                Some((Fun::Arith(*op), vec![x, y]))
            }
            _ => None,
        }
    }

    /// The value of `t` in world `w`; `None` when it cannot be computed
    /// exactly or the steps are spent.
    fn eval(&mut self, t: &'t Term, w: usize) -> Option<i128> {
        self.steps += 1;
        if self.steps > self.limit {
            return None;
        }
        if self.is_member(t) {
            return Some(self.k[w]);
        }
        if let Some((op, a, b)) = self.exact(t) {
            let x = self.eval(a, w)?;
            let y = self.eval(b, w)?;
            if let Some(value) = integer_op(op, x, y) {
                return Some(value);
            }
            // Division by zero is a function; overflow is not computed.
            if y != 0 {
                return None;
            }
            let point = self.point_of(t, w)?;
            return self.read(&point, w, Sort::Int);
        }
        match t {
            Term::Bool(b) => Some(i128::from(*b)),
            Term::Int(n) => Some(*n),
            Term::Var { sort, .. } | Term::Call { sort, .. } => {
                let point = self.point_of(t, w)?;
                self.read(&point, w, *sort)
            }
            Term::Arith(..) => {
                let point = self.point_of(t, w)?;
                self.read(&point, w, Sort::Int)
            }
            Term::Neg(a) => self.eval(a, w)?.checked_neg(),
            Term::Not(a) => Some(1 - self.eval(a, w)?),
            Term::And(cs) => {
                for c in cs {
                    if self.eval(c, w)? == 0 {
                        return Some(0);
                    }
                }
                Some(1)
            }
            Term::Or(cs) => {
                for c in cs {
                    if self.eval(c, w)? != 0 {
                        return Some(1);
                    }
                }
                Some(0)
            }
            Term::Implies(a, b) => {
                if self.eval(a, w)? == 0 {
                    return Some(1);
                }
                Some(i128::from(self.eval(b, w)? != 0))
            }
            Term::Cmp(op, a, b) => {
                let x = self.eval(a, w)?;
                let y = self.eval(b, w)?;
                Some(i128::from(match op {
                    CmpOp::Eq => x == y,
                    CmpOp::Lt => x < y,
                    CmpOp::Le => x <= y,
                }))
            }
            Term::Ite(c, a, b, _) => {
                if self.eval(c, w)? != 0 {
                    self.eval(a, w)
                } else {
                    self.eval(b, w)
                }
            }
        }
    }

    /// The integer operation `t` is, where arithmetic is exact.
    fn exact(&self, t: &'t Term) -> Option<(ArithOp, &'t Term, &'t Term)> {
        if self.p.exact {
            exact_op(t)
        } else {
            None
        }
    }

    /// Choose values so that the exact operation `t`, `a op b`, takes
    /// `value` in both worlds: an operand is given a value that fits the
    /// other operand's, where that is one value in both worlds. A divisor
    /// is not solved for.
    fn solve(&mut self, t: &'t Term, op: ArithOp, a: &'t Term, b: &'t Term, value: i128) -> bool {
        for (side, other, left) in [(a, b, true), (b, a, false)] {
            let Some((o0, o1)) = self.both(other) else {
                continue;
            };
            if o0 != o1 {
                continue;
            }
            for target in self.ordered(operand_values(op, left, o0, value)) {
                let saved = self.fixed.clone();
                if self.set(side, target) && self.both(t) == Some((value, value)) {
                    return true;
                }
                self.fixed = saved;
            }
        }
        false
    }

    fn both(&mut self, t: &'t Term) -> Option<(i128, i128)> {
        Some((self.eval(t, 0)?, self.eval(t, 1)?))
    }

    fn differs(&mut self, t: &'t Term) -> bool {
        matches!(self.both(t), Some((x, y)) if x != y)
    }

    fn holds(&mut self, t: &'t Term, want: bool) -> bool {
        let v = i128::from(want);
        self.both(t) == Some((v, v))
    }

    // ------------------------------------------------------------------
    // Forcing values
    // ------------------------------------------------------------------

    /// Choose values so that the boolean `t` is `want` in both worlds.
    /// While satisfying the facts, first without replacing any value chosen
    /// for another fact.
    fn force(&mut self, t: &'t Term, want: bool) -> bool {
        if self.holds(t, want) {
            return true;
        }
        if self.exhausted() {
            return false;
        }
        self.prefer_preserved(|search| search.force_once(t, want))
    }

    /// Keep the same strict-first/soft fallback for every repair proposal.
    fn prefer_preserved(&mut self, mut attempt: impl FnMut(&mut Self) -> bool) -> bool {
        if self.soft && !self.strict {
            let saved = self.fixed.clone();
            self.strict = true;
            let done = attempt(self);
            self.strict = false;
            if done {
                return true;
            }
            self.fixed = saved;
        }
        attempt(self)
    }

    fn force_once(&mut self, t: &'t Term, want: bool) -> bool {
        match t {
            Term::Not(a) => self.force(a, !want),
            Term::And(cs) | Term::Or(cs) => {
                let every = matches!(t, Term::And(_)) == want;
                if every {
                    for _ in 0..2 {
                        for c in cs {
                            self.force(c, want);
                        }
                        if self.holds(t, want) {
                            return true;
                        }
                    }
                    false
                } else {
                    for c in self.ordered(cs.iter().collect()) {
                        let saved = self.fixed.clone();
                        if self.force(c, want) && self.holds(t, want) {
                            return true;
                        }
                        self.fixed = saved;
                    }
                    false
                }
            }
            Term::Implies(a, b) => {
                if want {
                    for (part, value) in self.ordered(vec![(&**a, false), (&**b, true)]) {
                        let saved = self.fixed.clone();
                        if self.force(part, value) && self.holds(t, true) {
                            return true;
                        }
                        self.fixed = saved;
                    }
                    false
                } else {
                    self.force(a, true) && self.force(b, false) && self.holds(t, false)
                }
            }
            Term::Ite(c, a, b, _) => {
                for (branch, arm) in self.ordered(vec![(true, a), (false, b)]) {
                    let saved = self.fixed.clone();
                    if self.force(c, branch) && self.force(arm, want) && self.holds(t, want) {
                        return true;
                    }
                    self.fixed = saved;
                }
                false
            }
            Term::Cmp(op, a, b) => self.force_cmp(t, *op, a, b, want),
            Term::Var { .. } | Term::Call { .. } => self.set_point(t, i128::from(want)),
            _ => false,
        }
    }

    /// Choose values so that the comparison `t` is `want` in both worlds,
    /// by giving one side a value fitting the other side's values.
    fn force_cmp(&mut self, t: &'t Term, op: CmpOp, a: &'t Term, b: &'t Term, want: bool) -> bool {
        if a.sort() == Sort::Bool {
            for (side, other) in [(b, a), (a, b)] {
                let Some((o0, o1)) = self.both(other) else {
                    continue;
                };
                if o0 != o1 {
                    continue;
                }
                let target = if want { o0 } else { 1 - o0 };
                let saved = self.fixed.clone();
                if self.set(side, target) && self.holds(t, want) {
                    return true;
                }
                self.fixed = saved;
            }
            return false;
        }
        // `side` is the right operand first, then the left one.
        for (side, other, left) in [(b, a, false), (a, b, true)] {
            let Some((o0, o1)) = self.both(other) else {
                continue;
            };
            let (lo, hi) = (o0.min(o1), o0.max(o1));
            let up = |v: i128, by: i128| v.checked_add(by);
            let down = |v: i128, by: i128| v.checked_sub(by);
            let m = self.margin;
            let target = match (op, left, want) {
                (CmpOp::Eq, _, true) => (o0 == o1).then_some(o0),
                (CmpOp::Eq, _, false) => up(hi, 1 + m),
                // other <= side
                (CmpOp::Le, false, true) => up(hi, m),
                (CmpOp::Le, false, false) => down(lo, 1 + m),
                // other < side
                (CmpOp::Lt, false, true) => up(hi, 1 + m),
                (CmpOp::Lt, false, false) => down(lo, m),
                // side <= other
                (CmpOp::Le, true, true) => down(lo, m),
                (CmpOp::Le, true, false) => up(hi, 1 + m),
                // side < other
                (CmpOp::Lt, true, true) => down(lo, 1 + m),
                (CmpOp::Lt, true, false) => up(hi, m),
            };
            let Some(target) = target else {
                continue;
            };
            let saved = self.fixed.clone();
            if self.set(side, target) && self.holds(t, want) {
                return true;
            }
            self.fixed = saved;
        }
        false
    }

    /// Choose values so that `t` takes `value` in both worlds.
    fn set(&mut self, t: &'t Term, value: i128) -> bool {
        if self.both(t) == Some((value, value)) {
            return true;
        }
        if self.exhausted() || self.is_member(t) {
            return false;
        }
        if let Some((op, a, b)) = self.exact(t) {
            return self.solve(t, op, a, b, value);
        }
        match t {
            Term::Var { .. } | Term::Call { .. } | Term::Arith(..) => self.set_point(t, value),
            Term::Neg(a) => value.checked_neg().is_some_and(|v| self.set(a, v)),
            Term::Ite(c, a, b, _) => {
                for (branch, arm) in self.ordered(vec![(true, a), (false, b)]) {
                    let saved = self.fixed.clone();
                    if self.force(c, branch)
                        && self.set(arm, value)
                        && self.both(t) == Some((value, value))
                    {
                        return true;
                    }
                    self.fixed = saved;
                }
                false
            }
            Term::Bool(_) | Term::Int(_) => false,
            _ => (value == 0 || value == 1) && self.force(t, value == 1),
        }
    }

    /// Give the points `t` reads in the two worlds the value `value`.
    fn set_point(&mut self, t: &'t Term, value: i128) -> bool {
        if self.is_member(t) {
            return false;
        }
        let mut points = Vec::new();
        for w in 0..2 {
            let Some(point) = self.point_of(t, w) else {
                return false;
            };
            if self.in_class(&point, w) != Some(false) {
                return false;
            }
            if !points.contains(&point) {
                points.push(point);
            }
        }
        let strict = self.strict;
        let held = |slot: Option<&(i128, bool)>| {
            slot.is_some_and(|&(old, hard)| (hard || strict) && old != value)
        };
        if points.iter().any(|point| held(self.fixed.get(point))) {
            return false;
        }
        for point in points {
            self.fixed.insert(point, (value, !self.soft));
        }
        true
    }

    // ------------------------------------------------------------------
    // Sensitizing
    // ------------------------------------------------------------------

    /// Choose values so that `t` differs between the worlds.
    fn sens(&mut self, t: &'t Term) -> bool {
        if self.differs(t) {
            return true;
        }
        if !self.has(t) || self.exhausted() || self.is_member(t) {
            return false;
        }
        if let Some((_, a, b)) = self.exact(t) {
            for arg in [a, b] {
                if !self.has(arg) {
                    continue;
                }
                let saved = self.fixed.clone();
                if self.sens(arg) && self.differs(t) {
                    return true;
                }
                self.fixed = saved;
            }
            return false;
        }
        match t {
            Term::Not(a) | Term::Neg(a) => self.sens(a),
            Term::And(cs) | Term::Or(cs) => {
                let others = matches!(t, Term::And(_));
                for (i, c) in cs.iter().enumerate() {
                    if !self.has(c) {
                        continue;
                    }
                    for first in [false, true] {
                        let saved = self.fixed.clone();
                        let mut ok = !first || self.sens(c);
                        for (j, o) in cs.iter().enumerate() {
                            if ok && j != i {
                                ok = self.force(o, others);
                            }
                        }
                        if ok && !first {
                            ok = self.sens(c);
                        }
                        if ok && self.differs(t) {
                            return true;
                        }
                        self.fixed = saved;
                    }
                }
                false
            }
            Term::Implies(a, b) => {
                for (fixed, fixed_to, varied) in [(a, true, b), (b, false, a)] {
                    if !self.has(varied) {
                        continue;
                    }
                    for first in [false, true] {
                        let saved = self.fixed.clone();
                        let ok = if first {
                            let sensed = self.sens(varied);
                            sensed && self.force(fixed, fixed_to)
                        } else {
                            let forced = self.force(fixed, fixed_to);
                            forced && self.sens(varied)
                        };
                        if ok && self.differs(t) {
                            return true;
                        }
                        self.fixed = saved;
                    }
                }
                false
            }
            Term::Ite(c, a, b, _) => {
                for (branch, arm) in [(true, a), (false, b)] {
                    if !self.has(arm) {
                        continue;
                    }
                    for first in [false, true] {
                        let saved = self.fixed.clone();
                        let ok = if first {
                            let sensed = self.sens(arm);
                            sensed && self.force(c, branch)
                        } else {
                            let forced = self.force(c, branch);
                            forced && self.sens(arm)
                        };
                        if ok && self.differs(t) {
                            return true;
                        }
                        self.fixed = saved;
                    }
                }
                if self.has(c) {
                    let saved = self.fixed.clone();
                    if self.sens(c) && self.differs(t) {
                        return true;
                    }
                    self.fixed = saved;
                }
                false
            }
            Term::Cmp(op, a, b) => self.sens_cmp(t, *op, a, b),
            Term::Call { args, .. } => {
                for arg in args {
                    if self.sens_point(t, arg) {
                        return true;
                    }
                }
                false
            }
            Term::Arith(_, a, b) => self.sens_point(t, a) || self.sens_point(t, b),
            _ => false,
        }
    }

    /// Make the argument `arg` of the point `t` differ between the worlds,
    /// then the values at the two points it reads.
    fn sens_point(&mut self, t: &'t Term, arg: &'t Term) -> bool {
        if !self.has(arg) {
            return false;
        }
        let saved = self.fixed.clone();
        if self.sens(arg) && self.split_point(t) && self.differs(t) {
            return true;
        }
        self.fixed = saved;
        false
    }

    /// Give the two points `t` reads different values.
    fn split_point(&mut self, t: &'t Term) -> bool {
        let sort = t.sort();
        let (Some(p0), Some(p1)) = (self.point_of(t, 0), self.point_of(t, 1)) else {
            return false;
        };
        if p0 == p1 {
            return false;
        }
        let (Some(c0), Some(c1)) = (self.in_class(&p0, 0), self.in_class(&p1, 1)) else {
            return false;
        };
        let v0 = if c0 {
            self.k[0]
        } else {
            self.value_at(&p0, sort)
        };
        let v1 = if c1 {
            self.k[1]
        } else {
            self.value_at(&p1, sort)
        };
        if v0 != v1 {
            return true;
        }
        let other = |v: i128| if sort == Sort::Bool { 1 - v } else { v + 1 };
        let strict = self.strict;
        let free = |slot: Option<&(i128, bool)>| !slot.is_some_and(|&(_, hard)| hard || strict);
        if !c1 && free(self.fixed.get(&p1)) {
            self.fixed.insert(p1, (other(v0), !self.soft));
            return true;
        }
        if !c0 && free(self.fixed.get(&p0)) {
            self.fixed.insert(p0, (other(v1), !self.soft));
            return true;
        }
        false
    }

    fn sens_cmp(&mut self, t: &'t Term, op: CmpOp, a: &'t Term, b: &'t Term) -> bool {
        if a.sort() == Sort::Bool {
            for side in [a, b] {
                if !self.has(side) {
                    continue;
                }
                let saved = self.fixed.clone();
                if self.sens(side) && self.differs(t) {
                    return true;
                }
                self.fixed = saved;
            }
            return false;
        }
        for (side, other, left) in [(a, b, true), (b, a, false)] {
            if !self.has(side) {
                continue;
            }
            let saved = self.fixed.clone();
            if !self.sens(side) {
                self.fixed = saved;
                continue;
            }
            if self.differs(t) {
                return true;
            }
            if let Some((s0, s1)) = self.both(side) {
                let (lo, hi) = (s0.min(s1), s0.max(s1));
                // A value for `other` between the two values of `side`.
                let targets = match (op, left) {
                    (CmpOp::Eq, _) => vec![s0, s1],
                    // side <= x
                    (CmpOp::Le, true) => vec![lo],
                    // side < x
                    (CmpOp::Lt, true) => vec![hi],
                    // x <= side
                    (CmpOp::Le, false) => vec![hi],
                    // x < side
                    (CmpOp::Lt, false) => vec![lo],
                };
                for x in targets {
                    let inner = self.fixed.clone();
                    if self.set(other, x) && self.differs(t) {
                        return true;
                    }
                    self.fixed = inner;
                }
            }
            self.fixed = saved;
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scalar_premises_are_agreed_before_local_choices_are_protected() {
        let x = Term::var("bounded", Sort::Int);
        let member = Term::call("actual", Vec::new(), Sort::Int);
        let node = Term::eq(member.clone(), Term::Int(0));
        for reverse in [false, true] {
            let mut facts = vec![
                Term::le(Term::Int(1), x.clone()),
                Term::le(Term::Int(2), x.clone()),
                Term::le(x.clone(), Term::Int(4)),
            ];
            if reverse {
                facts.reverse();
            }
            let problem = Problem {
                node: &node,
                members: vec![&member],
                sort: Sort::Int,
                facts: facts.iter().collect(),
                exact: false,
            };
            let mut search = Search::new(&problem, SEARCH_STEPS);
            search.zero_defaults = true;
            assert!(search.prepare_scalar_atoms());
            assert_eq!(search.both(&x), Some((2, 2)));
            assert!(search.fixed[&(Fun::Var("bounded"), Vec::new())].1);
            assert!(search.sens(&node) && search.satisfy_facts() && search.differs(&node));
            let mut small = Search::new(&problem, 1);
            small.zero_defaults = true;
            assert!(!small.prepare_scalar_atoms());
            assert_eq!(small.limit, 1);
        }
        let facts = [Term::le(Term::Int(2), x.clone()), Term::le(x, Term::Int(1))];
        let problem = Problem {
            node: &node,
            members: vec![&member],
            sort: Sort::Int,
            facts: facts.iter().collect(),
            exact: false,
        };
        let mut search = Search::new(&problem, SEARCH_STEPS);
        search.zero_defaults = true;
        assert!(!search.prepare_scalar_atoms());
        let mut budget = SEARCH_STEPS;
        assert!(!depends(&problem, &mut budget));
    }

    #[test]
    fn a_named_binding_must_not_needlessly_merge_distinct_call_arguments() {
        for aliases in [true, false] {
            let x = Term::var("input", Sort::Int);
            let y = Term::var("argument", Sort::Int);
            let z = Term::var("other_argument", Sort::Int);
            let member = Term::call("actual", vec![y.clone()], Sort::Int);
            let other = Term::call("actual", vec![z.clone()], Sort::Int);
            let node = Term::eq(member.clone(), Term::Int(0));
            let rhs = if aliases {
                z.clone()
            } else {
                Term::arith(ArithOp::Sub, x.clone(), Term::Int(1))
            };
            let facts = [
                Term::eq(x, Term::Int(2)),
                Term::eq(z, Term::Int(0)),
                Term::eq(y, rhs),
                Term::eq(other, Term::Int(0)),
            ];
            let problem = Problem {
                node: &node,
                members: vec![&member],
                sort: Sort::Int,
                facts: facts.iter().collect(),
                exact: false,
            };
            let mut search = Search::new(&problem, SEARCH_STEPS);
            search.k = [0, 1];
            search
                .fixed
                .insert((Fun::Var("input"), Vec::new()), (2, true));
            search
                .fixed
                .insert((Fun::Var("argument"), Vec::new()), (0, false));
            search
                .fixed
                .insert((Fun::Var("other_argument"), Vec::new()), (0, true));
            search
                .fixed
                .insert((Fun::Call("actual"), vec![0]), (0, true));
            assert!(search.sens(&node));
            let found = search.satisfy_facts() && search.differs(&node);
            assert_eq!(
                found, !aliases,
                "aliases={aliases} choices={:?}",
                search.fixed
            );
        }
    }

    #[test]
    fn zero_aliases_fall_back_without_replenishing_the_search_budget() {
        let left = Term::call("actual", vec![Term::var("left", Sort::Int)], Sort::Int);
        let right = Term::call("actual", vec![Term::var("right", Sort::Int)], Sort::Int);
        let node = Term::eq(left.clone(), right);
        let problem = Problem {
            node: &node,
            members: vec![&left],
            sort: Sort::Int,
            facts: Vec::new(),
            exact: false,
        };
        // Uniform zero arguments alias the two applications and leave no
        // difference; the original hashed search can keep them distinct.
        let mut prefix = Search::new(&problem, SEARCH_STEPS);
        assert!(!prefix.try_zero_defaults());
        assert!(!prefix.zero_defaults);
        assert_eq!(prefix.limit, SEARCH_STEPS);
        let mut baseline = Search::new(&problem, SEARCH_STEPS);
        assert!(baseline.run_hashed());
        let mut full = Search::new(&problem, SEARCH_STEPS);
        assert!(full.run());
        assert!(
            !full.zero_defaults,
            "the witness came from the hashed fallback"
        );
        assert_eq!(full.steps, prefix.steps + baseline.steps);
        eprintln!(
            "witness fallback steps: zero={} hashed={} total={}",
            prefix.steps, baseline.steps, full.steps
        );
        // An unchanged caller grant that only just fits the original
        // fallback cannot pay for both trials. Prefix work must stay spent.
        let mut tight = Search::new(&problem, baseline.steps);
        assert!(!tight.run());
        assert_eq!(tight.limit, baseline.steps);
        let mut zero = 0;
        assert!(!depends(&problem, &mut zero));
        assert_eq!(zero, 0);
    }

    #[test]
    fn original_recursive_postcondition_has_a_constructive_two_world_witness() {
        // Child nodes are the callee's ensures equalities. Analysis excludes
        // each containing formula while checking whether that node depends
        // on its SF application; all OTHER selected facts remain mandatory.
        for (argument, result, expected) in [(0, 11, (0, 1)), (4, 5, (0, 1)), (7, 8, (1, 0))] {
            let (facts, node) =
                super::super::relevance::e18_completion_tests::witness_context(argument, result);
            let member = Term::call(
                "sf0",
                vec![Term::var(format!("v{argument}"), Sort::Int)],
                Sort::Int,
            );
            let alias_argument = if argument == 0 { 7 } else { 0 };
            let alias = Term::call(
                "sf0",
                vec![Term::var(format!("v{alias_argument}"), Sort::Int)],
                Sort::Int,
            );
            for include_alias in [false, true] {
                let mut members = vec![&member];
                if include_alias {
                    members.push(&alias);
                }
                let problem = Problem {
                    node: &node,
                    members,
                    sort: Sort::Int,
                    facts: facts.iter().collect(),
                    exact: false,
                };
                let mut search = Search::new(&problem, SEARCH_STEPS);
                search.k = [0, 1];
                for (name, value) in [
                    ("v0", 2),
                    ("v1", 0),
                    ("v2", 0),
                    ("v3", 0),
                    ("v4", 0),
                    ("v5", 1),
                    ("v6", 0),
                    ("v7", 1),
                    ("v8", 0),
                    ("v9", 1),
                    ("v10", 1),
                    ("v11", 1),
                    ("sq0", 0),
                ] {
                    search
                        .fixed
                        .insert((Fun::Var(name), Vec::new()), (value, true));
                }
                search.fixed.insert((Fun::Call("sf0"), vec![0]), (1, true));
                search.fixed.insert((Fun::Call("sf0"), vec![1]), (0, true));
                search.fixed.insert((Fun::Call("sf0"), vec![2]), (0, true));
                search
                    .fixed
                    .insert((Fun::Call("qa1"), Vec::new()), (1, true));
                assert_eq!(search.class_points(0), search.class_points(1));
                assert_eq!(search.both(&node), Some(expected));
                assert_eq!(
                    facts.iter().all(|fact| search.holds(fact, true)),
                    !include_alias,
                    "v{argument} alias={include_alias}"
                );
                assert_eq!(
                    search.satisfy_facts() && search.differs(&node),
                    !include_alias
                );
            }
        }
    }

    #[test]
    fn a_sole_repair_cannot_escape_validation_of_the_other_facts() {
        let x = Term::var("other", Sort::Int);
        let call = Term::call("actual", vec![Term::Int(0)], Sort::Int);
        let node = Term::eq(call.clone(), x.clone());
        let first = Term::le(x.clone(), Term::Int(0));
        for (second, expected) in [
            (Term::le(x.clone(), Term::Int(0)), true),
            (Term::le(Term::Int(1), x.clone()), false),
        ] {
            let mut budget = SEARCH_STEPS;
            assert_eq!(
                depends(
                    &Problem {
                        node: &node,
                        members: vec![&call],
                        sort: Sort::Int,
                        facts: vec![&first, &second],
                        exact: false,
                    },
                    &mut budget
                ),
                expected
            );
        }
        // No candidate succeeds for an empty disjunction. A failed sole
        // candidate likewise cannot supply a witness for a false fact.
        for impossible in [Term::Or(Vec::new()), Term::Bool(false)] {
            let mut budget = SEARCH_STEPS;
            assert!(!depends(
                &Problem {
                    node: &node,
                    members: vec![&call],
                    sort: Sort::Int,
                    facts: vec![&impossible],
                    exact: false,
                },
                &mut budget
            ));
        }
    }

    fn s(n: i128) -> Term {
        Term::call("sf0", vec![Term::Int(n)], Sort::Int)
    }

    fn var(name: &str, sort: Sort) -> Term {
        Term::var(name, sort)
    }

    fn ite(c: Term, a: Term, b: Term) -> Term {
        let sort = a.sort();
        Term::Ite(Box::new(c), Box::new(a), Box::new(b), sort)
    }

    fn eq(a: Term, b: Term) -> Term {
        Term::Cmp(CmpOp::Eq, Box::new(a), Box::new(b))
    }

    fn le(a: Term, b: Term) -> Term {
        Term::Cmp(CmpOp::Le, Box::new(a), Box::new(b))
    }

    fn check(node: &Term, member: &Term, facts: &[Term]) -> bool {
        check_in(node, member, facts, false)
    }

    fn check_in(node: &Term, member: &Term, facts: &[Term], exact: bool) -> bool {
        let problem = Problem {
            node,
            members: vec![member],
            sort: member.sort(),
            facts: facts.iter().collect(),
            exact,
        };
        let mut budget = usize::MAX;
        depends(&problem, &mut budget)
    }

    #[test]
    fn plain_atoms_depend() {
        let c = s(1);
        assert!(check(&eq(c.clone(), Term::Int(6)), &c, &[]));
        assert!(check(&le(c.clone(), s(2)), &c, &[]));
        let guarded = Term::Or(vec![
            Term::Not(Box::new(eq(var("x", Sort::Int), Term::Int(3)))),
            eq(c.clone(), Term::Int(6)),
        ]);
        assert!(check(&guarded, &c, &[]));
    }

    #[test]
    fn an_if_of_numerals_against_another_numeral_does_not() {
        let c = s(1);
        let cond = Term::Not(Box::new(le(c.clone(), Term::Int(7))));
        let value = ite(cond, Term::Int(1), Term::Int(2));
        let node = Term::Not(Box::new(eq(value.clone(), Term::Int(3))));
        assert!(!check(&node, &c, &[]));
        assert!(!check(&le(value.clone(), Term::Int(3)), &c, &[]));
        assert!(check(&eq(value, Term::Int(2)), &c, &[]));
    }

    #[test]
    fn complementary_branches_do_not() {
        let c = s(1);
        let p = Term::Not(Box::new(le(c.clone(), Term::Int(7))));
        let node = ite(p.clone(), p.clone(), Term::Not(Box::new(p)));
        assert!(!check(&node, &c, &[]));
    }

    #[test]
    fn facts_constrain_the_witness() {
        // With `x == 3`, `if s(1) > 7 { x } else { 3 } == 3` always holds.
        let c = s(1);
        let x = var("x", Sort::Int);
        let cond = Term::Not(Box::new(le(c.clone(), Term::Int(7))));
        let node = eq(ite(cond, x.clone(), Term::Int(3)), Term::Int(3));
        assert!(check(&node, &c, &[]));
        assert!(!check(&node, &c, &[eq(x, Term::Int(3))]));
    }

    #[test]
    fn facts_are_repaired_without_undoing_each_other() {
        // `0 <= y`, `!c || y == 1` and `c || y == 2` hold together only with
        // `y` following `c`; `c` is fixed by the subformula's own search.
        let c = s(1);
        let p = var("c", Sort::Bool);
        let y = var("y", Sort::Int);
        let node = Term::Or(vec![
            Term::Not(Box::new(p.clone())),
            eq(c.clone(), Term::Int(1)),
        ]);
        let facts = [
            le(Term::Int(0), y.clone()),
            Term::Or(vec![
                Term::Not(Box::new(p.clone())),
                eq(y.clone(), Term::Int(1)),
            ]),
            Term::Or(vec![p, eq(y, Term::Int(2))]),
        ];
        assert!(check(&node, &c, &facts));
    }

    #[test]
    fn arithmetic_is_a_function() {
        // `s(1) + 1 > s(1)` keeps its terms: Verus's `Add` is uninterpreted.
        let c = s(1);
        let add = Term::Arith(ArithOp::Add, Box::new(c.clone()), Box::new(Term::Int(1)));
        assert!(check(&Term::Not(Box::new(le(add, c.clone()))), &c, &[]));
    }

    #[test]
    fn exact_arithmetic_forces_values() {
        // `x + 1 == 2` leaves `x` open where `Add` is a function, and makes
        // it 1 where arithmetic is exact: `s(x)` reads the point of `s(1)`.
        let c = s(1);
        let x = var("x", Sort::Int);
        let node = eq(Term::call("sf0", vec![x.clone()], Sort::Int), c.clone());
        let arith = |op, a: Term, b: Term| Term::Arith(op, Box::new(a), Box::new(b));
        let plus_one = arith(ArithOp::Add, x.clone(), Term::Int(1));
        let fixed = [
            eq(plus_one.clone(), Term::Int(2)),
            eq(arith(ArithOp::Sub, x.clone(), Term::Int(1)), Term::Int(0)),
            eq(arith(ArithOp::Mul, Term::Int(2), x.clone()), Term::Int(2)),
            eq(
                Term::call(NL_MUL, vec![x.clone(), var("y", Sort::Int)], Sort::Int),
                Term::Int(2),
            ),
        ];
        for fact in &fixed[..3] {
            assert!(check_in(&node, &c, std::slice::from_ref(fact), false));
            assert!(!check_in(&node, &c, std::slice::from_ref(fact), true));
        }
        // `x * y == 2` with `y == 2`.
        let pinned = [fixed[3].clone(), eq(var("y", Sort::Int), Term::Int(2))];
        assert!(!check_in(&node, &c, &pinned, true));
        // Facts that leave `x` apart from 1 leave a witness.
        let open = [eq(plus_one, Term::Int(3))];
        assert!(check_in(&node, &c, &open, true));
        let square = Term::call(NL_MUL, vec![x.clone(), x.clone()], Sort::Int);
        assert!(check_in(&node, &c, &[eq(square, Term::Int(1))], true));
        // Division and remainder: `x / 2 == 0` and `x % 3 == 1` leave `x`
        // open, and make it 1 with `1 <= x` or `0 <= x < 3`.
        let half = eq(arith(ArithOp::Div, x.clone(), Term::Int(2)), Term::Int(0));
        let rem = eq(arith(ArithOp::Mod, x.clone(), Term::Int(3)), Term::Int(1));
        let lt3 = Term::Not(Box::new(le(Term::Int(3), x.clone())));
        assert!(check_in(&node, &c, std::slice::from_ref(&half), true));
        assert!(!check_in(
            &node,
            &c,
            &[half, le(Term::Int(1), x.clone())],
            true
        ));
        assert!(check_in(&node, &c, std::slice::from_ref(&rem), true));
        assert!(!check_in(&node, &c, &[rem, le(Term::Int(0), x), lt3], true));
    }

    #[test]
    fn calls_at_the_class_point_take_its_value() {
        // `if x == 1 { b } else { x == 1 }` forces `x == 1`, so `s(x)` reads
        // the point of `s(1)` and `s(x) == s(1)` holds in both worlds.
        let c = s(1);
        let x = var("x", Sort::Int);
        let sx = Term::call("sf0", vec![x.clone()], Sort::Int);
        let node = eq(sx.clone(), c.clone());
        let is1 = eq(x.clone(), Term::Int(1));
        let forced = ite(is1.clone(), var("b", Sort::Bool), is1);
        assert!(!check(&node, &c, &[forced]));
        let open = ite(
            eq(x.clone(), Term::Int(1)),
            var("b", Sort::Bool),
            eq(x.clone(), Term::Int(2)),
        );
        assert!(check(&node, &c, &[open]));
        // A bound met at its edge puts `s(x)` on the point; inside it does not.
        assert!(check(&node, &c, &[le(x, Term::Int(1))]));
    }

    #[test]
    fn nested_members_settle() {
        // The class of `s(s(1))`: its argument reads `s`, whose value at
        // the class's point would be the class's own.
        let outer = Term::call("sf0", vec![s(1)], Sort::Int);
        let y = var("y", Sort::Int);
        let other = Term::call("sf0", vec![y], Sort::Int);
        assert!(check(&eq(other, outer.clone()), &outer, &[]));
        assert!(check(&le(outer.clone(), Term::Int(4)), &outer, &[]));
    }

    #[test]
    fn boolean_arguments_are_told_apart() {
        let p = var("p", Sort::Bool);
        let q = var("q", Sort::Bool);
        let at = |c: Term| ite(c, Term::Int(1), Term::Int(2));
        assert!(!same_values(&[at(p.clone())], &[at(q)]));
        assert!(same_values(&[at(p.clone())], &[at(p)]));
    }

    #[test]
    fn argument_correspondence_requires_equal_sorts() {
        assert!(!same_values(&[Term::Bool(true)], &[Term::Int(1)]));
        assert!(!same_values(
            &[var("a", Sort::Poly)],
            &[var("a", Sort::TypeId)]
        ));
        assert!(!same_values(
            &[var("a", Sort::Nominal(0))],
            &[var("a", Sort::Nominal(1))]
        ));
    }

    #[test]
    fn wide_values_tell_arguments_apart() {
        let x = var("x", Sort::Int);
        assert!(same_values(&[Term::Int(1)], &[Term::Int(1)]));
        assert!(!same_values(std::slice::from_ref(&x), &[Term::Int(1)]));
        let ite_one = ite(var("b", Sort::Bool), Term::Int(1), Term::Int(1));
        assert!(same_values(&[ite_one], &[Term::Int(1)]));
        assert!(same_values(
            std::slice::from_ref(&x),
            std::slice::from_ref(&x)
        ));
    }
}

#[cfg(test)]
#[path = "witness_arithmetic_tests.rs"]
mod arithmetic_tests;
