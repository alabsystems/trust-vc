//! Quantifiers and choices: their solver vocabulary and their instances.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! The query language is quantifier free. A quantified formula is a
//! boolean function of its free variables, its atom `qa<k>`: `qa<k>(v)`
//! stands for the truth of the formula at `v`. A query states facts about
//! atoms, never their definitions:
//!
//! * the Skolem fact: `!qa(v) ==> !body(v, s)` for a `forall`, and
//!   `qa(v) ==> body(v, s)` for an `exists`, with fresh symbols `s`;
//! * instances: `qa(v) ==> body(v, t)` for a `forall`, and
//!   `!qa(v) ==> !body(v, t)` for an `exists`, at the terms `t` that
//!   E-matching on the quantifier's triggers finds among the applications
//!   Z3 has relevant (`super::relevance`), round after round, as Z3 makes
//!   them.
//!
//! Every fact holds when each atom is read as the truth of its formula, so
//! a query proved with them holds with the quantifiers. The instances are
//! ones Z3 makes too (Verus runs it with E-matching only), so a query is not
//! proved where Verus's is not. Z3 may make more (it matches modulo the
//! equalities it knows, and keeps going longer), so a failure here may be
//! one Verus does not report.
//!
//! A choice `choose|x| cond` with holes `h` (its maximal subexpressions
//! that mention nothing bound inside it, as in AIR's closures,
//! `air/src/closure.rs`) is one function `ch<k>_<i>(h)` per scalar leaf of
//! its value. Choices equal up to their holes share the functions. Verus's
//! axiom `forall h. (exists x. cond) ==> (exists x. cond && ch(h) == x)` is
//! instantiated at the applications Z3 has relevant, with its `exists x.
//! cond` an atom like any other; the value's type facts hold at every
//! application.

use std::collections::{HashMap, HashSet};
use std::fmt::Write;
use std::ops::Not;

use crate::expr::{Expr, ExprKind, Lit, QuantKind};
use crate::ids::LocalId;

use super::query::{Function, Symbol};
use super::relevance::{instance_gate, Analysis, CallRole, Position};
use super::spec::{SpecDef, Tables};
use super::term::{ArithOp, Sort, Term};
use super::trigger_pattern::{
    Head as TriggerHead, Pattern as TriggerPattern, Template as TriggerTemplate,
};
use super::val::{LeafTy, Shape, Val};
use crate::IntRange;

/// Instance rounds per query.
const ROUNDS: usize = 8;
/// Instances per query.
const MAX_INSTANCES: usize = 400;
/// Bindings tried per trigger group and atom in one round.
const MAX_BINDINGS: usize = 200;
/// Term nodes the relevance analysis of one query may read.
const ANALYSIS_BUDGET: usize = 200_000;
/// The largest relevance condition written out in a fact.
const RELEVANCE_TERM_CAP: usize = 64;

/// A quantified formula over the variables `qx<i>` and the parameters
/// `qp<i>`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct QuantTemplate {
    pub(crate) kind: QuantKind,
    /// Sorts of the bound variables `qx0, qx1, ...`.
    pub(crate) vars: Vec<Sort>,
    /// Sorts of the parameters `qp0, qp1, ...`: the free variables.
    pub(crate) params: Vec<Sort>,
    /// The formula, with the type facts of the variables (`==>` for
    /// `forall`, `&&` for `exists`).
    pub(crate) body: Term,
    /// Trigger groups; every group mentions every variable.
    pub(super) triggers: Vec<Vec<TriggerPattern>>,
}

/// A choice, over the variables `qx<i>` and the parameters `qp<i>` (the
/// holes' leaves, then any other free variable).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ChooseTemplate {
    pub(crate) vars: Vec<Sort>,
    pub(crate) params: Vec<Sort>,
    /// The condition with the variables' type facts.
    pub(crate) cond: Term,
    /// The value, one term per leaf, with the leaf's type.
    pub(crate) result: Vec<(Term, LeafTy)>,
    /// The atom of `exists vars. cond`.
    pub(crate) exists: usize,
}

/// The quantifiers and choices of one crate.
#[derive(Debug, Default)]
pub(crate) struct Registry {
    quants: Vec<QuantTemplate>,
    quant_index: HashMap<QuantTemplate, usize>,
    chooses: Vec<ChooseTemplate>,
    choose_index: HashMap<String, usize>,
    next_name: u64,
}

/// Solver name of atom `k`.
fn atom_name(k: usize) -> String {
    format!("qa{k}")
}

/// Solver name of leaf `i` of choice `k`.
fn choose_name(k: usize, i: usize) -> String {
    format!("ch{k}_{i}")
}

fn digits(text: &str) -> Option<usize> {
    if text.is_empty() || !text.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    text.parse().ok()
}

/// The atom index named by `name`.
pub(crate) fn atom_of(name: &str) -> Option<usize> {
    canonical_index(name, "qa")
}

/// The choice and leaf named by `name`.
pub(crate) fn choose_of(name: &str) -> Option<(usize, usize)> {
    let (k, i) = name.strip_prefix("ch")?.split_once('_')?;
    Some((canonical_index(k, "")?, canonical_index(i, "")?))
}

/// Canonical name of bound variable `i`.
fn var_name(i: usize) -> String {
    format!("qx{i}")
}

/// Canonical name of parameter `i`.
fn param_name(i: usize) -> String {
    format!("qp{i}")
}

/// The variables of `t` in order of first occurrence, with their sorts.
pub(crate) fn vars_in_order(t: &Term, out: &mut Vec<(String, Sort)>) -> bool {
    match t {
        Term::Var { name, sort } => match out.iter().find(|(seen, _)| seen == name) {
            Some((_, previous)) => previous == sort,
            None => {
                out.push((name.clone(), *sort));
                true
            }
        },
        Term::Bool(_) | Term::Int(_) => true,
        Term::Not(a) | Term::Neg(a) => vars_in_order(a, out),
        Term::And(cs) | Term::Or(cs) | Term::Call { args: cs, .. } => {
            cs.iter().all(|c| vars_in_order(c, out))
        }
        Term::Implies(a, b) | Term::Cmp(_, a, b) | Term::Arith(_, a, b) => {
            vars_in_order(a, out) && vars_in_order(b, out)
        }
        Term::Ite(c, a, b, _) => {
            vars_in_order(c, out) && vars_in_order(a, out) && vars_in_order(b, out)
        }
    }
}

fn native_tuple(values: &[Term], sorts: &[Sort]) -> bool {
    values.len() == sorts.len()
        && values.iter().zip(sorts).all(|(value, sort)| {
            super::closed_templates::native_sort(*sort) && value.sort() == *sort
        })
}

fn canonical_index(name: &str, prefix: &str) -> Option<usize> {
    let suffix = name.strip_prefix(prefix)?;
    if suffix.len() > 1 && suffix.starts_with('0') {
        return None;
    }
    digits(suffix)
}

fn template_variables(term: &Term, params: &[Sort], vars: &[Sort]) -> bool {
    match term {
        Term::Var { name, sort } => {
            let expected = canonical_index(name, "qx")
                .and_then(|i| vars.get(i))
                .or_else(|| canonical_index(name, "qp").and_then(|i| params.get(i)));
            expected == Some(sort) && super::closed_templates::native_sort(*sort)
        }
        Term::Bool(_) | Term::Int(_) => true,
        Term::Not(a) | Term::Neg(a) => template_variables(a, params, vars),
        Term::And(args) | Term::Or(args) | Term::Call { args, .. } => {
            args.iter().all(|arg| template_variables(arg, params, vars))
        }
        Term::Implies(a, b) | Term::Cmp(_, a, b) | Term::Arith(_, a, b) => {
            template_variables(a, params, vars) && template_variables(b, params, vars)
        }
        Term::Ite(c, a, b, _) => {
            template_variables(c, params, vars)
                && template_variables(a, params, vars)
                && template_variables(b, params, vars)
        }
    }
}

impl Registry {
    /// A fresh name for a variable bound while translating.
    pub(crate) fn fresh_name(&mut self, prefix: &str) -> String {
        let name = format!("{prefix}{}", self.next_name);
        self.next_name = self.next_name.wrapping_add(1);
        name
    }

    /// A value of `shape` made of fresh variables, listed in `out`.
    pub(crate) fn fresh_val(
        &mut self,
        shape: &Shape,
        prefix: &str,
        out: &mut Vec<(String, LeafTy)>,
    ) -> Val {
        match shape {
            Shape::Leaf(leaf) => {
                let name = self.fresh_name(prefix);
                out.push((name.clone(), *leaf));
                Val::Leaf(Term::var(name, leaf.sort()))
            }
            Shape::Node(children) => Val::Node(
                children
                    .iter()
                    .map(|child| self.fresh_val(child, prefix, out))
                    .collect(),
            ),
        }
    }

    /// The term of a quantified formula whose variables are `bound` (named
    /// as in `body`), with its type facts already in `body`.
    pub(super) fn quant(
        &mut self,
        kind: QuantKind,
        bound: &[(String, Sort)],
        body: Term,
        triggers: Vec<Vec<TriggerPattern>>,
    ) -> Option<Term> {
        let mut all = Vec::new();
        if body.sort() != Sort::Bool || !vars_in_order(&body, &mut all) {
            return None;
        }
        for term in triggers.iter().flatten() {
            if !vars_in_order(term.term(), &mut all) {
                return None;
            }
        }
        let mut seen = HashSet::new();
        if bound.iter().any(|(name, sort)| {
            !super::closed_templates::native_sort(*sort)
                || !seen.insert(name)
                || all.iter().any(|(n, s)| n == name && s != sort)
        }) || all
            .iter()
            .any(|(_, sort)| !super::closed_templates::native_sort(*sort))
        {
            return None;
        }
        let free: Vec<(String, Sort)> = all
            .into_iter()
            .filter(|(name, _)| !bound.iter().any(|(b, _)| b == name))
            .collect();
        let mut map: HashMap<&str, Term> = HashMap::new();
        for (i, (name, sort)) in bound.iter().enumerate() {
            map.insert(name.as_str(), Term::var(var_name(i), *sort));
        }
        for (i, (name, sort)) in free.iter().enumerate() {
            map.insert(name.as_str(), Term::var(param_name(i), *sort));
        }
        let template = QuantTemplate {
            kind,
            vars: bound.iter().map(|(_, sort)| *sort).collect(),
            params: free.iter().map(|(_, sort)| *sort).collect(),
            body: body.substitute(&map),
            triggers: triggers
                .iter()
                .map(|group| group.iter().map(|t| t.substitute(&map)).collect())
                .collect(),
        };
        let k = self.register_quant(template);
        let args = free
            .iter()
            .map(|(name, sort)| Term::var(name.clone(), *sort))
            .collect();
        Some(Term::call(atom_name(k), args, Sort::Bool))
    }

    fn register_quant(&mut self, template: QuantTemplate) -> usize {
        if let Some(&k) = self.quant_index.get(&template) {
            return k;
        }
        let k = self.quants.len();
        self.quant_index.insert(template.clone(), k);
        self.quants.push(template);
        k
    }

    /// The choice with shape `key`, whose condition and value are `cond`
    /// and `result` over the variables `bound` and the hole leaves `holes`
    /// (named as in the terms): its index and its parameters' arguments, or
    /// `None` when an earlier choice of the same shape has another
    /// template.
    pub(crate) fn choose(
        &mut self,
        key: String,
        bound: &[(String, Sort)],
        holes: &[(String, Sort)],
        cond: Term,
        result: Vec<(Term, LeafTy)>,
        triggers: Vec<Vec<Term>>,
    ) -> Option<(usize, Vec<String>)> {
        let triggers: Vec<Vec<TriggerPattern>> = triggers
            .into_iter()
            .map(|group| {
                group
                    .into_iter()
                    .map(TriggerPattern::application)
                    .collect::<Option<Vec<_>>>()
            })
            .collect::<Option<Vec<_>>>()?;
        let mut all = Vec::new();
        if cond.sort() != Sort::Bool || !vars_in_order(&cond, &mut all) {
            return None;
        }
        for (term, _) in &result {
            if !vars_in_order(term.term(), &mut all) {
                return None;
            }
        }
        if result.iter().any(|(term, leaf)| term.sort() != leaf.sort()) {
            return None;
        }
        for term in triggers.iter().flatten() {
            if !vars_in_order(term.term(), &mut all) {
                return None;
            }
        }
        let mut declared = HashMap::new();
        for (name, sort) in bound.iter().chain(holes) {
            if !super::closed_templates::native_sort(*sort)
                || declared.insert(name, sort).is_some()
                || all.iter().any(|(n, s)| n == name && s != sort)
            {
                return None;
            }
        }
        if all
            .iter()
            .any(|(_, sort)| !super::closed_templates::native_sort(*sort))
        {
            return None;
        }
        let mut free: Vec<(String, Sort)> = holes.to_vec();
        for (name, sort) in all {
            let known =
                bound.iter().any(|(b, _)| *b == name) || free.iter().any(|(f, _)| *f == name);
            if !known {
                free.push((name, sort));
            }
        }
        let mut map: HashMap<&str, Term> = HashMap::new();
        for (i, (name, sort)) in bound.iter().enumerate() {
            map.insert(name.as_str(), Term::var(var_name(i), *sort));
        }
        for (i, (name, sort)) in free.iter().enumerate() {
            map.insert(name.as_str(), Term::var(param_name(i), *sort));
        }
        let vars: Vec<Sort> = bound.iter().map(|(_, sort)| *sort).collect();
        let params: Vec<Sort> = free.iter().map(|(_, sort)| *sort).collect();
        let cond = cond.substitute(&map);
        let triggers: Vec<Vec<TriggerPattern>> = triggers
            .iter()
            .map(|group| group.iter().map(|t| t.substitute(&map)).collect())
            .collect();
        let exists = self.register_quant(QuantTemplate {
            kind: QuantKind::Exists,
            vars: vars.clone(),
            params: params.clone(),
            body: cond.clone(),
            triggers,
        });
        let template = ChooseTemplate {
            vars,
            params,
            cond,
            result: result
                .into_iter()
                .map(|(term, leaf)| (term.substitute(&map), leaf))
                .collect(),
            exists,
        };
        let names = free.into_iter().map(|(name, _)| name).collect();
        if let Some(&k) = self.choose_index.get(&key) {
            return (self.chooses[k] == template).then_some((k, names));
        }
        let k = self.chooses.len();
        self.choose_index.insert(key, k);
        self.chooses.push(template);
        Some((k, names))
    }

    /// The application of leaf `i` of choice `k` at `args`.
    pub(crate) fn choose_app(&self, k: usize, i: usize, args: Vec<Term>) -> Option<Term> {
        let template = self.chooses.get(k)?;
        if !native_tuple(&args, &template.params) {
            return None;
        }
        let (_, leaf) = template.result.get(i)?;
        Some(Term::call(choose_name(k, i), args, leaf.sort()))
    }

    /// Borrow the exact registered signature without copying names or sorts.
    pub(super) fn signature(&self, name: &str) -> Option<(&[Sort], Sort)> {
        if let Some(k) = atom_of(name) {
            let template = self.quants.get(k)?;
            return Some((&template.params, Sort::Bool));
        }
        let (k, i) = choose_of(name)?;
        let template = self.chooses.get(k)?;
        let (_, leaf) = template.result.get(i)?;
        Some((&template.params, leaf.sort()))
    }

    /// The declaration of an atom or choice function named `name`.
    pub(crate) fn function(&self, name: &str) -> Option<Function> {
        let (params, ret) = self.signature(name)?;
        Some(Function {
            name: name.to_string(),
            params: params.to_vec(),
            ret,
        })
    }

    /// The bounds of a choice function's values, when its type bounds them.
    pub(crate) fn range(&self, name: &str) -> Option<(Option<i128>, Option<u128>)> {
        let (k, i) = choose_of(name)?;
        let (_, leaf) = self.chooses.get(k)?.result.get(i)?;
        let bounds = leaf.bounds();
        (bounds != (None, None)).then_some(bounds)
    }

    /// Does the registry name a function in `t`?
    pub(crate) fn mentioned_in(&self, t: &Term) -> bool {
        let mut found = false;
        t.for_each_call(&mut |name, _| {
            found = found || atom_of(name).is_some() || choose_of(name).is_some();
        });
        found
    }

    /// Exact call names and interpreted arithmetic operations at trigger
    /// roots. The same query Analysis grant prepays scans, name copies/hash
    /// and set growth; no head is itself a material seed or an instance.
    fn trigger_heads(&self, pay: &mut impl FnMut(usize) -> bool) -> Option<TriggerHeads> {
        let mut out = TriggerHeads::default();
        for template in &self.quants {
            if !pay(1) {
                return None;
            }
            for term in template.triggers.iter().flatten() {
                if !pay(4) {
                    return None;
                }
                if !term.valid_head(pay) {
                    return None;
                }
                match (term.head(), term.term()) {
                    (TriggerHead::Call, Term::Call { name, .. }) => {
                        if !pay(name.len().saturating_mul(4)) {
                            return None;
                        }
                        out.calls.insert(name.clone());
                    }
                    (TriggerHead::Arithmetic(op), _) => {
                        out.arithmetic.insert(op);
                    }
                    (TriggerHead::Clip(range), _) => {
                        if !pay(128) {
                            return None;
                        }
                        out.calls.insert(super::spec::clip_oob_name(range));
                        out.clips.insert(range);
                    }
                    _ => return None,
                }
            }
        }
        Some(out)
    }
}

/// Reserve the subsequent checked substitution and its parameter map. The
/// census itself is charged node by node, rather than first calling size().
fn charge_substitution(
    term: &Term,
    args: &[Term],
    binding: &[Term],
    pay: &mut impl FnMut(usize) -> bool,
) -> bool {
    for value in args.iter().chain(binding) {
        // qx/qp plus a usize index is at most 22 bytes; reserve all name/map
        // copies before formatting and the existing map's value copies.
        if !pay(96)
            || !super::closed_templates::charge_term(value, pay)
            || !super::closed_templates::charge_term(value, pay)
        {
            return false;
        }
    }
    fn walk(
        term: &Term,
        args: &[Term],
        binding: &[Term],
        pay: &mut impl FnMut(usize) -> bool,
    ) -> bool {
        if !pay(4) {
            return false;
        }
        match term {
            Term::Bool(_) | Term::Int(_) => true,
            Term::Var { name, .. } => {
                if !pay(name.len().saturating_mul(4)) {
                    return false;
                }
                let replacement = canonical_index(name, "qx")
                    .and_then(|i| binding.get(i))
                    .or_else(|| canonical_index(name, "qp").and_then(|i| args.get(i)));
                replacement.is_none_or(|value| super::closed_templates::charge_term(value, pay))
            }
            Term::Not(a) | Term::Neg(a) => walk(a, args, binding, pay),
            Term::And(values) | Term::Or(values) => {
                values.iter().all(|value| walk(value, args, binding, pay))
            }
            Term::Call {
                name, args: values, ..
            } => {
                pay(name.len().saturating_mul(4))
                    && values.iter().all(|value| walk(value, args, binding, pay))
            }
            Term::Implies(a, b) | Term::Cmp(_, a, b) | Term::Arith(_, a, b) => {
                walk(a, args, binding, pay) && walk(b, args, binding, pay)
            }
            Term::Ite(c, a, b, _) => {
                walk(c, args, binding, pay)
                    && walk(a, args, binding, pay)
                    && walk(b, args, binding, pay)
            }
        }
    }
    walk(term, args, binding, pay)
}

/// `t` with the parameters at `args` and the variables at `binding`. Production
/// callers reserve the walk and all copies with charge_substitution first.

fn at(t: &Term, args: &[Term], binding: &[Term], params: &[Sort], vars: &[Sort]) -> Option<Term> {
    if !native_tuple(args, params)
        || !native_tuple(binding, vars)
        || !template_variables(t, params, vars)
    {
        return None;
    }
    let names: Vec<(String, Term)> = args
        .iter()
        .enumerate()
        .map(|(i, a)| (param_name(i), a.clone()))
        .chain(
            binding
                .iter()
                .enumerate()
                .map(|(i, b)| (var_name(i), b.clone())),
        )
        .collect();
    let map = names
        .iter()
        .map(|(name, term)| (name.as_str(), term.clone()))
        .collect();
    Some(t.substitute(&map))
}

fn with_params<T: TriggerTemplate>(
    ts: &[T],
    args: &[Term],
    params: &[Sort],
    vars: &[Sort],
) -> Option<Vec<T>> {
    if !native_tuple(args, params)
        || ts
            .iter()
            .any(|term| !template_variables(term.term(), params, vars))
    {
        return None;
    }
    let names: Vec<(String, Term)> = args
        .iter()
        .enumerate()
        .map(|(i, a)| (param_name(i), a.clone()))
        .collect();
    let map = names
        .iter()
        .map(|(name, term)| (name.as_str(), term.clone()))
        .collect();
    Some(ts.iter().map(|term| term.substitute(&map)).collect())
}

fn matches(
    pattern: &Term,
    term: &Term,
    binding: &mut HashMap<String, Term>,
    vars: &[Sort],
    vocabulary: &super::closed_templates::Vocabulary,
    registry: &Registry,
    pay: &mut impl FnMut(usize) -> bool,
) -> bool {
    if !pay(1) || pattern.sort() != term.sort() {
        return false;
    }
    match (pattern, term) {
        (Term::Var { name, sort }, _) if name.starts_with("qx") => {
            if !pay(name.len().saturating_mul(4).saturating_add(1)) {
                return false;
            }
            let Some(index) = canonical_index(name, "qx") else {
                return false;
            };
            if vars.get(index) != Some(sort) {
                return false;
            }
            match binding.get(name) {
                Some(previous) => {
                    super::closed_templates::charge_term(previous, pay)
                        && super::closed_templates::charge_term(term, pay)
                        && previous == term
                }
                None => {
                    if !pay(name.len()) || !super::closed_templates::charge_term(term, pay) {
                        return false;
                    }
                    binding.insert(name.clone(), term.clone());
                    true
                }
            }
        }
        (
            Term::Call {
                name: f,
                args: ps,
                sort,
            },
            Term::Call {
                name: g,
                args,
                sort: actual,
            },
        ) => {
            pay(f
                .len()
                .saturating_add(g.len())
                .saturating_add(ps.len())
                .saturating_add(args.len()))
                && f == g
                && sort == actual
                && ps.len() == args.len()
                && vocabulary.call_is_typed(registry, f, ps, *sort, pay)
                && vocabulary.call_is_typed(registry, g, args, *actual, pay)
                && ps
                    .iter()
                    .zip(args)
                    .all(|(p, a)| matches(p, a, binding, vars, vocabulary, registry, pay))
        }
        (Term::Arith(op, p, q), Term::Arith(op2, a, b)) => {
            op == op2
                && matches(p, a, binding, vars, vocabulary, registry, pay)
                && matches(q, b, binding, vars, vocabulary, registry, pay)
        }
        (Term::Cmp(op, p, q), Term::Cmp(actual, a, b)) => {
            op == actual
                && matches(p, a, binding, vars, vocabulary, registry, pay)
                && matches(q, b, binding, vars, vocabulary, registry, pay)
        }
        (Term::And(ps), Term::And(args)) | (Term::Or(ps), Term::Or(args)) => {
            pay(ps.len().saturating_add(args.len()))
                && ps.len() == args.len()
                && ps
                    .iter()
                    .zip(args)
                    .all(|(p, a)| matches(p, a, binding, vars, vocabulary, registry, pay))
        }
        (Term::Ite(pc, py, pn, sort), Term::Ite(c, y, n, actual)) => {
            sort == actual
                && matches(pc, c, binding, vars, vocabulary, registry, pay)
                && matches(py, y, binding, vars, vocabulary, registry, pay)
                && matches(pn, n, binding, vars, vocabulary, registry, pay)
        }
        (Term::Neg(p), Term::Neg(a)) | (Term::Not(p), Term::Not(a)) => {
            matches(p, a, binding, vars, vocabulary, registry, pay)
        }
        _ => {
            super::closed_templates::charge_term(pattern, pay)
                && super::closed_templates::charge_term(term, pay)
                && pattern == term
        }
    }
}

/// What instantiation adds to a query.
#[derive(Debug, Default)]
pub(crate) struct Instances {
    /// Facts, in written form (spec functions not inlined), each with its
    /// place in Verus's query.
    pub(crate) facts: Vec<(Term, Position)>,
    /// Definitions of the relevance symbols the facts keep.
    pub(crate) definitions: Vec<Term>,
    /// Skolem constants and relevance symbols.
    pub(crate) symbols: Vec<Symbol>,
}

/// One relevant application and the condition under which it is.
type Item = (Term, Term);

/// Lookup aids only. A match still checks the whole actual typed term,
/// registered call signature, rigid type pairs and every qx binder sort.
#[derive(Default)]
struct TriggerHeads {
    calls: HashSet<String>,
    arithmetic: HashSet<ArithOp>,
    clips: HashSet<IntRange>,
}

#[derive(Default)]
struct TriggerIndex<'a, 'name> {
    calls: HashMap<&'name str, Vec<&'a Item>>,
    arithmetic: HashMap<ArithOp, Vec<&'a Item>>,
    clips: HashMap<IntRange, Vec<&'a Item>>,
}

// Existing call-only unit fixtures construct the same production index;
// arithmetic occupies a separate exact-operation namespace.
#[cfg(test)]
impl<'a, 'name> FromIterator<(&'name str, Vec<&'a Item>)> for TriggerIndex<'a, 'name> {
    fn from_iter<T: IntoIterator<Item = (&'name str, Vec<&'a Item>)>>(values: T) -> Self {
        Self {
            calls: values.into_iter().collect(),
            arithmetic: HashMap::new(),
            clips: HashMap::new(),
        }
    }
}

/// The facts about the atoms and choices of a query whose formulas, as
/// written, are `hypotheses` and `goal`: Skolem facts, E-matching
/// instances and choice axioms, in rounds (see the module documentation).
/// `defs` are the definitions the query inlines. Running out of a budget
/// only stops instantiating.
pub(crate) fn instantiate(
    ctx: &super::val::Ctx<'_>,
    reg: &Registry,
    hypotheses: &[(Term, Position)],
    goal: &(Term, Position),
    defs: &HashMap<&str, &SpecDef>,
    tables: &Tables,
) -> Instances {
    let mut head_work = ANALYSIS_BUDGET;
    let Some(heads) = reg.trigger_heads(&mut |cost| match head_work.checked_sub(cost) {
        Some(left) => {
            head_work = left;
            true
        }
        None => false,
    }) else {
        return Instances::default();
    };
    let role = |name: &str| {
        let collect =
            heads.calls.contains(name) || atom_of(name).is_some() || choose_of(name).is_some();
        match (collect, defs.contains_key(name)) {
            (true, true) => CallRole::CollectDefined,
            (true, false) => CallRole::Collect,
            (false, true) => CallRole::Defined,
            (false, false) => CallRole::Other,
        }
    };
    let mut analysis = Analysis::new(&role, defs, head_work)
        .with_arithmetic_triggers(&heads.arithmetic)
        .with_clip_triggers(&heads.clips)
        .with_ranges(&tables.ranged)
        .with_typings(&tables.typings)
        .with_type_context(ctx)
        .with_prefix("rq");
    let mut out = Instances::default();
    let vocabulary = {
        let mut pay = |cost| analysis.charge(cost).is_ok();
        super::closed_templates::Vocabulary::new(ctx, &tables.functions, &tables.sigs, &mut pay)
    };
    let Some(vocabulary) = vocabulary else {
        return out;
    };
    let Ok(seeds) = analysis.seeds(hypotheses, goal) else {
        return out;
    };
    let mut pool: Vec<Item> = seeds.into_items();
    // The conditions found for each application.
    let mut conds: HashMap<Term, Vec<Term>> = pool
        .iter()
        .map(|(call, cond)| (call.clone(), vec![cond.clone()]))
        .collect();
    let mut facts: Vec<(Term, Option<Term>)> = Vec::new();
    let mut skolemized: HashSet<Term> = HashSet::new();
    let mut chosen: HashSet<(usize, Vec<Term>)> = HashSet::new();
    // Instances made, by atom and binding. Each is made once, under the
    // condition first found; a condition found later is not added, which
    // only leaves out instances.
    let mut made: HashSet<(Term, Vec<Term>)> = HashSet::new();
    let mut next_skolem = 0u64;
    let mut skolems = |sorts: &[Sort], symbols: &mut Vec<Symbol>| -> Vec<Term> {
        sorts
            .iter()
            .map(|sort| {
                let name = format!("sq{next_skolem}");
                next_skolem += 1;
                symbols.push(Symbol {
                    name: name.clone(),
                    sort: *sort,
                    display: "witness".to_string(),
                });
                Term::var(name, *sort)
            })
            .collect()
    };

    'rounds: for _ in 0..ROUNDS {
        let mut found: Vec<Item> = Vec::new();
        let mut index = TriggerIndex::default();
        for item in &pool {
            if analysis.charge(4).is_err() {
                break 'rounds;
            }
            match &item.0 {
                Term::Call { name, .. } => {
                    if analysis.charge(name.len()).is_err() {
                        break 'rounds;
                    }
                    index.calls.entry(name.as_str()).or_default().push(item);
                }
                Term::Arith(op, ..) => {
                    index.arithmetic.entry(*op).or_default().push(item);
                }
                Term::Ite(..) => {
                    for range in &heads.clips {
                        if super::spec::clip_fallback(&item.0, *range, &mut |cost| {
                            analysis.charge(cost).is_ok()
                        })
                        .is_some()
                        {
                            index.clips.entry(*range).or_default().push(item);
                        }
                    }
                }
                _ => {}
            }
        }
        let read = |body: &Term, cond: Term, analysis: &mut Analysis<'_>, found: &mut Vec<Item>| {
            if let Ok(conds) = analysis.body(body) {
                for (call, inner) in conds.into_items() {
                    found.push((call, Term::and([cond.clone(), inner])));
                }
            }
        };
        let mut new_facts: Vec<(Term, Option<Term>)> = Vec::new();
        for (call, cond) in &pool {
            let Term::Call { name, args, .. } = call else {
                continue;
            };
            let typed = {
                let mut pay = |cost| analysis.charge(cost).is_ok();
                vocabulary.ground(reg, call, &mut pay)
            };
            if !typed {
                continue;
            }
            if let Some(k) = atom_of(name) {
                let Some(template) = reg.quants.get(k) else {
                    continue;
                };
                if !native_tuple(args, &template.params)
                    || template
                        .vars
                        .iter()
                        .any(|sort| !super::closed_templates::native_sort(*sort))
                {
                    continue;
                }
                let holds = match template.kind {
                    QuantKind::Forall => call.clone(),
                    QuantKind::Exists => call.clone().not(),
                };
                if skolemized.insert(call.clone()) {
                    if analysis.charge(template.vars.len()).is_err() {
                        continue;
                    }
                    let witness = skolems(&template.vars, &mut out.symbols);
                    if !charge_substitution(&template.body, args, &witness, &mut |cost| {
                        analysis.charge(cost).is_ok()
                    }) {
                        continue;
                    }
                    let Some(body) = at(
                        &template.body,
                        args,
                        &witness,
                        &template.params,
                        &template.vars,
                    ) else {
                        continue;
                    };
                    let fact = match template.kind {
                        QuantKind::Forall => Term::implies(call.clone().not(), body.clone().not()),
                        QuantKind::Exists => Term::implies(call.clone(), body.clone()),
                    };
                    let when = Term::and([cond.clone(), holds.clone().not()]);
                    read(&body, when, &mut analysis, &mut found);
                    new_facts.push((fact, None));
                }
                for group in &template.triggers {
                    if !group.iter().all(|term| {
                        charge_substitution(term.term(), args, &[], &mut |cost| {
                            analysis.charge(cost).is_ok()
                        })
                    }) {
                        break;
                    }
                    let Some(patterns) = with_params(group, args, &template.params, &template.vars)
                    else {
                        continue;
                    };
                    let found_bindings = {
                        let mut pay = |cost| analysis.charge(cost).is_ok();
                        bindings(
                            &patterns,
                            &index,
                            &template.vars,
                            &vocabulary,
                            reg,
                            &mut pay,
                        )
                    };
                    for (binding, conds) in found_bindings {
                        if made.len() >= MAX_INSTANCES {
                            break;
                        }
                        if !made.insert((call.clone(), binding.clone())) {
                            continue;
                        }
                        let rel = Term::and(std::iter::once(cond.clone()).chain(conds));
                        if !charge_substitution(&template.body, args, &binding, &mut |cost| {
                            analysis.charge(cost).is_ok()
                        }) {
                            break;
                        }
                        let Some(body) = at(
                            &template.body,
                            args,
                            &binding,
                            &template.params,
                            &template.vars,
                        ) else {
                            continue;
                        };
                        let gate = instance_gate(std::slice::from_ref(&body));
                        let fact = match template.kind {
                            QuantKind::Forall => Term::implies(
                                rel.clone(),
                                Term::implies(call.clone(), body.clone()),
                            ),
                            QuantKind::Exists => Term::implies(
                                rel.clone(),
                                Term::implies(call.clone().not(), body.clone().not()),
                            ),
                        };
                        let when = Term::and([rel, holds.clone(), gate.clone()]);
                        read(&body, when, &mut analysis, &mut found);
                        new_facts.push((fact, Some(gate)));
                    }
                }
            } else if let Some((k, _)) = choose_of(name) {
                let Some(template) = reg.chooses.get(k) else {
                    continue;
                };
                if !native_tuple(args, &template.params)
                    || template
                        .vars
                        .iter()
                        .any(|sort| !super::closed_templates::native_sort(*sort))
                    || !chosen.insert((k, args.clone()))
                {
                    continue;
                }
                if analysis.charge(template.vars.len()).is_err() {
                    continue;
                }
                let witness = skolems(&template.vars, &mut out.symbols);
                if !charge_substitution(&template.cond, args, &witness, &mut |cost| {
                    analysis.charge(cost).is_ok()
                }) {
                    continue;
                }
                let Some(condition) = at(
                    &template.cond,
                    args,
                    &witness,
                    &template.params,
                    &template.vars,
                ) else {
                    continue;
                };
                let mut parts = vec![condition];
                let mut complete = true;
                for (i, (value, leaf)) in template.result.iter().enumerate() {
                    if value.sort() != leaf.sort()
                        || !charge_substitution(value, args, &witness, &mut |cost| {
                            analysis.charge(cost).is_ok()
                        })
                    {
                        complete = false;
                        break;
                    }
                    let Some(value) = at(value, args, &witness, &template.params, &template.vars)
                    else {
                        complete = false;
                        break;
                    };
                    let Some(app) = reg.choose_app(k, i, args.clone()) else {
                        complete = false;
                        break;
                    };
                    parts.push(Term::eq(value, app));
                }
                if !complete {
                    continue;
                }
                let chosen_value = Term::and(parts);
                let exists = Term::call(atom_name(template.exists), args.clone(), Sort::Bool);
                let fact = Term::implies(
                    cond.clone(),
                    Term::implies(exists.clone(), chosen_value.clone()),
                );
                found.push((exists.clone(), cond.clone()));
                read(
                    &chosen_value,
                    Term::and([cond.clone(), exists]),
                    &mut analysis,
                    &mut found,
                );
                new_facts.push((fact, None));
            }
        }
        if new_facts.is_empty() {
            break;
        }
        facts.extend(new_facts);
        for (call, cond) in found {
            let entry = conds.entry(call.clone()).or_default();
            if entry.contains(&cond) {
                continue;
            }
            entry.push(cond);
            let cond = Term::or(entry.iter().cloned());
            match pool.iter_mut().find(|(known, _)| *known == call) {
                // Relevant under another condition too.
                Some(existing) => existing.1 = cond,
                None => pool.push((call, cond)),
            }
        }
    }

    let (terms, gates): (Vec<Term>, Vec<Option<Term>>) = facts.into_iter().unzip();
    let resolved = analysis.namer.resolve_each(terms, RELEVANCE_TERM_CAP);
    out.symbols.extend(resolved.symbols);
    out.definitions = resolved.definitions;
    for (fact, gate) in resolved.facts.into_iter().zip(gates) {
        if fact == Term::Bool(true) {
            continue;
        }
        out.facts.push((fact, Position { late: true, gate }));
    }
    out
}

/// Every binding of the variables `qx0 .. qx<n-1>` under which each of
/// `patterns` matches an application of `index`, with the conditions of the
/// applications matched.
fn bindings<T: TriggerTemplate>(
    patterns: &[T],
    index: &TriggerIndex<'_, '_>,
    vars: &[Sort],
    vocabulary: &super::closed_templates::Vocabulary,
    registry: &Registry,
    pay: &mut impl FnMut(usize) -> bool,
) -> Vec<(Vec<Term>, Vec<Term>)> {
    let mut partial: Vec<(HashMap<String, Term>, Vec<Term>)> = vec![(HashMap::new(), Vec::new())];
    for pattern in patterns {
        if !pattern.valid_head(pay) || !vocabulary.ground(registry, pattern.term(), pay) {
            return Vec::new();
        }
        let Some(head) = pattern.root() else {
            return Vec::new();
        };
        let candidates = match (head, pattern.term()) {
            (TriggerHead::Call, Term::Call { name, .. }) => {
                if !pay(name.len().saturating_add(1)) {
                    return Vec::new();
                }
                index.calls.get(name.as_str())
            }
            (TriggerHead::Arithmetic(op), _) => {
                if !pay(1) {
                    return Vec::new();
                }
                index.arithmetic.get(&op)
            }
            (TriggerHead::Clip(range), _) => {
                if !pay(1) {
                    return Vec::new();
                }
                index.clips.get(&range)
            }
            _ => return Vec::new(),
        };
        let Some(candidates) = candidates else {
            return Vec::new();
        };
        let mut next = Vec::new();
        'extend: for (binding, conds) in &partial {
            for (term, cond) in candidates {
                if next.len() >= MAX_BINDINGS {
                    break 'extend;
                }
                if !pay(1) {
                    return Vec::new();
                }
                for (name, term) in binding {
                    if !pay(name.len().saturating_add(1))
                        || !super::closed_templates::charge_term(term, pay)
                    {
                        return Vec::new();
                    }
                }
                for term in conds.iter().chain(std::iter::once(cond)) {
                    if !super::closed_templates::charge_term(term, pay) {
                        return Vec::new();
                    }
                }
                if !vocabulary.ground(registry, term, pay) {
                    continue;
                }
                let mut extended = binding.clone();
                if matches(
                    pattern.term(),
                    term,
                    &mut extended,
                    vars,
                    vocabulary,
                    registry,
                    pay,
                ) {
                    let mut conditions = conds.clone();
                    conditions.push(cond.clone());
                    next.push((extended, conditions));
                }
            }
        }
        partial = next;
    }
    let mut out = Vec::new();
    for (binding, conditions) in partial {
        let mut values = Vec::new();
        let mut complete = true;
        for (i, sort) in vars.iter().enumerate() {
            if !pay(32) {
                complete = false;
                break;
            }
            let Some(term) = binding.get(&var_name(i)) else {
                complete = false;
                break;
            };
            if term.sort() != *sort || !super::closed_templates::charge_term(term, pay) {
                complete = false;
                break;
            }
            values.push(term.clone());
        }
        if complete {
            out.push((values, conditions));
        }
    }
    out
}

/// The shape of a choice for identity (`air/src/closure.rs`): the
/// expression with its holes, the maximal subexpressions that mention no
/// local bound inside it, left out, and the locals bound inside numbered in
/// order. The holes in order.
pub(crate) fn choose_shape(e: &Expr) -> (String, Vec<&Expr>) {
    let mut inner: HashSet<LocalId> = HashSet::new();
    collect_bound(e, &mut inner);
    let mut state = Shaper {
        inner,
        numbers: HashMap::new(),
        holes: Vec::new(),
        out: String::new(),
    };
    state.top(e);
    (state.out, state.holes)
}

/// Every local bound by `e` or inside it.
fn collect_bound(e: &Expr, out: &mut HashSet<LocalId>) {
    match &e.kind {
        ExprKind::Let { local, .. } => {
            out.insert(*local);
        }
        ExprKind::Quant { vars, .. }
        | ExprKind::Choose { vars, .. }
        | ExprKind::UntriggeredQuant { vars, .. }
        | ExprKind::UntriggeredChoose { vars, .. } => {
            out.extend(vars.iter().map(|(var, _)| *var));
        }
        _ => {}
    }
    e.for_each_child(&mut |child| collect_bound(child, out));
}

struct Shaper<'e> {
    inner: HashSet<LocalId>,
    numbers: HashMap<LocalId, usize>,
    holes: Vec<&'e Expr>,
    out: String,
}

impl<'e> Shaper<'e> {
    fn number(&mut self, local: LocalId) -> usize {
        let next = self.numbers.len();
        *self.numbers.entry(local).or_insert(next)
    }

    fn closed(&self, e: &Expr) -> bool {
        !e.any(&|sub| match &sub.kind {
            ExprKind::Read(place) | ExprKind::Old(place) => self.inner.contains(&place.local),
            ExprKind::Let { .. }
            | ExprKind::Quant { .. }
            | ExprKind::Choose { .. }
            | ExprKind::UntriggeredQuant { .. }
            | ExprKind::UntriggeredChoose { .. } => true,
            _ => false,
        })
    }

    fn top(&mut self, e: &'e Expr) {
        let ExprKind::Choose {
            vars,
            triggers,
            cond,
            result,
        } = &e.kind
        else {
            self.expr(e);
            return;
        };
        let _ = write!(self.out, "choose[{:?}](", e.ty);
        for (var, ty) in vars {
            let n = self.number(*var);
            let _ = write!(self.out, "b{n}:{ty:?},");
        }
        self.out.push_str(")(");
        self.expr(cond);
        self.out.push_str(")(");
        self.expr(result);
        self.out.push_str(")(");
        for group in triggers {
            self.out.push('[');
            for term in group {
                self.expr(term);
                self.out.push(',');
            }
            self.out.push(']');
        }
        self.out.push(')');
    }

    fn expr(&mut self, e: &'e Expr) {
        if self.closed(e) {
            let _ = write!(self.out, "H{}:{:?}", self.holes.len(), e.ty);
            self.holes.push(e);
            return;
        }
        let ty = &e.ty;
        match &e.kind {
            ExprKind::IntegerConstant(value) => {
                let _ = write!(self.out, "integer_constant({value:?}):{ty:?}");
            }
            ExprKind::Lit(lit) => {
                let lit: &Lit = lit;
                let _ = write!(self.out, "lit({lit:?}):{ty:?}");
            }
            ExprKind::Read(place) | ExprKind::Old(place) => {
                let old = matches!(e.kind, ExprKind::Old(_));
                let n = self.number(place.local);
                let _ = write!(
                    self.out,
                    "{}b{n}{:?}:{ty:?}",
                    if old { "old" } else { "" },
                    place.projections
                );
            }
            ExprKind::Let { local, .. } => {
                let n = self.number(*local);
                let _ = write!(self.out, "let b{n}:{ty:?}(");
                self.children(e);
                self.out.push(')');
            }
            ExprKind::Quant { kind, vars, .. } => {
                let _ = write!(self.out, "{kind:?}(");
                for (var, var_ty) in vars {
                    let n = self.number(*var);
                    let _ = write!(self.out, "b{n}:{var_ty:?},");
                }
                self.out.push_str(")(");
                self.children(e);
                self.out.push(')');
            }
            ExprKind::Choose { vars, .. } => {
                let _ = write!(self.out, "choose:{ty:?}(");
                for (var, var_ty) in vars {
                    let n = self.number(*var);
                    let _ = write!(self.out, "b{n}:{var_ty:?},");
                }
                self.out.push_str(")(");
                self.children(e);
                self.out.push(')');
            }
            other => {
                let _ = write!(self.out, "{}:{ty:?}(", node_label(other));
                self.children(e);
                self.out.push(')');
            }
        }
    }

    fn children(&mut self, e: &'e Expr) {
        let mut kids: Vec<&'e Expr> = Vec::new();
        e.for_each_child(&mut |child| kids.push(child));
        for (i, child) in kids.into_iter().enumerate() {
            if i > 0 {
                self.out.push(',');
            }
            self.expr(child);
        }
    }
}

/// The node of `kind` without its subexpressions, for shapes.
fn node_label(kind: &ExprKind) -> String {
    match kind {
        ExprKind::Unary { op, check, .. } => format!("un{op:?}{check:?}"),
        ExprKind::Binary { op, check, .. } => format!("bin{op:?}{check:?}"),
        ExprKind::If { .. } => "if".to_string(),
        ExprKind::Call {
            callee, type_args, ..
        } => format!("call{callee:?}{type_args:?}"),
        ExprKind::Cast { kind, .. } => format!("cast{kind:?}"),
        ExprKind::Ctor { adt, variant, .. } => format!("ctor{adt:?}#{variant}"),
        ExprKind::IsVariant { variant, .. } => format!("variant-test{variant}"),
        ExprKind::Tuple(_) => "tuple".to_string(),
        ExprKind::Field { variant, field, .. } => format!("field{variant}:{field}"),
        ExprKind::TupleField { index, .. } => format!("tfield{index}"),
        ExprKind::Borrow(_) => "borrow".to_string(),
        ExprKind::ProofInSpec(_) => "proof".to_string(),
        ExprKind::IntegerConstant(value) => format!("integer_constant({value:?})"),
        ExprKind::UntriggeredQuant { .. } => "untriggered-quant".into(),
        ExprKind::UntriggeredChoose { .. } => "untriggered-choose".into(),
        ExprKind::Lit(_)
        | ExprKind::Read(_)
        | ExprKind::Old(_)
        | ExprKind::Let { .. }
        | ExprKind::Quant { .. }
        | ExprKind::Choose { .. } => String::new(),
    }
}

#[cfg(test)]
#[path = "quant_typed_tests.rs"]
mod typed_tests;

#[cfg(test)]
#[path = "quant_arithmetic_tests.rs"]
mod arithmetic_tests;
