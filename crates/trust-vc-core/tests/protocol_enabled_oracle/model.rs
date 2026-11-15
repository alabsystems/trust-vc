// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The independent semantic model: TLA+'s meaning of the generated fragment,
//! evaluated by brute force. It shares no code with TY.
//!
//! * An expression is evaluated over a pair of states `<<s, t>>` (`t` absent
//!   for a state predicate) in a lookup mode: unprimed, or under a prime. A
//!   state variable reads `s` unprimed and `t` under a prime; priming an
//!   expression primes every state variable it reads, through definitions
//!   and operator arguments too (TLA+ definitions are expanded, so `S'` with
//!   `S == {s \in T : x \in s}` is `{s \in T' : x' \in s}`).
//! * A bound variable (quantifier, filter binder, tuple-pattern component) is
//!   a VALUE fixed where it is bound.
//! * A definition (module or LET, any arity) and an operator argument are
//!   EXPANDED where they are referenced: their body is evaluated in the
//!   lexical scope it was written in, under the pair and the lookup mode of
//!   the reference. That is TLA+'s substitution semantics, and it is what
//!   TLC does inside ENABLED (every `LazyValue` re-evaluated at each
//!   reference). A LET definition is therefore lazy, in its definition's
//!   scope.
//! * `ENABLED A` holds in `s` iff some state `u` of the universe makes `A`
//!   true for `<<s, u>>`. The universe is every state with `x \in 0..3`,
//!   `y \in SUBSET (1..3)`, `z \in (1..2) \X (1..2)`, and every ENABLED
//!   operand the generator writes ends with exactly those three
//!   memberships primed ([`super::ast::type_ok_primed`]), so a successor the
//!   operand admits is in the universe and the brute force is exactly TLA+'s
//!   existential over all states. The outer pair plays no part: ENABLED
//!   binds its own successor (an action's `x' = 1` is invisible inside a
//!   `~ENABLED B` conjunct of that action), while a definition or argument
//!   written outside and referenced inside ENABLED reads ENABLED's successor
//!   (expansion), and a value bound outside stays that value.

use super::ast::{Def, Pat, St, Var, E, V, VARS};
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OErr {
    /// The generator wrote something outside the fragment's well-formed
    /// modules (a double prime, a prime in a state predicate, a type
    /// error). Never TY's fault; a generated case that raises this is a
    /// generator defect.
    IllFormed(String),
}

fn ill<T>(msg: impl Into<String>) -> Result<T, OErr> {
    Err(OErr::IllFormed(msg.into()))
}

#[derive(Clone)]
enum Bind {
    Val(V),
    /// An operator argument: the actual and the caller's scope.
    Thunk(Rc<E>, Env),
    /// A definition and the scope it was written in.
    Def(Rc<Def>, Env),
    /// An operator parameter bound to an operator (a definition or a
    /// `LAMBDA`) and the scope it was written in.
    Op(Rc<Def>, Env),
}

struct Node {
    name: String,
    bind: Bind,
    next: Env,
}

#[derive(Clone, Default)]
pub struct Env(Option<Rc<Node>>);

impl Env {
    fn push(&self, name: &str, bind: Bind) -> Env {
        Env(Some(Rc::new(Node {
            name: name.to_string(),
            bind,
            next: self.clone(),
        })))
    }

    fn lookup(&self, name: &str) -> Option<&Bind> {
        let mut cur = &self.0;
        while let Some(node) = cur {
            if node.name == name {
                return Some(&node.bind);
            }
            cur = &node.next.0;
        }
        None
    }
}

/// Module-level definitions.
pub struct Globals {
    defs: HashMap<String, Rc<Def>>,
}

impl Globals {
    pub fn new(defs: &[Def]) -> Self {
        Globals {
            defs: defs
                .iter()
                .map(|d| (d.name.clone(), Rc::new(d.clone())))
                .collect(),
        }
    }
}

#[derive(Clone, Copy)]
struct Cx<'a> {
    s: &'a St,
    t: Option<&'a St>,
    primed: bool,
    g: &'a Globals,
    universe: &'a [St],
}

/// Every state of the universe, in a fixed order.
pub fn universe() -> Vec<St> {
    let mut out = Vec::new();
    let subsets: Vec<V> = (0..8u32)
        .map(|mask| {
            V::Set(
                (1..=3)
                    .filter(|i| mask & (1 << (i - 1)) != 0)
                    .map(V::Int)
                    .collect(),
            )
        })
        .collect();
    for xv in 0..=3 {
        for yv in &subsets {
            for a in 1..=2 {
                for c in 1..=2 {
                    out.push([V::Int(xv), yv.clone(), V::Tup(vec![V::Int(a), V::Int(c)])]);
                }
            }
        }
    }
    out
}

/// The model of one module.
pub struct Model<'a> {
    g: Globals,
    universe: &'a [St],
}

impl<'a> Model<'a> {
    pub fn new(defs: &[Def], universe: &'a [St]) -> Self {
        Model {
            g: Globals::new(defs),
            universe,
        }
    }

    fn cx<'b>(&'b self, s: &'b St, t: Option<&'b St>) -> Cx<'b> {
        Cx {
            s,
            t,
            primed: false,
            g: &self.g,
            universe: self.universe,
        }
    }

    /// A state predicate in `s`.
    pub fn holds_in(&self, e: &E, s: &St) -> Result<bool, OErr> {
        as_bool(eval(e, &Env::default(), self.cx(s, None))?)
    }

    /// An action on `<<s, t>>`.
    pub fn holds_on(&self, e: &E, s: &St, t: &St) -> Result<bool, OErr> {
        as_bool(eval(e, &Env::default(), self.cx(s, Some(t)))?)
    }

    /// `{t \in universe : next(s, t)}`.
    pub fn successors(&self, next: &E, s: &St) -> Result<Vec<St>, OErr> {
        let mut out = Vec::new();
        for t in self.universe {
            if self.holds_on(next, s, t)? {
                out.push(t.clone());
            }
        }
        Ok(out)
    }
}

/// The reachable states from `init` under `next` (breadth first) and
/// whether `inv` holds in every one of them.
pub struct Exploration {
    pub reachable: Vec<St>,
    pub violating: Vec<St>,
}

pub fn explore(model: &Model<'_>, init: &St, next: &E, inv: &E) -> Result<Exploration, OErr> {
    let mut seen: BTreeSet<St> = BTreeSet::new();
    let mut order = Vec::new();
    let mut queue = std::collections::VecDeque::new();
    seen.insert(init.clone());
    queue.push_back(init.clone());
    while let Some(s) = queue.pop_front() {
        order.push(s.clone());
        for t in model.successors(next, &s)? {
            if seen.insert(t.clone()) {
                queue.push_back(t);
            }
        }
    }
    let mut violating = Vec::new();
    for s in &order {
        if !model.holds_in(inv, s)? {
            violating.push(s.clone());
        }
    }
    Ok(Exploration {
        reachable: order,
        violating,
    })
}

fn as_bool(v: V) -> Result<bool, OErr> {
    match v {
        V::Bool(b) => Ok(b),
        other => ill(format!("expected a Boolean, got {other:?}")),
    }
}

fn as_int(v: V) -> Result<i64, OErr> {
    match v {
        V::Int(i) => Ok(i),
        other => ill(format!("expected an integer, got {other:?}")),
    }
}

fn as_set(v: V) -> Result<BTreeSet<V>, OErr> {
    match v {
        V::Set(s) => Ok(s),
        other => ill(format!("expected a set, got {other:?}")),
    }
}

fn read_var(v: Var, cx: Cx<'_>) -> Result<V, OErr> {
    if cx.primed {
        match cx.t {
            Some(t) => Ok(t[v.index()].clone()),
            None => ill(format!("{}' in a state predicate", v.name())),
        }
    } else {
        Ok(cx.s[v.index()].clone())
    }
}

fn bind_pat(env: &Env, p: &Pat, v: &V) -> Result<Env, OErr> {
    match p {
        Pat::One(n) => Ok(env.push(n, Bind::Val(v.clone()))),
        Pat::Tup(ns) => match v {
            V::Tup(items) if items.len() == ns.len() => {
                let mut env = env.clone();
                for (n, item) in ns.iter().zip(items) {
                    env = env.push(n, Bind::Val(item.clone()));
                }
                Ok(env)
            }
            other => ill(format!("tuple pattern over {other:?}")),
        },
    }
}

fn bind_defs(env: &Env, defs: &[Def]) -> Env {
    let mut env = env.clone();
    for d in defs {
        // A LET definition sees its predecessors (no RECURSIVE here).
        let scope = env.clone();
        env = env.push(&d.name, Bind::Def(Rc::new(d.clone()), scope));
    }
    env
}

fn eval(e: &E, env: &Env, cx: Cx<'_>) -> Result<V, OErr> {
    match e {
        E::Int(i) => Ok(V::Int(*i)),
        E::Bool(b) => Ok(V::Bool(*b)),
        E::Var(v) => read_var(*v, cx),
        E::Prime(inner) => {
            if cx.primed {
                return ill("double prime");
            }
            if cx.t.is_none() {
                return ill("prime in a state predicate");
            }
            eval(inner, env, Cx { primed: true, ..cx })
        }
        E::Name(n) => match env.lookup(n) {
            Some(Bind::Val(v)) => Ok(v.clone()),
            Some(Bind::Thunk(actual, scope)) => eval(actual, scope, cx),
            Some(Bind::Def(d, scope)) => {
                if !d.params.is_empty() {
                    return ill(format!("{n} used without arguments"));
                }
                eval(&d.body, scope, cx)
            }
            Some(Bind::Op(..)) => ill(format!("operator {n} used as a value")),
            None => match cx.g.defs.get(n) {
                Some(d) if d.params.is_empty() => eval(&d.body, &Env::default(), cx),
                _ => ill(format!("undefined {n}")),
            },
        },
        E::Apply(op, args) => {
            let (d, scope) = resolve_operator(op, env, cx)?;
            if d.params.len() != args.len() {
                return ill(format!("arity of {op}"));
            }
            let mut inner = scope;
            for (i, (p, a)) in d.params.iter().zip(args).enumerate() {
                let bind = if d.arity(i) > 0 {
                    // An operator argument: a LAMBDA, or an operator's name.
                    let (od, oscope) = match a {
                        E::Lambda(ps, body) => (
                            Rc::new(Def {
                                name: "LAMBDA".into(),
                                params: ps.clone(),
                                arities: Vec::new(),
                                body: (**body).clone(),
                            }),
                            env.clone(),
                        ),
                        E::Name(n) => resolve_operator(n, env, cx)?,
                        other => return ill(format!("operator argument {other:?}")),
                    };
                    if od.params.len() != d.arity(i) {
                        return ill(format!("arity of the operator argument of {op}"));
                    }
                    Bind::Op(od, oscope)
                } else {
                    Bind::Thunk(Rc::new(a.clone()), env.clone())
                };
                inner = inner.push(p, bind);
            }
            eval(&d.body, &inner, cx)
        }
        E::Add(a, c) => Ok(V::Int(
            as_int(eval(a, env, cx)?)? + as_int(eval(c, env, cx)?)?,
        )),
        E::Mod(a, m) => Ok(V::Int(as_int(eval(a, env, cx)?)?.rem_euclid(*m))),
        E::Card(s) => Ok(V::Int(as_set(eval(s, env, cx)?)?.len() as i64)),
        E::Index(t, i) => match eval(t, env, cx)? {
            V::Tup(items) if *i >= 1 && (*i as usize) <= items.len() => {
                Ok(items[*i as usize - 1].clone())
            }
            other => ill(format!("index {i} of {other:?}")),
        },
        E::Tuple(es) => Ok(V::Tup(
            es.iter()
                .map(|e| eval(e, env, cx))
                .collect::<Result<_, _>>()?,
        )),
        E::SetEnum(es) => Ok(V::Set(
            es.iter()
                .map(|e| eval(e, env, cx))
                .collect::<Result<_, _>>()?,
        )),
        E::Range(lo, hi) => Ok(V::Set((*lo..=*hi).map(V::Int).collect())),
        E::Cup(a, c) => {
            let mut s = as_set(eval(a, env, cx)?)?;
            s.extend(as_set(eval(c, env, cx)?)?);
            Ok(V::Set(s))
        }
        E::Cap(a, c) => {
            let s = as_set(eval(a, env, cx)?)?;
            let t = as_set(eval(c, env, cx)?)?;
            Ok(V::Set(s.intersection(&t).cloned().collect()))
        }
        E::Diff(a, c) => {
            let s = as_set(eval(a, env, cx)?)?;
            let t = as_set(eval(c, env, cx)?)?;
            Ok(V::Set(s.difference(&t).cloned().collect()))
        }
        E::Subset(s) => {
            let items: Vec<V> = as_set(eval(s, env, cx)?)?.into_iter().collect();
            if items.len() > 12 {
                return ill("SUBSET of a large set");
            }
            let mut out = BTreeSet::new();
            for mask in 0..(1u32 << items.len()) {
                out.insert(V::Set(
                    items
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| mask & (1 << i) != 0)
                        .map(|(_, v)| v.clone())
                        .collect(),
                ));
            }
            Ok(V::Set(out))
        }
        E::Times(a, c) => {
            let s = as_set(eval(a, env, cx)?)?;
            let t = as_set(eval(c, env, cx)?)?;
            let mut out = BTreeSet::new();
            for l in &s {
                for r in &t {
                    out.insert(V::Tup(vec![l.clone(), r.clone()]));
                }
            }
            Ok(V::Set(out))
        }
        E::Filter(p, s, pred) => {
            let mut out = BTreeSet::new();
            for member in as_set(eval(s, env, cx)?)? {
                let inner = bind_pat(env, p, &member)?;
                if as_bool(eval(pred, &inner, cx)?)? {
                    out.insert(member);
                }
            }
            Ok(V::Set(out))
        }
        E::Eq(a, c) => Ok(V::Bool(eval(a, env, cx)? == eval(c, env, cx)?)),
        E::Lt(a, c) => Ok(V::Bool(
            as_int(eval(a, env, cx)?)? < as_int(eval(c, env, cx)?)?,
        )),
        E::In(a, c) => {
            let v = eval(a, env, cx)?;
            Ok(V::Bool(as_set(eval(c, env, cx)?)?.contains(&v)))
        }
        E::NotIn(a, c) => {
            let v = eval(a, env, cx)?;
            Ok(V::Bool(!as_set(eval(c, env, cx)?)?.contains(&v)))
        }
        E::Subseteq(a, c) => {
            let s = as_set(eval(a, env, cx)?)?;
            let t = as_set(eval(c, env, cx)?)?;
            Ok(V::Bool(s.is_subset(&t)))
        }
        E::Not(a) => Ok(V::Bool(!as_bool(eval(a, env, cx)?)?)),
        E::And(es) => {
            for e in es {
                if !as_bool(eval(e, env, cx)?)? {
                    return Ok(V::Bool(false));
                }
            }
            Ok(V::Bool(true))
        }
        E::Or(es) => {
            for e in es {
                if as_bool(eval(e, env, cx)?)? {
                    return Ok(V::Bool(true));
                }
            }
            Ok(V::Bool(false))
        }
        E::If(c, t, f) => {
            if as_bool(eval(c, env, cx)?)? {
                eval(t, env, cx)
            } else {
                eval(f, env, cx)
            }
        }
        E::Exists(p, s, body) => {
            for member in as_set(eval(s, env, cx)?)? {
                let inner = bind_pat(env, p, &member)?;
                if as_bool(eval(body, &inner, cx)?)? {
                    return Ok(V::Bool(true));
                }
            }
            Ok(V::Bool(false))
        }
        E::Forall(p, s, body) => {
            for member in as_set(eval(s, env, cx)?)? {
                let inner = bind_pat(env, p, &member)?;
                if !as_bool(eval(body, &inner, cx)?)? {
                    return Ok(V::Bool(false));
                }
            }
            Ok(V::Bool(true))
        }
        E::Let(defs, body) => eval(body, &bind_defs(env, defs), cx),
        E::Enabled(a) => {
            if cx.primed {
                return ill("ENABLED under a prime");
            }
            for u in cx.universe {
                let inner = Cx {
                    s: cx.s,
                    t: Some(u),
                    primed: false,
                    ..cx
                };
                if as_bool(eval(a, env, inner)?)? {
                    return Ok(V::Bool(true));
                }
            }
            Ok(V::Bool(false))
        }
        E::Unchanged(v) => {
            if cx.primed {
                return ill("UNCHANGED under a prime");
            }
            match cx.t {
                Some(t) => Ok(V::Bool(t[v.index()] == cx.s[v.index()])),
                None => ill("UNCHANGED in a state predicate"),
            }
        }
        // `UNCHANGED e` is `e' = e`.
        E::UnchangedE(inner) => {
            if cx.primed {
                return ill("UNCHANGED under a prime");
            }
            if cx.t.is_none() {
                return ill("UNCHANGED in a state predicate");
            }
            let after = eval(inner, env, Cx { primed: true, ..cx })?;
            Ok(V::Bool(after == eval(inner, env, cx)?))
        }
        // `<<A>>_e` is `A /\ ~(e' = e)`.
        E::AngleAction(a, sub) => {
            if cx.primed {
                return ill("<<A>>_e under a prime");
            }
            if cx.t.is_none() {
                return ill("<<A>>_e in a state predicate");
            }
            if !as_bool(eval(a, env, cx)?)? {
                return Ok(V::Bool(false));
            }
            let after = eval(sub, env, Cx { primed: true, ..cx })?;
            Ok(V::Bool(after != eval(sub, env, cx)?))
        }
        E::Lambda(..) => ill("LAMBDA as a value"),
    }
}

/// The operator `op` names here: a definition (LET or module), or an
/// operator parameter's operator.
fn resolve_operator(op: &str, env: &Env, cx: Cx<'_>) -> Result<(Rc<Def>, Env), OErr> {
    match env.lookup(op) {
        Some(Bind::Def(d, scope)) | Some(Bind::Op(d, scope)) => Ok((Rc::clone(d), scope.clone())),
        Some(_) => ill(format!("{op} is not an operator")),
        None => match cx.g.defs.get(op) {
            Some(d) => Ok((Rc::clone(d), Env::default())),
            None => ill(format!("undefined operator {op}")),
        },
    }
}

/// Whether a state of the universe is `s` (the universe has every value of
/// each variable's type, so this only checks the shape).
pub fn in_universe(s: &St) -> bool {
    let x_ok = matches!(&s[0], V::Int(i) if (0..=3).contains(i));
    let y_ok = matches!(&s[1], V::Set(items)
        if items.iter().all(|v| matches!(v, V::Int(i) if (1..=3).contains(i))));
    let z_ok = matches!(&s[2], V::Tup(items) if items.len() == 2
        && items.iter().all(|v| matches!(v, V::Int(i) if (1..=2).contains(i))));
    x_ok && y_ok && z_ok && VARS.len() == 3
}
