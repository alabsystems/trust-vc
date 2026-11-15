// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Random TLA+ integer and Boolean expressions over `x, y, b`, named integer
//! locals, module operators with parameters, LET and ENABLED: a generator, an
//! evaluator independent of ty, a printer, and the free locals of each.

use std::collections::BTreeSet;

/// splitmix64: a fixed seed gives a fixed sequence of cases on every host.
pub struct Rng(pub u64);

impl Rng {
    pub fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    pub fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    pub fn range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + self.below((hi - lo + 1) as u64) as i64
    }
    pub fn chance(&mut self, num: u64, den: u64) -> bool {
        self.below(den) < num
    }
    pub fn pick<T: Copy>(&mut self, items: &[T]) -> T {
        items[self.below(items.len() as u64) as usize]
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct St {
    pub x: i64,
    pub y: i64,
    pub b: bool,
    /// `c \subseteq 0..3`, bit `v` for member `v`. No expression reads it:
    /// it is drawn from set filters (`c' \in F`), and the invariants name it.
    pub c: u8,
}

/// The largest member of `c`: its filters are over `SUBSET (lo..hi)` with
/// `0 <= lo <= hi <= C_MAX`.
pub const C_MAX: i64 = 3;

/// The TLA+ set of the members `mask` holds, ascending.
pub fn pr_set(mask: u8) -> String {
    let members: Vec<String> = (0..=C_MAX)
        .filter(|v| mask & (1 << v) != 0)
        .map(|v| v.to_string())
        .collect();
    format!("{{{}}}", members.join(", "))
}

pub type Name = &'static str;

/// The names a binder may take. Operator parameters, quantifiers and LET
/// definitions all draw from it, so a caller's binder often has the name of
/// a parameter of the operator it calls.
pub const NAMES: [Name; 4] = ["k", "v", "w", "u"];

#[derive(Clone, Debug)]
pub enum IE {
    X,
    Y,
    Xp,
    Yp,
    Local(Name),
    C(i64),
    Add(Box<IE>, Box<IE>),
    Sub(Box<IE>, Box<IE>),
    Mul(Box<IE>, Box<IE>),
    Div(Box<IE>, i64),
    Mod(Box<IE>, i64),
    Neg(Box<IE>),
    Ite(Box<BE>, Box<IE>, Box<IE>),
    /// `H<j>(args)`.
    Call(usize, Vec<IE>),
    /// `LET name == def IN body`.
    Let(Name, Box<IE>, Box<IE>),
}

#[derive(Clone, Debug)]
pub enum BE {
    B,
    Bp,
    T,
    F,
    Lt(IE, IE),
    Le(IE, IE),
    Eq(IE, IE),
    Ne(IE, IE),
    Not(Box<BE>),
    And(Box<BE>, Box<BE>),
    Or(Box<BE>, Box<BE>),
    Imp(Box<BE>, Box<BE>),
    Iff(Box<BE>, Box<BE>),
    /// `\E name \in lo..hi : body`.
    Ex(Name, i64, i64, Box<BE>),
    In(IE, Vec<IE>),
    /// `ENABLED A<i>`.
    Enabled(usize),
}

/// `H<j>(params) == body`: integer-valued, reading its parameters, constants,
/// `x`, `y` and lower-numbered helpers.
#[derive(Clone, Debug)]
pub struct Helper {
    pub params: Vec<Name>,
    pub body: IE,
}

/// What evaluation needs beyond the state: the helpers, and which actions
/// are enabled in a state.
pub struct Ctx<'a> {
    pub helpers: &'a [Helper],
    pub enabled: &'a dyn Fn(usize, St) -> bool,
}

/// The state, the successor when the expression is an action's, and the
/// locals in scope, innermost last.
pub struct Env {
    pub s: St,
    pub t: Option<St>,
    pub locals: Vec<(Name, i64)>,
}

impl Env {
    pub fn state(s: St) -> Self {
        Env {
            s,
            t: None,
            locals: Vec::new(),
        }
    }
    fn local(&self, name: Name) -> i64 {
        let found = self.locals.iter().rev().find(|(bound, _)| *bound == name);
        found
            .map(|(_, value)| *value)
            .expect("the generator binds every local it reads")
    }
    fn with<T>(&mut self, name: Name, value: i64, f: impl FnOnce(&mut Env) -> T) -> T {
        self.locals.push((name, value));
        let out = f(self);
        self.locals.pop();
        out
    }
}

pub fn ev_i(e: &IE, cx: &Ctx, env: &mut Env) -> i64 {
    match e {
        IE::X => env.s.x,
        IE::Y => env.s.y,
        IE::Xp => env.t.expect("a primed read in an action").x,
        IE::Yp => env.t.expect("a primed read in an action").y,
        IE::Local(name) => env.local(name),
        IE::C(c) => *c,
        IE::Add(a, b) => ev_i(a, cx, env) + ev_i(b, cx, env),
        IE::Sub(a, b) => ev_i(a, cx, env) - ev_i(b, cx, env),
        IE::Mul(a, b) => ev_i(a, cx, env) * ev_i(b, cx, env),
        // TLA+ `\div` is floor division and `%` is in 0..k-1 for k > 0.
        IE::Div(a, k) => ev_i(a, cx, env).div_euclid(*k),
        IE::Mod(a, k) => ev_i(a, cx, env).rem_euclid(*k),
        IE::Neg(a) => -ev_i(a, cx, env),
        IE::Ite(c, a, b) => {
            if ev_b(c, cx, env) {
                ev_i(a, cx, env)
            } else {
                ev_i(b, cx, env)
            }
        }
        IE::Call(j, args) => {
            let helper = &cx.helpers[*j];
            let values: Vec<i64> = args.iter().map(|arg| ev_i(arg, cx, env)).collect();
            let mut inner = Env {
                s: env.s,
                t: env.t,
                locals: helper.params.iter().copied().zip(values).collect(),
            };
            ev_i(&helper.body, cx, &mut inner)
        }
        IE::Let(name, def, body) => {
            let value = ev_i(def, cx, env);
            env.with(name, value, |env| ev_i(body, cx, env))
        }
    }
}

pub fn ev_b(e: &BE, cx: &Ctx, env: &mut Env) -> bool {
    match e {
        BE::B => env.s.b,
        BE::Bp => env.t.expect("a primed read in an action").b,
        BE::T => true,
        BE::F => false,
        BE::Lt(a, b) => ev_i(a, cx, env) < ev_i(b, cx, env),
        BE::Le(a, b) => ev_i(a, cx, env) <= ev_i(b, cx, env),
        BE::Eq(a, b) => ev_i(a, cx, env) == ev_i(b, cx, env),
        BE::Ne(a, b) => ev_i(a, cx, env) != ev_i(b, cx, env),
        BE::Not(p) => !ev_b(p, cx, env),
        BE::And(p, q) => ev_b(p, cx, env) && ev_b(q, cx, env),
        BE::Or(p, q) => ev_b(p, cx, env) || ev_b(q, cx, env),
        BE::Imp(p, q) => !ev_b(p, cx, env) || ev_b(q, cx, env),
        BE::Iff(p, q) => ev_b(p, cx, env) == ev_b(q, cx, env),
        BE::Ex(name, lo, hi, p) => (*lo..=*hi).any(|v| env.with(name, v, |env| ev_b(p, cx, env))),
        BE::In(e, set) => {
            let value = ev_i(e, cx, env);
            set.iter().any(|m| ev_i(m, cx, env) == value)
        }
        BE::Enabled(i) => (cx.enabled)(*i, env.s),
    }
}

pub fn int(c: i64) -> String {
    if c < 0 {
        format!("(-{})", -c)
    } else {
        c.to_string()
    }
}

pub fn pr_i(e: &IE) -> String {
    match e {
        IE::X => "x".into(),
        IE::Y => "y".into(),
        IE::Xp => "x'".into(),
        IE::Yp => "y'".into(),
        IE::Local(name) => (*name).into(),
        IE::C(c) => int(*c),
        IE::Add(a, b) => format!("({} + {})", pr_i(a), pr_i(b)),
        IE::Sub(a, b) => format!("({} - {})", pr_i(a), pr_i(b)),
        IE::Mul(a, b) => format!("({} * {})", pr_i(a), pr_i(b)),
        IE::Div(a, k) => format!("({} \\div {k})", pr_i(a)),
        IE::Mod(a, k) => format!("({} % {k})", pr_i(a)),
        IE::Neg(a) => format!("(-{})", pr_i(a)),
        IE::Ite(c, a, b) => format!("(IF {} THEN {} ELSE {})", pr_b(c), pr_i(a), pr_i(b)),
        IE::Call(j, args) => {
            let args: Vec<String> = args.iter().map(pr_i).collect();
            format!("H{j}({})", args.join(", "))
        }
        IE::Let(name, def, body) => format!("(LET {name} == {} IN {})", pr_i(def), pr_i(body)),
    }
}

pub fn pr_b(e: &BE) -> String {
    match e {
        BE::B => "b".into(),
        BE::Bp => "b'".into(),
        BE::T => "TRUE".into(),
        BE::F => "FALSE".into(),
        BE::Lt(a, b) => format!("({} < {})", pr_i(a), pr_i(b)),
        BE::Le(a, b) => format!("({} <= {})", pr_i(a), pr_i(b)),
        BE::Eq(a, b) => format!("({} = {})", pr_i(a), pr_i(b)),
        BE::Ne(a, b) => format!("({} # {})", pr_i(a), pr_i(b)),
        BE::Not(p) => format!("(~{})", pr_b(p)),
        BE::And(p, q) => format!("({} /\\ {})", pr_b(p), pr_b(q)),
        BE::Or(p, q) => format!("({} \\/ {})", pr_b(p), pr_b(q)),
        BE::Imp(p, q) => format!("({} => {})", pr_b(p), pr_b(q)),
        BE::Iff(p, q) => format!("({} <=> {})", pr_b(p), pr_b(q)),
        BE::Ex(name, lo, hi, p) => {
            format!("(\\E {name} \\in {}..{} : {})", int(*lo), int(*hi), pr_b(p))
        }
        BE::In(e, set) => {
            let members: Vec<String> = set.iter().map(pr_i).collect();
            format!("({} \\in {{{}}})", pr_i(e), members.join(", "))
        }
        BE::Enabled(i) => format!("(ENABLED A{i})"),
    }
}

/// The locals `e` reads that it does not bind itself.
pub fn free_i(e: &IE, bound: &mut Vec<Name>, out: &mut BTreeSet<Name>) {
    match e {
        IE::X | IE::Y | IE::Xp | IE::Yp | IE::C(_) => {}
        IE::Local(name) => {
            if !bound.contains(name) {
                out.insert(name);
            }
        }
        IE::Add(a, b) | IE::Sub(a, b) | IE::Mul(a, b) => {
            free_i(a, bound, out);
            free_i(b, bound, out);
        }
        IE::Div(a, _) | IE::Mod(a, _) | IE::Neg(a) => free_i(a, bound, out),
        IE::Ite(c, a, b) => {
            free_b(c, bound, out);
            free_i(a, bound, out);
            free_i(b, bound, out);
        }
        IE::Call(_, args) => args.iter().for_each(|arg| free_i(arg, bound, out)),
        IE::Let(name, def, body) => {
            free_i(def, bound, out);
            bound.push(name);
            free_i(body, bound, out);
            bound.pop();
        }
    }
}

pub fn free_b(e: &BE, bound: &mut Vec<Name>, out: &mut BTreeSet<Name>) {
    match e {
        BE::B | BE::Bp | BE::T | BE::F | BE::Enabled(_) => {}
        BE::Lt(a, b) | BE::Le(a, b) | BE::Eq(a, b) | BE::Ne(a, b) => {
            free_i(a, bound, out);
            free_i(b, bound, out);
        }
        BE::Not(p) => free_b(p, bound, out),
        BE::And(p, q) | BE::Or(p, q) | BE::Imp(p, q) | BE::Iff(p, q) => {
            free_b(p, bound, out);
            free_b(q, bound, out);
        }
        BE::Ex(name, _, _, p) => {
            bound.push(name);
            free_b(p, bound, out);
            bound.pop();
        }
        BE::In(e, set) => {
            free_i(e, bound, out);
            set.iter().for_each(|m| free_i(m, bound, out));
        }
    }
}
