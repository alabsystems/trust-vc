// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Seeded generator of well-formed modules over the fragment.
//!
//! Every generated module is SANY-well-formed by construction: a binder or
//! definition never reuses a name visible where it is introduced, a prime is
//! applied only to a state-level expression (a parameter the body primes
//! takes only state-level actuals), and ENABLED never appears under a prime.
//! Every value assigned to a primed variable lies in that variable's
//! universe (integer expressions are reduced `% 4`, sets are subsets of
//! `1..3`, pairs are drawn from `(1..2) \X (1..2)`), and every ENABLED
//! operand ends with the primed type memberships, so the model's brute
//! force is exact.
//!
//! The shapes the ENABLED review named are all reachable, in every
//! conjunct order: a prime read before the witness assigns it (directly, in
//! a set filter, in an operator argument, through a primed operator
//! application or a primed LET definition), `~ENABLED` / `ENABLED` as a
//! conjunct of `Next` before or after `Next`'s own assignments, LET-bound
//! filters (built before the primes they read are assigned, referenced
//! after), tuple-pattern filters and quantifiers inside other binders,
//! operator parameters whose name a caller binder reuses (captured locals),
//! operators that prime a parameter (`A(S) == y' \in S'`), and LET
//! operators that capture an enclosing binder.

use super::ast::*;

/// splitmix64.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0xD1B5_4A32_D192_ED03)
    }

    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    pub fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n.max(1)
    }

    pub fn pct(&mut self, p: u64) -> bool {
        self.below(100) < p
    }

    fn pick<'a, T>(&mut self, xs: &'a [T]) -> &'a T {
        &xs[self.below(xs.len() as u64) as usize]
    }

    fn shuffle<T>(&mut self, xs: &mut [T]) {
        for i in (1..xs.len()).rev() {
            let j = self.below(i as u64 + 1) as usize;
            xs.swap(i, j);
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Ty {
    Int,
    IntSet,
    SetSet,
    Pair,
    PairSet,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Level {
    Const,
    State,
    Action,
}

#[derive(Clone, Debug)]
enum Kind {
    /// A bound variable: a value.
    Value,
    /// An operator parameter. `state_only` parameters take state-level
    /// actuals only, so the body may prime them.
    Param { state_only: bool },
    /// A zero-arity LET definition of the given level.
    LetDef(Level),
}

#[derive(Clone, Debug)]
struct Local {
    name: String,
    ty: Ty,
    kind: Kind,
}

impl Local {
    fn level(&self) -> Level {
        match self.kind {
            Kind::Value => Level::Const,
            Kind::Param { state_only: true } => Level::State,
            Kind::Param { state_only: false } => Level::Action,
            Kind::LetDef(l) => l,
        }
    }
}

/// What an operator returns: a value of a type, or an action.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Ret {
    Val(Ty),
    Action,
}

#[derive(Clone, Debug)]
struct OpSig {
    name: String,
    /// Parameter types and whether each takes state-level actuals only.
    params: Vec<(Ty, bool)>,
    ret: Ret,
    /// The level of the body, not counting what its actuals contribute.
    level: Level,
    shape: OpShape,
}

/// How an operator's application is written.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum OpShape {
    /// Each actual generated for its parameter's type and level.
    Plain,
    /// One parameter, primed as an assignment target in the body
    /// (`Set(v) == v' = e`): its actual is the state variable itself.
    AssignsFormal(Var),
    /// `HO(F(_), a) == F(a)` (or `LET D == a IN F(D)`): the first actual is
    /// a `LAMBDA` or the name of an `AssignsFormal` operator over `x`.
    HigherOrder,
}

pub struct Gen<'r> {
    rng: &'r mut Rng,
    ops: Vec<OpSig>,
    locals: Vec<Local>,
    /// Primes may be written here (an action, not under a prime).
    primes_ok: bool,
    /// ENABLED may be written here.
    enabled_ok: bool,
    /// Whether this expression is inside an ENABLED operand (no second
    /// level of ENABLED nesting, to keep the brute force small).
    in_enabled: bool,
    /// Percent of integer/set/pair leaves written as a primed state variable
    /// where primes are allowed (raised inside ENABLED operands, so reads of
    /// primes before and after their assignment are common).
    prime_bias: u64,
    fresh: u32,
    /// Names a binder may not take although no expression may read them: the
    /// formal of the operator whose body is being generated, when the body
    /// reads it only through its own fixed shape. A binder reusing a visible
    /// formal is a module SANY rejects ("Multiply-defined symbol").
    reserved: Vec<String>,
    /// The module-level definitions generated so far.
    out_defs: Vec<Def>,
    /// Module-level definitions naming a tuple of state variables
    /// (`VT1 == <<x, y>>`), for `UNCHANGED` and `<<A>>_e`.
    var_tuples: Vec<String>,
}

const BINDERS: [&str; 6] = ["k", "n", "s", "a", "c", "w"];
const LET_NAMES: [&str; 4] = ["S", "T", "U", "R"];
const LET_OPS: [&str; 2] = ["G", "H"];

impl<'r> Gen<'r> {
    pub fn new(rng: &'r mut Rng) -> Self {
        Gen {
            rng,
            ops: Vec::new(),
            locals: Vec::new(),
            primes_ok: false,
            enabled_ok: true,
            in_enabled: false,
            prime_bias: 0,
            fresh: 0,
            reserved: Vec::new(),
            out_defs: Vec::new(),
            var_tuples: Vec::new(),
        }
    }

    // ---- scope helpers ----

    fn in_scope(&self, n: &str) -> bool {
        self.locals.iter().any(|l| l.name == n)
            || self.ops.iter().any(|o| o.name == n)
            || self.reserved.iter().any(|r| r == n)
    }

    fn fresh_from(&mut self, pool: &[&str]) -> String {
        let free: Vec<&str> = pool.iter().copied().filter(|n| !self.in_scope(n)).collect();
        if free.is_empty() {
            self.fresh += 1;
            return format!("v{}", self.fresh);
        }
        self.rng.pick(&free).to_string()
    }

    fn max_level(&self) -> Level {
        if self.primes_ok {
            Level::Action
        } else {
            Level::State
        }
    }

    fn visible(&self, ty: Ty) -> Vec<Local> {
        let max = self.max_level();
        self.locals
            .iter()
            .filter(|l| l.ty == ty && l.level() <= max)
            .cloned()
            .collect()
    }

    fn with<T>(&mut self, primes_ok: bool, enabled_ok: bool, f: impl FnOnce(&mut Self) -> T) -> T {
        let saved = (self.primes_ok, self.enabled_ok);
        self.primes_ok = primes_ok;
        self.enabled_ok = enabled_ok;
        let out = f(self);
        self.primes_ok = saved.0;
        self.enabled_ok = saved.1;
        out
    }

    /// Generate `f` under a prime: no primes, no ENABLED, state-level names.
    fn under_prime<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.with(false, false, f)
    }

    fn bind<T>(&mut self, locals: Vec<Local>, f: impl FnOnce(&mut Self) -> T) -> T {
        let n = locals.len();
        self.locals.extend(locals);
        let out = f(self);
        let keep = self.locals.len() - n;
        self.locals.truncate(keep);
        out
    }

    fn ops_returning(&self, ret: Ret) -> Vec<OpSig> {
        let max = self.max_level();
        self.ops
            .iter()
            .filter(|o| o.ret == ret && o.level <= max)
            .cloned()
            .collect()
    }

    // ---- typed expressions ----

    fn small_int(&mut self) -> E {
        int(self.rng.below(4) as i64)
    }

    pub fn gen_int(&mut self, d: u32) -> E {
        if self.primes_ok && self.rng.pct(self.prime_bias) {
            return if self.rng.pct(70) {
                prime(x())
            } else {
                index(prime(z()), 1 + self.rng.below(2) as i64)
            };
        }
        let names = self.visible(Ty::Int);
        let choice = if d == 0 {
            self.rng.below(5)
        } else {
            self.rng.below(11)
        };
        match choice {
            0 => self.small_int(),
            1 => x(),
            2 if self.primes_ok => prime(x()),
            3 if !names.is_empty() => name(&self.rng.pick(&names).name.clone()),
            4 => {
                let t = if self.primes_ok && self.rng.pct(40) {
                    prime(z())
                } else {
                    z()
                };
                index(t, 1 + self.rng.below(2) as i64)
            }
            5 => modulo(add(self.gen_int(d - 1), self.gen_int(d - 1)), 4),
            6 => card(self.gen_intset(d - 1)),
            7 => index(self.gen_pair(d - 1), 1 + self.rng.below(2) as i64),
            8 => ite(
                self.gen_bool(d - 1),
                self.gen_int(d - 1),
                self.gen_int(d - 1),
            ),
            9 => self
                .gen_apply(Ret::Val(Ty::Int), d)
                .unwrap_or_else(|| self.small_int()),
            10 if self.primes_ok => prime(x()),
            _ => self.small_int(),
        }
    }

    pub fn gen_intset(&mut self, d: u32) -> E {
        if self.primes_ok && self.rng.pct(self.prime_bias / 2) {
            return prime(y());
        }
        let names = self.visible(Ty::IntSet);
        let choice = if d == 0 {
            self.rng.below(6)
        } else {
            self.rng.below(13)
        };
        match choice {
            0 => range(1, 3),
            1 => set(vec![int(1 + self.rng.below(3) as i64)]),
            2 => y(),
            3 if self.primes_ok => prime(y()),
            4 if !names.is_empty() => name(&self.rng.pick(&names).name.clone()),
            5 => {
                if self.rng.pct(50) {
                    set(vec![])
                } else {
                    range(1, 2)
                }
            }
            6 => set(vec![add(modulo(self.gen_int(d - 1), 3), int(1))]),
            7 => cup(self.gen_intset(d - 1), self.gen_intset(d - 1)),
            8 => cap(self.gen_intset(d - 1), self.gen_intset(d - 1)),
            9 => diff(self.gen_intset(d - 1), self.gen_intset(d - 1)),
            10 => {
                let src = self.gen_intset(d - 1);
                let v = self.fresh_from(&BINDERS);
                let pred = self.bind(
                    vec![Local {
                        name: v.clone(),
                        ty: Ty::Int,
                        kind: Kind::Value,
                    }],
                    |g| g.gen_bool(d - 1),
                );
                filter(Pat::One(v), src, pred)
            }
            11 => self
                .gen_apply(Ret::Val(Ty::IntSet), d)
                .unwrap_or_else(|| range(1, 3)),
            12 => self
                .gen_primed_name_or_apply(Ty::IntSet, d)
                .unwrap_or_else(y),
            _ => y(),
        }
    }

    /// A subset of `SUBSET (1..3)`.
    pub fn gen_setset(&mut self, d: u32) -> E {
        let names = self.visible(Ty::SetSet);
        let choice = if d == 0 {
            self.rng.below(3)
        } else {
            self.rng.below(10)
        };
        match choice {
            0 => subsets(),
            1 if !names.is_empty() => name(&self.rng.pick(&names).name.clone()),
            2 => subset(range(1, 2)),
            3 | 4 => {
                let src = if self.rng.pct(70) {
                    subset(self.gen_intset(d - 1))
                } else {
                    self.gen_setset(d - 1)
                };
                self.setset_filter(src, d)
            }
            5 | 6 => self
                .gen_apply(Ret::Val(Ty::SetSet), d)
                .unwrap_or_else(subsets),
            7 => self
                .gen_primed_name_or_apply(Ty::SetSet, d)
                .unwrap_or_else(subsets),
            8 if self.primes_ok => {
                // An inline filter built under a prime.
                let f = self.under_prime(|g| {
                    let src = subset(g.gen_intset(d - 1));
                    g.setset_filter(src, d)
                });
                prime(f)
            }
            _ => subset(self.gen_intset(d.saturating_sub(1))),
        }
    }

    fn setset_filter(&mut self, src: E, d: u32) -> E {
        let v = self.fresh_from(&BINDERS);
        let pred = self.bind(
            vec![Local {
                name: v.clone(),
                ty: Ty::IntSet,
                kind: Kind::Value,
            }],
            |g| g.gen_bool(d.saturating_sub(1)),
        );
        filter(Pat::One(v), src, pred)
    }

    pub fn gen_pair(&mut self, d: u32) -> E {
        if self.primes_ok && self.rng.pct(self.prime_bias / 2) {
            return prime(z());
        }
        let names = self.visible(Ty::Pair);
        let choice = if d == 0 {
            self.rng.below(4)
        } else {
            self.rng.below(6)
        };
        match choice {
            0 => pair(1 + self.rng.below(2) as i64, 1 + self.rng.below(2) as i64),
            1 => z(),
            2 if self.primes_ok => prime(z()),
            3 if !names.is_empty() => name(&self.rng.pick(&names).name.clone()),
            4 | 5 => tuple(vec![
                add(modulo(self.gen_int(d - 1), 2), int(1)),
                add(modulo(self.gen_int(d - 1), 2), int(1)),
            ]),
            _ => z(),
        }
    }

    /// A subset of `(1..2) \X (1..2)`.
    pub fn gen_pairset(&mut self, d: u32) -> E {
        let names = self.visible(Ty::PairSet);
        let choice = if d == 0 {
            self.rng.below(2)
        } else {
            self.rng.below(8)
        };
        match choice {
            0 => pairs(),
            1 if !names.is_empty() => name(&self.rng.pick(&names).name.clone()),
            2 => times(
                cap(self.gen_intset(d - 1), range(1, 2)),
                cap(self.gen_intset(d - 1), range(1, 2)),
            ),
            3 | 4 => {
                let src = if self.rng.pct(70) {
                    pairs()
                } else {
                    self.gen_pairset(d - 1)
                };
                self.pair_filter(src, d)
            }
            5 => self
                .gen_apply(Ret::Val(Ty::PairSet), d)
                .unwrap_or_else(pairs),
            6 => self
                .gen_primed_name_or_apply(Ty::PairSet, d)
                .unwrap_or_else(pairs),
            7 if self.primes_ok => {
                let f = self.under_prime(|g| g.pair_filter(pairs(), d));
                prime(f)
            }
            _ => pairs(),
        }
    }

    /// `{<<a, c>> \in src : P}` (a tuple pattern) or `{w \in src : P}`.
    fn pair_filter(&mut self, src: E, d: u32) -> E {
        if self.rng.pct(70) {
            let a = self.fresh_from(&BINDERS);
            let locals_a = vec![Local {
                name: a.clone(),
                ty: Ty::Int,
                kind: Kind::Value,
            }];
            let (c, pred) = self.bind(locals_a, |g| {
                let c = g.fresh_from(&BINDERS);
                let pred = g.bind(
                    vec![Local {
                        name: c.clone(),
                        ty: Ty::Int,
                        kind: Kind::Value,
                    }],
                    |g| g.gen_bool(d.saturating_sub(1)),
                );
                (c, pred)
            });
            filter(Pat::Tup(vec![a, c]), src, pred)
        } else {
            let w = self.fresh_from(&BINDERS);
            let pred = self.bind(
                vec![Local {
                    name: w.clone(),
                    ty: Ty::Pair,
                    kind: Kind::Value,
                }],
                |g| g.gen_bool(d.saturating_sub(1)),
            );
            filter(Pat::One(w), src, pred)
        }
    }

    /// `S'` for a state-level LET definition or `F(args)'` for a
    /// state-level operator, in an action.
    fn gen_primed_name_or_apply(&mut self, ty: Ty, d: u32) -> Option<E> {
        if !self.primes_ok {
            return None;
        }
        let names: Vec<Local> = self
            .locals
            .iter()
            .filter(|l| l.ty == ty && matches!(l.kind, Kind::LetDef(lv) if lv <= Level::State))
            .cloned()
            .collect();
        if !names.is_empty() && self.rng.pct(50) {
            return Some(prime(name(&self.rng.pick(&names).name.clone())));
        }
        let ops: Vec<OpSig> = self
            .ops
            .iter()
            .filter(|o| o.ret == Ret::Val(ty) && o.level <= Level::State)
            .cloned()
            .collect();
        if ops.is_empty() {
            return None;
        }
        let op = self.rng.pick(&ops).clone();
        let applied = self.under_prime(|g| g.apply_with_args(&op, d));
        Some(prime(applied))
    }

    fn apply_with_args(&mut self, op: &OpSig, d: u32) -> E {
        match op.shape {
            OpShape::AssignsFormal(v) => return apply(&op.name, vec![E::Var(v)]),
            OpShape::HigherOrder => return self.apply_higher_order(op, d),
            OpShape::Plain => {}
        }
        let args: Vec<E> = op
            .params
            .iter()
            .map(|(ty, state_only)| {
                let ty = *ty;
                if *state_only {
                    let primes = false;
                    let enabled = self.enabled_ok && !self.in_enabled;
                    self.with(primes, enabled, |g| g.gen_value(ty, d.saturating_sub(1)))
                } else if ty == Ty::Int && self.primes_ok && self.rng.pct(40) {
                    // An action-level actual, forced by name wherever the
                    // body (or a LET over the formal) reads it.
                    self.action_level_int()
                } else {
                    self.gen_value(ty, d.saturating_sub(1))
                }
            })
            .collect();
        if op.params.is_empty() {
            name(&op.name)
        } else {
            apply(&op.name, args)
        }
    }

    /// `x' + k`, `z'[i]`: an integer actual that reads the successor.
    fn action_level_int(&mut self) -> E {
        match self.rng.below(3) {
            0 => modulo(add(prime(x()), self.small_int()), 4),
            1 => index(prime(z()), 1 + self.rng.below(2) as i64),
            _ => prime(x()),
        }
    }

    /// `HO(op, a)`: a `LAMBDA` that uses its parameter as a value (any
    /// actual), a `LAMBDA` that assigns through it, or an operator that
    /// assigns through its formal (the actual is then `x`).
    fn apply_higher_order(&mut self, op: &OpSig, d: u32) -> E {
        let v = self.fresh_from(&BINDERS);
        let assigning: Vec<String> = self
            .ops
            .iter()
            .filter(|o| o.shape == OpShape::AssignsFormal(Var::X))
            .map(|o| o.name.clone())
            .collect();
        match self.rng.below(3) {
            0 => {
                // Uses the parameter as a value: `x' = (v + c) % 4`.
                let c = self.small_int();
                let f = lambda(&[&v], eq(prime(x()), modulo(add(name(&v), c), 4)));
                let a = if self.primes_ok && self.rng.pct(50) {
                    self.action_level_int()
                } else {
                    self.with(false, false, |g| g.gen_int(d.saturating_sub(1).min(1)))
                };
                apply(&op.name, vec![f, a])
            }
            1 if !assigning.is_empty() => {
                let set = self.rng.pick(&assigning).clone();
                apply(&op.name, vec![name(&set), x()])
            }
            _ => {
                // Assigns through the parameter: `v' = e`, applied to `x`.
                let e = self.with(false, false, |g| g.gen_int(1));
                let f = lambda(&[&v], eq(prime(name(&v)), modulo(e, 4)));
                apply(&op.name, vec![f, x()])
            }
        }
    }

    /// A tuple of state variables to leave unchanged: written out, a
    /// module definition naming one, or a tuple nesting both.
    fn var_tuple_expr(&mut self) -> E {
        let mut vars: Vec<Var> = VARS.to_vec();
        self.rng.shuffle(&mut vars);
        let n = 1 + self.rng.below(3) as usize;
        let written = tuple(vars[..n].iter().map(|v| E::Var(*v)).collect());
        if self.var_tuples.is_empty() || self.rng.pct(35) {
            return written;
        }
        let named = name(&self.rng.pick(&self.var_tuples).clone());
        if self.rng.pct(50) {
            named
        } else {
            tuple(vec![E::Var(vars[0]), named])
        }
    }

    /// `UNCHANGED e` of a tuple (sometimes LET-bound).
    fn unchanged_tuple(&mut self) -> E {
        let t = self.var_tuple_expr();
        if self.rng.pct(25) {
            let w = self.fresh_from(&LET_NAMES);
            let_in(
                vec![Def {
                    name: w.clone(),
                    params: vec![],
                    arities: Vec::new(),
                    body: t,
                }],
                unchanged_e(name(&w)),
            )
        } else {
            unchanged_e(t)
        }
    }

    fn gen_apply(&mut self, ret: Ret, d: u32) -> Option<E> {
        let ops = self.ops_returning(ret);
        if ops.is_empty() {
            return None;
        }
        let op = self.rng.pick(&ops).clone();
        Some(self.apply_with_args(&op, d))
    }

    pub fn gen_value(&mut self, ty: Ty, d: u32) -> E {
        match ty {
            Ty::Int => self.gen_int(d),
            Ty::IntSet => self.gen_intset(d),
            Ty::SetSet => self.gen_setset(d),
            Ty::Pair => self.gen_pair(d),
            Ty::PairSet => self.gen_pairset(d),
        }
    }

    fn gen_set_of(&mut self, d: u32) -> (E, Ty) {
        match self.rng.below(4) {
            0 | 1 => (self.gen_intset(d), Ty::Int),
            2 => (self.gen_setset(d), Ty::IntSet),
            _ => (self.gen_pairset(d), Ty::Pair),
        }
    }

    pub fn gen_bool(&mut self, d: u32) -> E {
        let choice = if d == 0 {
            self.rng.below(6)
        } else {
            self.rng.below(16)
        };
        match choice {
            0 => eq(self.gen_int(0), self.gen_int(0)),
            1 => elem(self.gen_int(0), self.gen_intset(0)),
            2 => notin(self.gen_int(0), self.gen_intset(0)),
            3 => lt(self.gen_int(0), self.gen_int(0)),
            4 => subseteq(self.gen_intset(0), self.gen_intset(0)),
            5 => elem(self.gen_pair(0), self.gen_pairset(0)),
            6 => elem(self.gen_intset(d - 1), self.gen_setset(d - 1)),
            7 => eq(self.gen_intset(d - 1), self.gen_intset(d - 1)),
            8 => not(self.gen_bool(d - 1)),
            9 => and(vec![self.gen_bool(d - 1), self.gen_bool(d - 1)]),
            10 => or(vec![self.gen_bool(d - 1), self.gen_bool(d - 1)]),
            11 | 12 => self.gen_quant_bool(d),
            13 if self.enabled_ok && !self.in_enabled => {
                let e = enabled(self.gen_enabled_operand(d - 1));
                if self.rng.pct(50) {
                    not(e)
                } else {
                    e
                }
            }
            14 if self.primes_ok && self.rng.pct(40) => {
                // UNCHANGED read as a Boolean: negated, or an IF guard.
                let u = self.unchanged_tuple();
                if self.rng.pct(50) {
                    not(u)
                } else {
                    ite(u, self.gen_bool(d - 1), self.gen_bool(d - 1))
                }
            }
            14 => eq(self.gen_int(d - 1), self.gen_int(d - 1)),
            15 if self.rng.pct(25) => E::Bool(self.rng.pct(50)),
            _ => elem(self.gen_int(d - 1), self.gen_intset(d - 1)),
        }
    }

    fn gen_quant_bool(&mut self, d: u32) -> E {
        let (dom, ety) = self.gen_set_of(d - 1);
        let (pat, locals) = self.binder_for(ety);
        let body = self.bind(locals, |g| g.gen_bool(d - 1));
        if self.rng.pct(50) {
            exists(pat, dom, body)
        } else {
            forall(pat, dom, body)
        }
    }

    /// A binder for members of type `ty`: a pair is sometimes destructured
    /// by a tuple pattern.
    fn binder_for(&mut self, ty: Ty) -> (Pat, Vec<Local>) {
        if ty == Ty::Pair && self.rng.pct(60) {
            let a = self.fresh_from(&BINDERS);
            let la = Local {
                name: a.clone(),
                ty: Ty::Int,
                kind: Kind::Value,
            };
            self.locals.push(la.clone());
            let c = self.fresh_from(&BINDERS);
            self.locals.pop();
            let lc = Local {
                name: c.clone(),
                ty: Ty::Int,
                kind: Kind::Value,
            };
            (Pat::Tup(vec![a, c]), vec![la, lc])
        } else {
            let v = self.fresh_from(&BINDERS);
            (
                Pat::One(v.clone()),
                vec![Local {
                    name: v,
                    ty,
                    kind: Kind::Value,
                }],
            )
        }
    }

    // ---- actions ----

    fn assignment(&mut self, d: u32) -> E {
        match self.rng.below(9) {
            0 | 1 => eq(prime(x()), self.gen_int(d)),
            2 => eq(prime(y()), self.gen_intset(d)),
            3 | 4 => elem(prime(y()), self.gen_setset(d)),
            5 => eq(prime(z()), self.gen_pair(d)),
            6 => elem(prime(z()), self.gen_pairset(d)),
            7 => elem(prime(x()), self.gen_intset(d)),
            _ => match self.rng.below(6) {
                0 => subseteq(prime(y()), self.gen_intset(d)),
                1 => unchanged(Var::X),
                2 => unchanged(Var::Y),
                3 => unchanged(Var::Z),
                _ => self.unchanged_tuple(),
            },
        }
    }

    fn action_item(&mut self, d: u32) -> E {
        let choice = if d == 0 {
            self.rng.below(10)
        } else {
            self.rng.below(21)
        };
        match choice {
            0..=5 => self.assignment(d),
            6..=9 => self.gen_bool(d.min(2)),
            10 | 11 => {
                let (dom, ety) = self.gen_set_of(d - 1);
                let (pat, locals) = self.binder_for(ety);
                let body = self.bind(locals, |g| g.gen_action(d - 1));
                exists(pat, dom, body)
            }
            12 => or(vec![self.gen_action(d - 1), self.gen_action(d - 1)]),
            13 | 14 => self.gen_let(d, |g, d| g.gen_action(d)),
            15 => ite(
                self.gen_bool(d - 1),
                self.gen_action(d - 1),
                self.gen_action(d - 1),
            ),
            16 | 17 => self
                .gen_apply(Ret::Action, d)
                .unwrap_or_else(|| self.assignment(d - 1)),
            18 if self.enabled_ok && !self.in_enabled => {
                let e = enabled(self.gen_enabled_operand(d - 1));
                if self.rng.pct(60) {
                    not(e)
                } else {
                    e
                }
            }
            19 if self.primes_ok && self.rng.pct(50) => self.let_forwarding_chain(),
            _ => self.assignment(d.saturating_sub(1)),
        }
    }

    /// `LET H(r) == r' = e  G(q) == H(q) IN G(v)`: a LET operator's formal
    /// primed only through the LET operator it is passed to (sometimes via
    /// a LET alias of the formal), applied to a state variable.
    fn let_forwarding_chain(&mut self) -> E {
        let v = *self.rng.pick(&VARS);
        self.let_forwarding_chain_for(v)
    }

    /// [`Self::let_forwarding_chain`] assigning `v`.
    fn let_forwarding_chain_for(&mut self, v: Var) -> E {
        let ty = match v {
            Var::X => Ty::Int,
            Var::Y => Ty::IntSet,
            Var::Z => Ty::Pair,
        };
        let h = self.fresh_from(&LET_OPS);
        // `h` is not yet in scope: keep the two names distinct.
        self.ops.push(OpSig {
            name: h.clone(),
            params: vec![],
            ret: Ret::Action,
            level: Level::Action,
            shape: OpShape::Plain,
        });
        let g = self.fresh_from(&LET_OPS);
        let r = self.fresh_from(&BINDERS);
        let q = self.fresh_from(&BINDERS);
        self.ops.pop();
        let value = self.with(false, false, |g| g.gen_value(ty, 1));
        let h_body = if ty == Ty::Int {
            eq(prime(name(&r)), modulo(value, 4))
        } else if ty == Ty::IntSet {
            eq(prime(name(&r)), cap(value, range(1, 3)))
        } else {
            eq(prime(name(&r)), value)
        };
        let g_body = if self.rng.pct(40) {
            let alias = self.fresh_from(&LET_NAMES);
            let_in(
                vec![def(&alias, &[], name(&q))],
                apply(&h, vec![name(&alias)]),
            )
        } else {
            apply(&h, vec![name(&q)])
        };
        let_in(
            vec![def(&h, &[&r], h_body), def(&g, &[&q], g_body)],
            apply(&g, vec![E::Var(v)]),
        )
    }

    pub fn gen_action(&mut self, d: u32) -> E {
        let n = 1 + self.rng.below(3) as usize;
        let items: Vec<E> = (0..n).map(|_| self.action_item(d)).collect();
        if items.len() == 1 {
            items.into_iter().next().unwrap()
        } else {
            and(items)
        }
    }

    /// `LET defs IN body`: zero-arity definitions of any type (filters
    /// included, primed or reading primes when allowed) and sometimes a
    /// parameterized LET operator capturing the enclosing binders.
    fn gen_let(&mut self, d: u32, body: impl FnOnce(&mut Self, u32) -> E) -> E {
        let mut defs = Vec::new();
        let mut locals = Vec::new();
        let mut ops = Vec::new();
        let n = 1 + self.rng.below(2);
        for _ in 0..n {
            if self.rng.pct(25) {
                // A parameterized LET operator over a filter.
                let opname = self.fresh_from(&LET_OPS);
                let pname = self.fresh_from(&BINDERS);
                let ret_ty = if self.rng.pct(70) {
                    Ty::SetSet
                } else {
                    Ty::PairSet
                };
                let level_before = self.primes_ok;
                let state_level = self.rng.pct(50) || !level_before;
                let body_e = self.with(!state_level && level_before, false, |g| {
                    g.bind(
                        vec![Local {
                            name: pname.clone(),
                            ty: Ty::Int,
                            kind: Kind::Param { state_only: true },
                        }],
                        |g| match ret_ty {
                            Ty::SetSet => {
                                let src = subset(g.gen_intset(1));
                                g.setset_filter(src, 2)
                            }
                            _ => g.pair_filter(pairs(), 2),
                        },
                    )
                });
                let level = if state_level {
                    Level::State
                } else {
                    Level::Action
                };
                defs.push(Def {
                    name: opname.clone(),
                    params: vec![pname],
                    arities: Vec::new(),
                    body: body_e,
                });
                // Visible to the following definitions and the body.
                self.ops.push(OpSig {
                    name: opname,
                    params: vec![(Ty::Int, true)],
                    ret: Ret::Val(ret_ty),
                    level,
                    shape: OpShape::Plain,
                });
                ops.push(());
                continue;
            }
            let dname = self.fresh_from(&LET_NAMES);
            let ty = *self.rng.pick(&[
                Ty::SetSet,
                Ty::SetSet,
                Ty::SetSet,
                Ty::IntSet,
                Ty::Int,
                Ty::PairSet,
            ]);
            let (body_e, level) = if self.primes_ok && self.rng.pct(50) {
                // May read primes: an action-level definition (never primed).
                let e = self.gen_value(ty, d.min(2));
                (e, Level::Action)
            } else {
                let e = self.with(false, false, |g| g.gen_value(ty, d.min(2)));
                (e, Level::State)
            };
            defs.push(Def {
                name: dname.clone(),
                params: vec![],
                arities: Vec::new(),
                body: body_e,
            });
            let l = Local {
                name: dname,
                ty,
                kind: Kind::LetDef(level),
            };
            self.locals.push(l.clone());
            locals.push(l);
        }
        let b = body(self, d.saturating_sub(1));
        for _ in &locals {
            self.locals.pop();
        }
        for _ in &ops {
            self.ops.pop();
        }
        let_in(defs, b)
    }

    /// An ENABLED operand: an action, then the primed type memberships.
    ///
    /// The action assigns a random subset of the variables and reads primes
    /// in 1-3 tests, in a random order, so a prime is read before its
    /// assignment, after it, or never assigned, with the witness empty or
    /// not; a set drawn from is often a filter (inline, an operator's, a LET
    /// definition, primed) whose predicate reads primes. Sometimes it is
    /// wrapped in a LET whose definitions the items prefer to reference.
    pub fn gen_enabled_operand(&mut self, d: u32) -> E {
        let saved = (self.primes_ok, self.in_enabled, self.prime_bias);
        self.primes_ok = true;
        self.in_enabled = true;
        self.prime_bias = 35;
        let a = if self.rng.pct(35) {
            self.gen_let(d.max(1), |g, d| g.operand_items(d.max(1)))
        } else {
            self.operand_items(d.max(1))
        };
        // `<<A>>_e`: the action must change `e` (lowered to
        // `A /\ ~(UNCHANGED e)`).
        let a = if self.rng.pct(15) {
            let sub = self.var_tuple_expr();
            angle(a, sub)
        } else {
            a
        };
        self.primes_ok = saved.0;
        self.in_enabled = saved.1;
        self.prime_bias = saved.2;
        let mut items = vec![a];
        items.extend(type_ok_primed());
        and(items)
    }

    fn operand_items(&mut self, d: u32) -> E {
        let mut assigns = Vec::new();
        for v in VARS {
            if self.rng.pct(55) {
                assigns.push(self.assign_var(v, d));
            }
        }
        let mut reads = Vec::new();
        for _ in 0..(1 + self.rng.below(3)) {
            reads.push(self.read_item(d));
        }
        if self.rng.pct(30) {
            reads.push(self.action_item(d));
        }
        if self.rng.pct(25) {
            if let Some(call) = self.gen_apply(Ret::Action, d) {
                reads.push(call);
            }
        }
        // Half the time assignments come first (reads see an assigned
        // witness and a verdict is due); otherwise any order.
        let mut items = if self.rng.pct(50) {
            self.rng.shuffle(&mut assigns);
            self.rng.shuffle(&mut reads);
            assigns.into_iter().chain(reads).collect::<Vec<_>>()
        } else {
            let mut all: Vec<E> = assigns.into_iter().chain(reads).collect();
            self.rng.shuffle(&mut all);
            all
        };
        if items.len() == 1 {
            items.pop().unwrap()
        } else {
            and(items)
        }
    }

    /// Whether a LET definition of type `ty` is in scope (and usable here).
    fn has_let(&self, ty: Ty) -> bool {
        let max = self.max_level();
        self.locals
            .iter()
            .any(|l| l.ty == ty && matches!(l.kind, Kind::LetDef(_)) && l.level() <= max)
    }

    /// A LET definition of type `ty` in scope, preferred when there is one.
    fn let_name(&mut self, ty: Ty) -> Option<E> {
        let max = self.max_level();
        let names: Vec<String> = self
            .locals
            .iter()
            .filter(|l| l.ty == ty && matches!(l.kind, Kind::LetDef(_)) && l.level() <= max)
            .map(|l| l.name.clone())
            .collect();
        if names.is_empty() || !self.rng.pct(80) {
            return None;
        }
        Some(name(&self.rng.pick(&names).clone()))
    }

    fn assign_var(&mut self, v: Var, d: u32) -> E {
        match v {
            Var::X => {
                if self.rng.pct(70) {
                    eq(prime(x()), self.gen_int(d))
                } else {
                    elem(prime(x()), self.gen_intset(d))
                }
            }
            Var::Y if self.has_let(Ty::SetSet) && self.rng.pct(70) => {
                let s = self.let_name(Ty::SetSet).unwrap_or_else(subsets);
                let primable = matches!(&s, E::Name(n) if self.locals.iter()
                    .any(|l| &l.name == n && l.level() <= Level::State));
                if primable && self.rng.pct(70) {
                    elem(prime(y()), prime(s))
                } else {
                    elem(prime(y()), s)
                }
            }
            Var::Y => match self.rng.below(6) {
                0 => eq(prime(y()), self.gen_intset(d)),
                1 => subseteq(prime(y()), self.gen_intset(d)),
                2 => {
                    let s = match self.let_name(Ty::SetSet) {
                        Some(n) if self.rng.pct(50) => n,
                        Some(n) => match self
                            .locals
                            .iter()
                            .find(|l| E::Name(l.name.clone()) == n)
                            .map(|l| l.level())
                        {
                            Some(lv) if lv <= Level::State => prime(n),
                            _ => n,
                        },
                        None => self.gen_setset(d),
                    };
                    elem(prime(y()), s)
                }
                _ => elem(prime(y()), self.gen_setset(d)),
            },
            Var::Z => {
                if self.rng.pct(40) {
                    eq(prime(z()), self.gen_pair(d))
                } else {
                    let s = self
                        .let_name(Ty::PairSet)
                        .unwrap_or_else(|| self.gen_pairset(d));
                    elem(prime(z()), s)
                }
            }
        }
    }

    /// A test that reads primes.
    fn read_item(&mut self, d: u32) -> E {
        match self.rng.below(8) {
            0 => notin(int(1 + self.rng.below(3) as i64), prime(y())),
            1 => elem(int(1 + self.rng.below(3) as i64), prime(y())),
            2 => eq(prime(y()), self.gen_intset(d.min(1))),
            3 => notin(self.gen_int(d.min(1)), prime(y())),
            4 => eq(
                index(prime(z()), 1 + self.rng.below(2) as i64),
                self.gen_int(d.min(1)),
            ),
            5 => lt(self.gen_int(d.min(1)), self.gen_int(d.min(1))),
            _ => self.gen_bool(d.min(2)),
        }
    }

    // ---- module-level operators ----

    fn gen_module_op(&mut self, idx: usize) {
        match self.rng.below(10) {
            6 | 7 => return self.gen_alias_op(idx),
            8 => return self.gen_assigning_op(idx),
            9 => return self.gen_higher_order_op(idx),
            _ => {}
        }
        let kind = self.rng.below(6);
        let nparams = self.rng.below(3) as usize;
        let mut params = Vec::new();
        let mut locals = Vec::new();
        let ret = match kind {
            0 | 1 => Ret::Val(Ty::SetSet),
            2 => Ret::Val(Ty::PairSet),
            3 => Ret::Val(Ty::Int),
            _ => Ret::Action,
        };
        for _ in 0..nparams {
            let pname = self.fresh_from(&BINDERS);
            // An action operator sometimes takes a set it primes
            // (`A(S) == y' \in S'`): such a parameter takes state-level
            // actuals only, as SANY requires.
            let ty = if ret == Ret::Action && self.rng.pct(60) {
                Ty::SetSet
            } else {
                Ty::Int
            };
            let state_only = ty == Ty::SetSet || self.rng.pct(70);
            let l = Local {
                name: pname.clone(),
                ty,
                kind: Kind::Param { state_only },
            };
            self.locals.push(l.clone());
            locals.push(l);
            params.push((pname, ty, state_only));
        }
        let action_level = ret == Ret::Action || self.rng.pct(50);
        // No ENABLED in a module operator: an action operator may be applied
        // inside an ENABLED operand, and the model nests no second ENABLED.
        let body = self.with(action_level, false, |g| match ret {
            Ret::Val(Ty::SetSet) => {
                let src = if g.rng.pct(80) {
                    subsets()
                } else {
                    subset(g.gen_intset(1))
                };
                g.setset_filter(src, 2)
            }
            Ret::Val(Ty::PairSet) => g.pair_filter(pairs(), 2),
            Ret::Val(_) => g.gen_int(2),
            Ret::Action => {
                // Prime a SetSet parameter now and then.
                let primable: Vec<String> = params
                    .iter()
                    .filter(|(_, ty, so)| *ty == Ty::SetSet && *so)
                    .map(|(n, _, _)| n.clone())
                    .collect();
                if !primable.is_empty() && g.rng.pct(80) {
                    let p = g.rng.pick(&primable).clone();
                    let mut items = vec![elem(prime(y()), prime(name(&p)))];
                    items.push(g.action_item(1));
                    g.rng.shuffle(&mut items);
                    and(items)
                } else {
                    g.gen_action(2)
                }
            }
        });
        self.locals.truncate(self.locals.len() - locals.len());
        let level = if action_level {
            Level::Action
        } else {
            Level::State
        };
        let opname = match ret {
            Ret::Action => format!("Act{idx}"),
            Ret::Val(Ty::Int) => format!("Num{idx}"),
            Ret::Val(_) => format!("Flt{idx}"),
        };
        self.ops.push(OpSig {
            name: opname.clone(),
            params: params.iter().map(|(_, t, so)| (*t, *so)).collect(),
            ret,
            level,
            shape: OpShape::Plain,
        });
        self.out_defs.push(Def {
            name: opname,
            params: params.into_iter().map(|(n, _, _)| n).collect(),
            arities: Vec::new(),
            body,
        });
    }
}

impl Gen<'_> {
    /// `AliasK(p) == LET D == p IN /\ <a branch over x'> /\ <a test of D>`
    /// (or `D == F(0)` with `F(i) == p + i`): the formal takes action-level
    /// actuals, so `D` reads the successor through the binding of `p`, and
    /// the branch offers several successors to the same `D`.
    fn gen_alias_op(&mut self, idx: usize) {
        let opname = format!("Alias{idx}");
        let p = self.fresh_from(&BINDERS);
        self.locals.push(Local {
            name: p.clone(),
            ty: Ty::Int,
            kind: Kind::Param { state_only: false },
        });
        let dname = self.fresh_from(&LET_NAMES);
        let via_operator = self.rng.pct(30);
        let fname = if via_operator {
            Some(self.fresh_from(&LET_OPS))
        } else {
            None
        };
        let i = self.fresh_from(&BINDERS);
        let mut defs = Vec::new();
        let d_body = match &fname {
            Some(f) => {
                defs.push(def(f, &[&i], modulo(add(name(&p), name(&i)), 4)));
                apply(f, vec![int(0)])
            }
            None => name(&p),
        };
        defs.push(def(&dname, &[], d_body));
        let branch = match self.rng.below(3) {
            0 => or(vec![
                eq(prime(x()), self.small_int()),
                eq(prime(x()), self.small_int()),
            ]),
            1 => {
                let v = self.fresh_from(&BINDERS);
                exists(one(&v), range(0, 3), eq(prime(x()), name(&v)))
            }
            _ => elem(prime(x()), range(0, 3)),
        };
        let test = match self.rng.below(3) {
            0 => eq(
                prime(z()),
                tuple(vec![add(modulo(name(&dname), 2), int(1)), int(1)]),
            ),
            1 => eq(name(&dname), self.small_int()),
            _ => lt(name(&dname), self.small_int()),
        };
        let mut items = vec![branch, test];
        if self.rng.pct(30) {
            items.reverse();
        }
        self.locals.pop();
        self.ops.push(OpSig {
            name: opname.clone(),
            params: vec![(Ty::Int, false)],
            ret: Ret::Action,
            level: Level::Action,
            shape: OpShape::Plain,
        });
        self.out_defs.push(Def {
            name: opname,
            params: vec![p],
            arities: Vec::new(),
            body: let_in(defs, and(items)),
        });
    }

    /// `SetK(v) == v' = e` (or `v' \in S`), applied to the state variable
    /// of `v`'s type: an assignment through a formal.
    fn gen_assigning_op(&mut self, idx: usize) {
        let opname = format!("Set{idx}");
        let var = *self.rng.pick(&VARS);
        let v = self.fresh_from(&BINDERS);
        let target = prime(name(&v));
        self.reserved.push(v.clone());
        let body = self.with(false, false, |g| match var {
            Var::X => {
                if g.rng.pct(70) {
                    eq(target, modulo(g.gen_int(1), 4))
                } else {
                    elem(target, range(0, 3))
                }
            }
            Var::Y => eq(target, cap(g.gen_intset(1), range(1, 3))),
            Var::Z => {
                if g.rng.pct(50) {
                    eq(target, g.gen_pair(1))
                } else {
                    elem(target, pairs())
                }
            }
        });
        self.reserved.pop();
        self.ops.push(OpSig {
            name: opname.clone(),
            params: vec![(Ty::Int, true)],
            ret: Ret::Action,
            level: Level::Action,
            shape: OpShape::AssignsFormal(var),
        });
        self.out_defs.push(Def {
            name: opname,
            params: vec![v],
            arities: Vec::new(),
            body,
        });
    }

    /// `HOK(F(_), a) == F(a)`, or `LET D == a IN F(D)`.
    fn gen_higher_order_op(&mut self, idx: usize) {
        let opname = format!("HO{idx}");
        let f = self.fresh_from(&["F", "Fn"]);
        let a = self.fresh_from(&BINDERS);
        let body = if self.rng.pct(50) {
            apply(&f, vec![name(&a)])
        } else {
            let dname = self.fresh_from(&LET_NAMES);
            let_in(
                vec![def(&dname, &[], name(&a))],
                apply(&f, vec![name(&dname)]),
            )
        };
        self.ops.push(OpSig {
            name: opname.clone(),
            params: vec![(Ty::Int, false), (Ty::Int, false)],
            ret: Ret::Action,
            level: Level::Action,
            shape: OpShape::HigherOrder,
        });
        self.out_defs
            .push(def_ho(&opname, &[(&f, 1), (&a, 0)], body));
    }
}

impl<'r> Gen<'r> {
    /// Generate one module from the seeded stream.
    pub fn module(rng: &'r mut Rng) -> Module {
        let mut g = Gen::new(rng);
        for i in 0..g.rng.below(3) {
            let mut vars: Vec<Var> = VARS.to_vec();
            g.rng.shuffle(&mut vars);
            let n = 1 + g.rng.below(3) as usize;
            let vt = format!("VT{}", i + 1);
            g.out_defs.push(def(
                &vt,
                &[],
                tuple(vars[..n].iter().map(|v| E::Var(*v)).collect()),
            ));
            g.var_tuples.push(vt);
        }
        let nops = g.rng.below(4) as usize;
        for i in 0..nops {
            g.gen_module_op(i + 1);
        }
        let init = [
            V::Int(g.rng.below(4) as i64),
            V::Set((1..=3).filter(|_| g.rng.pct(40)).map(V::Int).collect()),
            pair_v(1 + g.rng.below(2) as i64, 1 + g.rng.below(2) as i64),
        ];
        let (next, inv) = if g.rng.pct(65) {
            // Stuttering Next; ENABLED in the invariant.
            (
                and(vec![
                    unchanged(Var::X),
                    unchanged(Var::Y),
                    unchanged(Var::Z),
                ]),
                g.gen_inv(),
            )
        } else {
            let next = g.gen_next();
            let inv = if g.rng.pct(50) {
                g.gen_inv()
            } else {
                g.with(false, false, |g| g.gen_bool(1))
            };
            (next, inv)
        };
        Module {
            defs: std::mem::take(&mut g.out_defs),
            init,
            next,
            inv,
        }
    }

    /// A state predicate with at least one ENABLED.
    fn gen_inv(&mut self) -> E {
        self.with(false, true, |g| {
            let core = enabled(g.gen_enabled_operand(2));
            let core = if g.rng.pct(30) { not(core) } else { core };
            match g.rng.below(6) {
                0 | 1 => core,
                2 => {
                    // Under a binder whose name an operator parameter may
                    // reuse (a captured local), in the operand.
                    let (dom, ety) = g.gen_set_of(0);
                    let (pat, locals) = g.binder_for(ety);
                    let body = g.bind(locals, |g| {
                        let e = enabled(g.gen_enabled_operand(2));
                        if g.rng.pct(30) {
                            not(e)
                        } else {
                            e
                        }
                    });
                    if g.rng.pct(50) {
                        forall(pat, dom, body)
                    } else {
                        exists(pat, dom, body)
                    }
                }
                3 => {
                    // A LET outside ENABLED, referenced inside (expansion).
                    g.gen_let(2, |g, _| {
                        let e = enabled(g.gen_enabled_operand(2));
                        if g.rng.pct(30) {
                            not(e)
                        } else {
                            e
                        }
                    })
                }
                4 => or(vec![core, g.gen_bool(1)]),
                _ => and(vec![core, g.gen_bool(1)]),
            }
        })
    }

    /// `Next` with ENABLED as a conjunct, before or after `Next`'s own
    /// assignments.
    fn gen_next(&mut self) -> E {
        let branches = 1 + self.rng.below(2);
        let mut out = Vec::new();
        for _ in 0..branches {
            let b = self.with(true, true, |g| {
                // An action-level LET around the branch, now and then: its
                // definition is expanded inside ENABLED. Its name is chosen
                // first and stays in scope while the branch is generated, so
                // no definition inside the branch reuses it (SANY forbids
                // the redefinition).
                let wrap = if g.rng.pct(20) {
                    let dname = g.fresh_from(&LET_NAMES);
                    let ty = if g.rng.pct(50) { Ty::Int } else { Ty::IntSet };
                    let dbody = g.gen_value(ty, 1);
                    Some((dname, ty, dbody))
                } else {
                    None
                };
                let locals = wrap
                    .iter()
                    .map(|(dname, ty, _)| Local {
                        name: dname.clone(),
                        ty: *ty,
                        kind: Kind::LetDef(Level::Action),
                    })
                    .collect();
                let body = g.bind(locals, |g| {
                    let mut items = vec![
                        eq(prime(x()), g.with(false, false, |g| g.gen_int(1))),
                        if g.rng.pct(50) {
                            eq(prime(y()), g.with(false, false, |g| g.gen_intset(1)))
                        } else {
                            elem(prime(y()), g.with(false, false, |g| g.gen_setset(1)))
                        },
                        if g.rng.pct(50) {
                            unchanged(Var::Z)
                        } else {
                            eq(prime(z()), g.with(false, false, |g| g.gen_pair(1)))
                        },
                    ];
                    // Now and then one variable is assigned through a LET
                    // operator chain instead (`G(q) == H(q)`, `H(r) == r' =
                    // e`, applied to the variable): Next's call-by-name route
                    // for LET operators.
                    if g.rng.pct(20) {
                        let k = g.rng.below(3) as usize;
                        items[k] = g.let_forwarding_chain_for(VARS[k]);
                    }
                    let e = enabled(g.gen_enabled_operand(2));
                    items.push(if g.rng.pct(60) { not(e) } else { e });
                    if g.rng.pct(40) {
                        items.push(g.with(false, false, |g| g.gen_bool(1)));
                    }
                    if wrap.is_some() {
                        let e = enabled(g.gen_enabled_operand(1));
                        items.push(if g.rng.pct(60) { not(e) } else { e });
                    }
                    g.rng.shuffle(&mut items);
                    and(items)
                });
                match wrap {
                    Some((dname, _, dbody)) => let_in(
                        vec![Def {
                            name: dname,
                            params: vec![],
                            arities: Vec::new(),
                            body: dbody,
                        }],
                        body,
                    ),
                    None => body,
                }
            });
            out.push(b);
        }
        if out.len() == 1 {
            out.pop().unwrap()
        } else {
            or(out)
        }
    }
}
