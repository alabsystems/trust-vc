// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Random expressions: what is in scope where one is generated decides which
//! locals, helpers, primes and ENABLED it may use.

use super::expr::{Helper, Name, Rng, BE, IE, NAMES};

#[derive(Clone, Default)]
pub struct Scope {
    /// Locals in scope, innermost last; a new binder takes a name not here,
    /// as TLA+ requires.
    pub locals: Vec<Name>,
    pub primed: bool,
    /// The arity of each helper callable here: `H0` .. `H<n-1>`.
    pub helpers: Vec<usize>,
    /// How many actions an ENABLED may name: `A0` .. `A<n-1>`.
    pub enabled: usize,
}

impl Scope {
    pub fn fresh(&self, r: &mut Rng) -> Option<Name> {
        let free: Vec<Name> = NAMES
            .iter()
            .copied()
            .filter(|name| !self.locals.contains(name))
            .collect();
        (!free.is_empty()).then(|| r.pick(&free))
    }

    pub fn with(&self, name: Name) -> Scope {
        let mut inner = self.clone();
        inner.locals.push(name);
        inner
    }
}

pub fn gen_i(r: &mut Rng, depth: u32, sc: &Scope) -> IE {
    if depth == 0 || r.chance(1, 3) {
        let mut leaves = vec![0, 1, 2, 2];
        if !sc.locals.is_empty() {
            leaves.extend([3, 3]);
        }
        if sc.primed {
            leaves.push(4);
        }
        return match r.pick(&leaves) {
            0 => IE::X,
            1 => IE::Y,
            2 => IE::C(r.range(-3, 5)),
            3 => IE::Local(r.pick(&sc.locals)),
            _ if r.chance(1, 2) => IE::Xp,
            _ => IE::Yp,
        };
    }
    let d = depth - 1;
    let pair = |r: &mut Rng| (Box::new(gen_i(r, d, sc)), Box::new(gen_i(r, d, sc)));
    match r.below(11) {
        0 | 1 => {
            let (a, b) = pair(r);
            IE::Add(a, b)
        }
        2 => {
            let (a, b) = pair(r);
            IE::Sub(a, b)
        }
        3 => {
            let (a, b) = pair(r);
            IE::Mul(a, b)
        }
        4 => IE::Div(Box::new(gen_i(r, d, sc)), r.range(1, 4)),
        5 => IE::Mod(Box::new(gen_i(r, d, sc)), r.range(1, 4)),
        6 => IE::Neg(Box::new(gen_i(r, d, sc))),
        7 => {
            let c = gen_b(r, d, sc);
            let (a, b) = pair(r);
            IE::Ite(Box::new(c), a, b)
        }
        8 | 9 if !sc.helpers.is_empty() => {
            let j = r.below(sc.helpers.len() as u64) as usize;
            let args = (0..sc.helpers[j]).map(|_| gen_i(r, d, sc)).collect();
            IE::Call(j, args)
        }
        _ => match sc.fresh(r) {
            Some(name) => {
                let def = gen_i(r, d, sc);
                let body = gen_i(r, d, &sc.with(name));
                IE::Let(name, Box::new(def), Box::new(body))
            }
            None => IE::Neg(Box::new(gen_i(r, d, sc))),
        },
    }
}

pub fn gen_b(r: &mut Rng, depth: u32, sc: &Scope) -> BE {
    if depth == 0 || r.chance(1, 4) {
        let mut leaves = vec![0, 1, 2];
        if sc.primed {
            leaves.push(3);
        }
        if sc.enabled > 0 {
            leaves.extend([4, 4]);
        }
        return match r.pick(&leaves) {
            0 => BE::B,
            1 if r.chance(1, 2) => BE::T,
            1 => BE::F,
            2 => BE::Lt(gen_i(r, 1, sc), gen_i(r, 1, sc)),
            3 => BE::Bp,
            _ => BE::Enabled(r.below(sc.enabled as u64) as usize),
        };
    }
    let d = depth - 1;
    let ints = |r: &mut Rng| (gen_i(r, d, sc), gen_i(r, d, sc));
    let bools = |r: &mut Rng| (Box::new(gen_b(r, d, sc)), Box::new(gen_b(r, d, sc)));
    match r.below(12) {
        0 => {
            let (a, b) = ints(r);
            BE::Lt(a, b)
        }
        1 => {
            let (a, b) = ints(r);
            BE::Le(a, b)
        }
        2 => {
            let (a, b) = ints(r);
            BE::Eq(a, b)
        }
        3 => {
            let (a, b) = ints(r);
            BE::Ne(a, b)
        }
        4 => BE::Not(Box::new(gen_b(r, d, sc))),
        5 => {
            let (p, q) = bools(r);
            BE::And(p, q)
        }
        6 => {
            let (p, q) = bools(r);
            BE::Or(p, q)
        }
        7 => {
            let (p, q) = bools(r);
            BE::Imp(p, q)
        }
        8 => {
            let (p, q) = bools(r);
            BE::Iff(p, q)
        }
        9 if sc.fresh(r).is_some() => {
            let name = sc.fresh(r).expect("checked just above");
            let lo = r.range(-2, 2);
            let hi = lo + r.range(0, 3);
            BE::Ex(name, lo, hi, Box::new(gen_b(r, d, &sc.with(name))))
        }
        _ => {
            let n = r.range(1, 3);
            let e = gen_i(r, d, sc);
            BE::In(e, (0..n).map(|_| gen_i(r, d.min(1), sc)).collect())
        }
    }
}

/// `n` helpers, each over one or two parameters named from [`NAMES`], each
/// able to call the ones before it.
pub fn gen_helpers(r: &mut Rng, n: usize) -> Vec<Helper> {
    let mut helpers: Vec<Helper> = Vec::new();
    for _ in 0..n {
        let mut sc = Scope {
            helpers: helpers.iter().map(|h| h.params.len()).collect(),
            ..Scope::default()
        };
        for _ in 0..r.range(1, 2) {
            if let Some(name) = sc.fresh(r) {
                sc.locals.push(name);
            }
        }
        let body = gen_i(r, 2, &sc);
        helpers.push(Helper {
            params: sc.locals,
            body,
        });
    }
    helpers
}
