// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The actions of a generated spec: their successors, computed here, and
//! their TLA+ text.

use std::collections::BTreeSet;

use super::expr::{
    ev_b, ev_i, free_b, free_i, int, pr_b, pr_i, Ctx, Env, Helper, Name, Rng, St, BE, C_MAX, IE,
    NAMES,
};
use super::gen::{gen_b, gen_i, Scope};

/// `(e % m) - k`: an assigned value, kept in a finite range.
#[derive(Clone, Debug)]
pub struct Reduce {
    pub e: IE,
    pub m: i64,
    pub k: i64,
}

/// A set filter a variable is drawn from.
#[derive(Clone, Debug)]
pub enum Filter {
    /// `{z \in lo..hi : pred}`, assigned as `v' \in` it. ty builds a filter
    /// over an interval whole, where it is written.
    Ints { lo: i64, hi: i64, pred: BE },
    /// `{s \in SUBSET (lo..hi) : (in_1 \in s) /\ ~(out_1 \in s) /\ extra}`,
    /// with `0 <= lo <= hi <= C_MAX`: an integer variable is assigned as
    /// `\E t \in` it `: v' = Cardinality(t)`, and `c` as `c' \in` it. ty
    /// keeps a filter over SUBSET lazy and tests its predicate member by
    /// member; over `(SUBSET (lo..hi)) \cup {{}}` (`cup`, the same set) it
    /// builds it whole where it is drawn from.
    Subsets {
        lo: i64,
        hi: i64,
        inside: Vec<IE>,
        outside: Vec<IE>,
        extra: BE,
        cup: bool,
    },
    /// `{<<p, q>> \in (lo..hi) \X (lo..hi) : pred}`, a tuple pattern whose
    /// components `pred` reads, assigned as `\E t \in` it
    /// `: v' = t[1] - t[2]`. ty keeps a filter over `\X` lazy; with `cup` the
    /// base is `((lo..hi) \X (lo..hi)) \cup {<<lo, lo>>}`, the same set, built
    /// whole.
    Pairs {
        lo: i64,
        hi: i64,
        names: [Name; 2],
        pred: BE,
        cup: bool,
    },
}

/// `Sel<j>(param) == <filter>`.
#[derive(Clone, Debug)]
pub struct Sel {
    pub param: Name,
    pub filter: Filter,
}

#[derive(Clone, Debug)]
pub enum Assign {
    Keep,
    Set(Reduce),
    Inline(Filter),
    /// From `Sel<j>(arg)`.
    Call(usize, IE),
    /// `c' \in Q<j>'`, or `c' \in (<filter>)'` for an inline one: a filter
    /// over `x`, `y` and `b` read in the successor. `c` only, which is
    /// assigned last.
    Primed(usize),
}

#[derive(Clone, Debug)]
pub struct Action {
    /// `\E name \in lo..hi : ...` around the whole action.
    pub ex: Option<(Name, i64, i64)>,
    pub guard: BE,
    pub x: Assign,
    pub y: Assign,
    pub b: Option<BE>,
    /// `Keep`, a `Subsets` filter (`Inline`, or a selector's by `Call`), or
    /// `Primed`, after every other variable is assigned.
    pub c: Assign,
    /// Spell an unchanged variable `x' = x` instead of `UNCHANGED x`.
    pub explicit_frame: bool,
}

impl Action {
    /// Whether the action draws from a filter whose predicate reads a name a
    /// caller's binder may also bind: a selector's parameter, or a tuple
    /// pattern's components.
    pub fn draws_from_a_capturable_filter(&self) -> bool {
        [&self.x, &self.y, &self.c].iter().any(|assign| {
            matches!(
                assign,
                Assign::Call(..) | Assign::Inline(Filter::Pairs { .. })
            )
        })
    }
}

/// A `Subsets` filter over `x`, `y`, `b` and the helpers that `c` is drawn
/// from in the successor: `Q<j> == <filter>` and `c' \in Q<j>'`, or, when
/// `inline`, `c' \in (<filter>)'`. ty materializes the value of a zero-arity
/// operator where it is read, so only the inline form reaches ENABLED's walk
/// of a lazy filter.
#[derive(Clone, Debug)]
pub struct Primed {
    pub filter: Filter,
    pub inline: bool,
}

pub struct Model {
    pub helpers: Vec<Helper>,
    pub sels: Vec<Sel>,
    pub primed: Vec<Primed>,
    pub actions: Vec<Action>,
}

const NO_ENABLED: &dyn Fn(usize, St) -> bool = &|_, _| false;

impl Model {
    pub fn generate(r: &mut Rng) -> Model {
        let n_helpers = r.range(0, 2) as usize;
        let helpers = super::gen::gen_helpers(r, n_helpers);
        let arities: Vec<usize> = helpers.iter().map(|h| h.params.len()).collect();
        let n_sels = r.range(0, 2);
        let sels: Vec<Sel> = (0..n_sels)
            .map(|_| {
                let param = r.pick(&NAMES);
                let sc = Scope {
                    locals: vec![param],
                    helpers: arities.clone(),
                    ..Scope::default()
                };
                Sel {
                    param,
                    filter: gen_filter(r, &sc),
                }
            })
            .collect();
        let primed: Vec<Primed> = (0..r.range(0, 2))
            .map(|_| {
                let sc = Scope {
                    helpers: arities.clone(),
                    ..Scope::default()
                };
                Primed {
                    filter: gen_subsets(r, &sc),
                    inline: r.chance(2, 3),
                }
            })
            .collect();
        let params: Vec<Name> = sels.iter().map(|sel| sel.param).collect();
        let subset_sels: Vec<usize> = (0..sels.len())
            .filter(|&j| matches!(sels[j].filter, Filter::Subsets { .. }))
            .collect();
        // An inline primed filter is printed inside the action that draws
        // from it, so an action's `\E` binder may not take a name the filter
        // binds (SANY: "Multiply-defined symbol").
        let inline_bound: Vec<Name> = NAMES
            .iter()
            .copied()
            .filter(|name| {
                primed.iter().filter(|p| p.inline).any(|p| {
                    pr_filter(&p.filter)
                        .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
                        .any(|word| word == *name)
                })
            })
            .collect();
        let actions = (0..r.range(1, 3))
            .map(|_| {
                gen_action(
                    r,
                    &arities,
                    &params,
                    &subset_sels,
                    primed.len(),
                    &inline_bound,
                )
            })
            .collect();
        Model {
            helpers,
            sels,
            primed,
            actions,
        }
    }

    pub fn ctx<'a>(&'a self, enabled: &'a dyn Fn(usize, St) -> bool) -> Ctx<'a> {
        Ctx {
            helpers: &self.helpers,
            enabled,
        }
    }

    /// The states action `i` steps to from `s`.
    pub fn successors(&self, i: usize, s: St, out: &mut Vec<St>) {
        let action = &self.actions[i];
        let cx = self.ctx(NO_ENABLED);
        let binders: Vec<Vec<(Name, i64)>> = match action.ex {
            Some((name, lo, hi)) => (lo..=hi).map(|v| vec![(name, v)]).collect(),
            None => vec![Vec::new()],
        };
        for locals in binders {
            let mut env = Env { s, t: None, locals };
            if !ev_b(&action.guard, &cx, &mut env) {
                continue;
            }
            let xs = self.values(&action.x, s.x, &cx, &mut env);
            let ys = self.values(&action.y, s.y, &cx, &mut env);
            let b = action.b.as_ref().map_or(s.b, |p| ev_b(p, &cx, &mut env));
            let drawn_now = match action.c {
                Assign::Primed(_) => Vec::new(),
                _ => self.masks(&action.c, s.c, &cx, &mut env),
            };
            for &x in &xs {
                for &y in &ys {
                    let cs = match action.c {
                        // `Q<j>'` reads the successor's `x`, `y` and `b`.
                        Assign::Primed(j) => {
                            let mut next = Env::state(St { x, y, b, c: s.c });
                            subset_masks(&self.primed[j].filter, &cx, &mut next)
                        }
                        _ => drawn_now.clone(),
                    };
                    for &c in &cs {
                        out.push(St { x, y, b, c });
                    }
                }
            }
        }
    }

    pub fn enabled(&self, i: usize, s: St) -> bool {
        let mut out = Vec::new();
        self.successors(i, s, &mut out);
        !out.is_empty()
    }

    /// The values an integer variable assigned by `assign` may take.
    fn values(&self, assign: &Assign, old: i64, cx: &Ctx, env: &mut Env) -> Vec<i64> {
        match assign {
            Assign::Keep => vec![old],
            Assign::Set(reduce) => vec![ev_i(&reduce.e, cx, env).rem_euclid(reduce.m) - reduce.k],
            Assign::Inline(filter) => drawn(filter, cx, env),
            Assign::Call(j, arg) => {
                let sel = &self.sels[*j];
                let mut inner = self.call_env(sel, arg, cx, env);
                drawn(&sel.filter, cx, &mut inner)
            }
            Assign::Primed(_) => unreachable!("only `c` is drawn from `Q<j>'`"),
        }
    }

    /// The values `c` assigned by `assign` (not `Primed`) may take.
    fn masks(&self, assign: &Assign, old: u8, cx: &Ctx, env: &mut Env) -> Vec<u8> {
        match assign {
            Assign::Keep => vec![old],
            Assign::Inline(filter) => subset_masks(filter, cx, env),
            Assign::Call(j, arg) => {
                let sel = &self.sels[*j];
                let mut inner = self.call_env(sel, arg, cx, env);
                subset_masks(&sel.filter, cx, &mut inner)
            }
            Assign::Set(_) | Assign::Primed(_) => unreachable!("not an assignment of `c`"),
        }
    }

    /// The state with only `sel`'s parameter bound, to `arg`.
    fn call_env(&self, sel: &Sel, arg: &IE, cx: &Ctx, env: &mut Env) -> Env {
        let value = ev_i(arg, cx, env);
        Env {
            s: env.s,
            t: None,
            locals: vec![(sel.param, value)],
        }
    }

    /// Whether some filter's predicate reads a local it does not bind.
    pub fn has_open_filter(&self) -> bool {
        let inline = |assign: &Assign| matches!(assign, Assign::Inline(f) if is_open(f));
        self.sels.iter().any(|sel| is_open(&sel.filter))
            || self
                .actions
                .iter()
                .any(|action| inline(&action.x) || inline(&action.y) || inline(&action.c))
    }

    /// The names a binder around ENABLED may share with a filter's own
    /// locals: selector parameters and tuple pattern components.
    pub fn capturable_names(&self) -> Vec<Name> {
        let mut names: Vec<Name> = self.sels.iter().map(|sel| sel.param).collect();
        let filters = self.sels.iter().map(|sel| &sel.filter).chain(
            self.actions
                .iter()
                .flat_map(|action| [&action.x, &action.y])
                .filter_map(|assign| match assign {
                    Assign::Inline(filter) => Some(filter),
                    _ => None,
                }),
        );
        for filter in filters {
            if let Filter::Pairs { names: pair, .. } = filter {
                names.extend(pair);
            }
        }
        names.sort_unstable();
        names.dedup();
        names
    }

    /// Whether some action draws `c'` from an operator read in the successor.
    pub fn has_primed_filter(&self) -> bool {
        self.actions
            .iter()
            .any(|action| matches!(action.c, Assign::Primed(_)))
    }

    /// Whether some filter has a tuple pattern.
    pub fn has_pair_filter(&self) -> bool {
        let pairs = |assign: &Assign| matches!(assign, Assign::Inline(Filter::Pairs { .. }));
        self.sels
            .iter()
            .any(|sel| matches!(sel.filter, Filter::Pairs { .. }))
            || self
                .actions
                .iter()
                .any(|action| pairs(&action.x) || pairs(&action.y))
    }

    /// The helper, selector, primed-operator and action definitions.
    pub fn print(&self) -> String {
        let mut text = String::new();
        for (j, helper) in self.helpers.iter().enumerate() {
            let params = helper.params.join(", ");
            text.push_str(&format!("H{j}({params}) == {}\n", pr_i(&helper.body)));
        }
        for (j, sel) in self.sels.iter().enumerate() {
            text.push_str(&format!(
                "Sel{j}({}) == {}\n",
                sel.param,
                pr_filter(&sel.filter)
            ));
        }
        for (j, primed) in self.primed.iter().enumerate() {
            if !primed.inline {
                text.push_str(&format!("Q{j} == {}\n", pr_filter(&primed.filter)));
            }
        }
        for (i, action) in self.actions.iter().enumerate() {
            text.push_str(&self.print_action(action, i));
        }
        text
    }

    fn print_action(&self, action: &Action, i: usize) -> String {
        let frame = |var: &str| {
            if action.explicit_frame {
                format!("{var}' = {var}")
            } else {
                format!("UNCHANGED {var}")
            }
        };
        let draw = |var: &str, filter: &Filter, set: String| match filter {
            Filter::Ints { .. } => format!("{var}' \\in {set}"),
            Filter::Subsets { .. } if var == "c" => format!("{var}' \\in {set}"),
            Filter::Subsets { .. } => format!("\\E t \\in {set} : {var}' = Cardinality(t)"),
            Filter::Pairs { .. } => format!("\\E t \\in {set} : {var}' = (t[1] - t[2])"),
        };
        let assign = |var: &str, assign: &Assign| match assign {
            Assign::Keep => frame(var),
            Assign::Set(reduce) if reduce.k == 0 => {
                format!("{var}' = ({} % {})", pr_i(&reduce.e), reduce.m)
            }
            Assign::Set(reduce) => {
                format!(
                    "{var}' = (({} % {}) - {})",
                    pr_i(&reduce.e),
                    reduce.m,
                    reduce.k
                )
            }
            Assign::Inline(filter) => draw(var, filter, pr_filter(filter)),
            Assign::Call(j, arg) => {
                draw(var, &self.sels[*j].filter, format!("Sel{j}({})", pr_i(arg)))
            }
            Assign::Primed(j) => {
                let primed = &self.primed[*j];
                let set = if primed.inline {
                    format!("({})'", pr_filter(&primed.filter))
                } else {
                    format!("Q{j}'")
                };
                draw(var, &primed.filter, set)
            }
        };
        let clauses = [
            pr_b(&action.guard),
            assign("x", &action.x),
            assign("y", &action.y),
            match &action.b {
                Some(p) => format!("b' = {}", pr_b(p)),
                None => frame("b"),
            },
            assign("c", &action.c),
        ];
        let indent = if action.ex.is_some() { "    " } else { "  " };
        let body: Vec<String> = clauses
            .iter()
            .map(|clause| format!("{indent}/\\ {clause}"))
            .collect();
        match action.ex {
            Some((name, lo, hi)) => format!(
                "A{i} ==\n  \\E {name} \\in {}..{} :\n{}\n",
                int(lo),
                int(hi),
                body.join("\n")
            ),
            None => format!("A{i} ==\n{}\n", body.join("\n")),
        }
    }
}

/// The integer values a variable drawn from `filter` may take.
fn drawn(filter: &Filter, cx: &Ctx, env: &mut Env) -> Vec<i64> {
    match filter {
        Filter::Ints { lo, hi, pred } => (*lo..=*hi)
            .filter(|&z| {
                env.locals.push(("z", z));
                let keep = ev_b(pred, cx, env);
                env.locals.pop();
                keep
            })
            .collect(),
        Filter::Subsets { .. } => subset_masks(filter, cx, env)
            .into_iter()
            .map(|mask| i64::from(mask.count_ones()))
            .collect(),
        Filter::Pairs {
            lo,
            hi,
            names: [p, q],
            pred,
            ..
        } => {
            let mut values = Vec::new();
            for first in *lo..=*hi {
                for second in *lo..=*hi {
                    env.locals.push((p, first));
                    env.locals.push((q, second));
                    if ev_b(pred, cx, env) {
                        values.push(first - second);
                    }
                    env.locals.pop();
                    env.locals.pop();
                }
            }
            values
        }
    }
}

/// The members of a `Subsets` filter, bit `v` for element `v`.
fn subset_masks(filter: &Filter, cx: &Ctx, env: &mut Env) -> Vec<u8> {
    let Filter::Subsets {
        lo,
        hi,
        inside,
        outside,
        extra,
        ..
    } = filter
    else {
        unreachable!("`c` and `Q<j>` are drawn from SUBSET filters only");
    };
    let inside: Vec<i64> = inside.iter().map(|e| ev_i(e, cx, env)).collect();
    let outside: Vec<i64> = outside.iter().map(|e| ev_i(e, cx, env)).collect();
    if !ev_b(extra, cx, env) {
        return Vec::new();
    }
    let has = |mask: u8, v: i64| (*lo..=*hi).contains(&v) && mask & (1 << v) != 0;
    let range: u8 = (*lo..=*hi).map(|v| 1u8 << v).sum();
    (0..=range)
        .filter(|&mask| mask & !range == 0)
        .filter(|&mask| {
            inside.iter().all(|&v| has(mask, v)) && !outside.iter().any(|&v| has(mask, v))
        })
        .collect()
}

fn is_open(filter: &Filter) -> bool {
    let mut free = BTreeSet::new();
    match filter {
        Filter::Ints { pred, .. } => free_b(pred, &mut vec!["z"], &mut free),
        Filter::Subsets {
            inside,
            outside,
            extra,
            ..
        } => {
            for e in inside.iter().chain(outside) {
                free_i(e, &mut Vec::new(), &mut free);
            }
            free_b(extra, &mut Vec::new(), &mut free);
        }
        Filter::Pairs {
            names: [p, q],
            pred,
            ..
        } => free_b(pred, &mut vec![*p, *q], &mut free),
    }
    !free.is_empty()
}

fn pr_filter(filter: &Filter) -> String {
    match filter {
        Filter::Ints { lo, hi, pred } => {
            format!("{{z \\in {}..{} : {}}}", int(*lo), int(*hi), pr_b(pred))
        }
        Filter::Subsets {
            lo,
            hi,
            inside,
            outside,
            extra,
            cup,
        } => {
            let mut conjuncts: Vec<String> = inside
                .iter()
                .map(|e| format!("({} \\in s)", pr_i(e)))
                .collect();
            conjuncts.extend(outside.iter().map(|e| format!("~({} \\in s)", pr_i(e))));
            conjuncts.push(pr_b(extra));
            let base = format!("SUBSET ({}..{})", int(*lo), int(*hi));
            let base = if *cup {
                format!("({base}) \\cup {{{{}}}}")
            } else {
                base
            };
            format!("{{s \\in {base} : {}}}", conjuncts.join(" /\\ "))
        }
        Filter::Pairs {
            lo,
            hi,
            names: [p, q],
            pred,
            cup,
        } => {
            let range = format!("({}..{})", int(*lo), int(*hi));
            let base = format!("{range} \\X {range}");
            let base = if *cup {
                format!("({base}) \\cup {{<<{lo}, {lo}>>}}", lo = int(*lo))
            } else {
                base
            };
            format!("{{<<{p}, {q}>> \\in {base} : {}}}", pr_b(pred))
        }
    }
}

/// A filter whose predicate reads its own variables and, sometimes, the
/// locals of `sc`.
fn gen_filter(r: &mut Rng, sc: &Scope) -> Filter {
    match r.below(6) {
        0 | 1 => {
            let lo = r.range(-1, 2);
            Filter::Ints {
                lo,
                hi: lo + r.range(0, 3),
                pred: gen_b(r, 2, &sc.with("z")),
            }
        }
        2 => gen_pairs(r, sc).unwrap_or_else(|| gen_subsets(r, sc)),
        _ => gen_subsets(r, sc),
    }
}

/// `{s \in SUBSET (lo..hi) : ...}` with `0 <= lo <= hi <= C_MAX`.
fn gen_subsets(r: &mut Rng, sc: &Scope) -> Filter {
    let lo = r.range(0, 1);
    let hi = (lo + r.range(0, 2)).min(C_MAX);
    let members = |r: &mut Rng| {
        (0..r.range(0, 2))
            .map(|_| gen_i(r, 1, sc))
            .collect::<Vec<_>>()
    };
    let mut inside = members(r);
    // Often test a local itself: the shape ty's ENABLED search misread.
    if !sc.locals.is_empty() && r.chance(1, 2) {
        inside.push(IE::Local(r.pick(&sc.locals)));
    }
    Filter::Subsets {
        lo,
        hi,
        inside,
        outside: members(r),
        extra: if r.chance(1, 2) {
            BE::T
        } else {
            gen_b(r, 1, sc)
        },
        cup: r.chance(1, 3),
    }
}

/// `{<<p, q>> \in S : pred}`, its components named from what is free here,
/// so that a caller's binder often has a component's name; `None` when fewer
/// than two names are free.
fn gen_pairs(r: &mut Rng, sc: &Scope) -> Option<Filter> {
    let p = sc.fresh(r)?;
    let q = sc.with(p).fresh(r)?;
    let lo = r.range(-1, 1);
    let mut pred = gen_b(r, 2, &sc.with(p).with(q));
    // Often test a component itself.
    if r.chance(1, 2) {
        let component = IE::Local(if r.chance(1, 2) { p } else { q });
        pred = BE::And(
            Box::new(BE::Le(component, IE::C(r.range(-1, 2)))),
            Box::new(pred),
        );
    }
    Some(Filter::Pairs {
        lo,
        hi: lo + r.range(0, 2),
        names: [p, q],
        pred,
        cup: r.chance(1, 3),
    })
}

/// An action; its `\E` binder, when it has one, often takes the name of a
/// selector's parameter.
fn gen_action(
    r: &mut Rng,
    helpers: &[usize],
    sel_params: &[Name],
    subset_sels: &[usize],
    primed: usize,
    inline_bound: &[Name],
) -> Action {
    let sels = sel_params.len();
    // The draws are the ones every earlier revision made, so a seed still
    // generates the same cases; only a binder that an inline filter of this
    // model binds too is renamed, to the first name nothing binds.
    let ex = r.chance(1, 3).then(|| {
        let lo = r.range(-1, 1);
        let drawn = if sels > 0 && r.chance(1, 2) {
            r.pick(sel_params)
        } else {
            r.pick(&NAMES)
        };
        let name = if inline_bound.contains(&drawn) {
            NAMES
                .iter()
                .copied()
                .find(|name| !inline_bound.contains(name))
                .unwrap_or("j")
        } else {
            drawn
        };
        (name, lo, lo + r.range(0, 2))
    });
    let sc = Scope {
        locals: ex.iter().map(|(name, _, _)| *name).collect(),
        helpers: helpers.to_vec(),
        ..Scope::default()
    };
    let guard = if r.chance(1, 4) {
        BE::T
    } else {
        gen_b(r, 2, &sc)
    };
    let assign = |r: &mut Rng, keep: u64| match r.below(8) {
        n if n < keep => Assign::Keep,
        n if n < 5 => Assign::Set(Reduce {
            e: gen_i(r, 2, &sc),
            m: r.range(2, 6),
            k: r.range(0, 2),
        }),
        5 | 6 if sels > 0 => Assign::Call(r.below(sels as u64) as usize, gen_i(r, 1, &sc)),
        _ => Assign::Inline(gen_filter(r, &sc)),
    };
    let x = assign(r, 2);
    let y = assign(r, 3);
    let b = r.chance(1, 2).then(|| gen_b(r, 2, &sc));
    let c = match r.below(10) {
        6 | 7 if primed > 0 => Assign::Primed(r.below(primed as u64) as usize),
        8 | 9 if !subset_sels.is_empty() => Assign::Call(r.pick(subset_sels), gen_i(r, 1, &sc)),
        n if n >= 4 => Assign::Inline(gen_subsets(r, &sc)),
        _ => Assign::Keep,
    };
    Action {
        ex,
        guard,
        x,
        y,
        b,
        c,
        explicit_frame: r.chance(1, 3),
    }
}
