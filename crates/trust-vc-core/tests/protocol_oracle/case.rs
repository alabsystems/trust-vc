// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! One random raw protocol obligation and its verdict, computed here by
//! explicit-state search: the exact reachable set, deadlocks, and each
//! invariant and property under TLC's semantics (a behavior of
//! `Init /\ [][Next]_vars` may stutter forever).

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt::Write as _;

use super::expr::{ev_b, int, pr_b, pr_set, Env, Rng, St, BE, C_MAX};
use super::gen::{gen_b, Scope};
use super::model::Model;

pub struct Case {
    pub spec: String,
    pub config: String,
    /// The obligations the oracle finds violated: `TypeOK`, `Inv`, `Prop`,
    /// `deadlock_freedom`.
    pub violated: BTreeSet<&'static str>,
    /// The spec evaluates ENABLED (directly, or through WF) and some filter's
    /// predicate reads a local it does not bind: the shape an older ty's
    /// ENABLED search misread, which the in-process lane refused.
    pub enabled_open_filter: bool,
    pub reachable: usize,
    pub kind: String,
}

fn state_pred(s: &St) -> String {
    let b = if s.b { "TRUE" } else { "FALSE" };
    format!(
        "(x = {} /\\ y = {} /\\ b = {b} /\\ c = {})",
        int(s.x),
        int(s.y),
        pr_set(s.c)
    )
}

/// Under `WF_vars(Next)`, is there a behavior from `starts` that stays in
/// `region` forever? It ends stuttering at a region state with no
/// successor but itself, or on a cycle of region states with a real step.
fn fair_escape(
    reach: &[St],
    edges: &[(St, St)],
    starts: &[St],
    region: &dyn Fn(&St) -> bool,
) -> bool {
    let inside: BTreeSet<St> = reach.iter().copied().filter(|s| region(s)).collect();
    let mut succ: BTreeMap<St, Vec<St>> = BTreeMap::new();
    let mut moves: BTreeSet<St> = BTreeSet::new();
    for (s, t) in edges {
        if s != t {
            moves.insert(*s);
            if inside.contains(s) && inside.contains(t) {
                succ.entry(*s).or_default().push(*t);
            }
        }
    }
    let reach_from = |s: St| {
        let mut seen = BTreeSet::new();
        let mut stack: Vec<St> = succ.get(&s).cloned().unwrap_or_default();
        while let Some(u) = stack.pop() {
            if seen.insert(u) {
                stack.extend(succ.get(&u).cloned().unwrap_or_default());
            }
        }
        seen
    };
    let stuck: BTreeSet<St> = inside
        .iter()
        .copied()
        .filter(|s| !moves.contains(s) || reach_from(*s).contains(s))
        .collect();
    starts
        .iter()
        .filter(|s| inside.contains(s))
        .any(|s| stuck.contains(s) || reach_from(*s).iter().any(|u| stuck.contains(u)))
}

pub fn gen_case(r: &mut Rng) -> Case {
    let model = Model::generate(r);
    let n_actions = model.actions.len();
    let set_of = |r: &mut Rng| {
        let vals: BTreeSet<i64> = (0..r.range(1, 3)).map(|_| r.range(-2, 4)).collect();
        vals.into_iter().collect::<Vec<_>>()
    };
    let xs = set_of(r);
    let ys = set_of(r);
    let bs: Vec<bool> = match r.below(3) {
        0 => vec![false],
        1 => vec![true],
        _ => vec![false, true],
    };
    let full = (1u64 << (C_MAX + 1)) - 1;
    let cs: Vec<u8> = (0..r.range(1, 2))
        .map(|_| r.below(full + 1) as u8)
        .collect::<BTreeSet<u8>>()
        .into_iter()
        .collect();
    // The macro lane's shape: `Next` ends in a stutter disjunct.
    let stutter = r.chance(1, 4);

    let mut init = Vec::new();
    for &x in &xs {
        for &y in &ys {
            for &b in &bs {
                for &c in &cs {
                    init.push(St { x, y, b, c });
                }
            }
        }
    }
    let mut seen: BTreeSet<St> = init.iter().copied().collect();
    let mut queue: VecDeque<St> = init.iter().copied().collect();
    let mut edges: Vec<(St, St)> = Vec::new();
    let mut deadlock = false;
    while let Some(s) = queue.pop_front() {
        let mut succ = Vec::new();
        for i in 0..n_actions {
            model.successors(i, s, &mut succ);
        }
        if stutter {
            succ.push(s);
        }
        deadlock |= succ.is_empty();
        for t in succ {
            edges.push((s, t));
            if seen.insert(t) {
                queue.push_back(t);
            }
        }
    }
    let reach: Vec<St> = seen.iter().copied().collect();
    let enabled = |i: usize, s: St| model.enabled(i, s);
    let cx = model.ctx(&enabled);
    let sat = |p: &BE, s: &St| ev_b(p, &cx, &mut Env::state(*s));
    let everywhere = |p: &BE| reach.iter().all(|s| sat(p, s));

    let state_sc = Scope {
        helpers: model.helpers.iter().map(|h| h.params.len()).collect(),
        enabled: n_actions,
        ..Scope::default()
    };
    let inv_kind = r.below(7);
    let (inv, inv_holds): (String, bool) = match inv_kind {
        0 | 1 => {
            let p = gen_b(r, 3, &state_sc);
            (pr_b(&p), everywhere(&p))
        }
        2 => {
            // `\A k \in lo..hi : P`, written `~\E k : ~P`, where P may read
            // `k` and name the actions.
            let name = r.pick(&super::expr::NAMES);
            let lo = r.range(-1, 2);
            let p = gen_b(r, 2, &state_sc.with(name));
            let all = BE::Not(Box::new(BE::Ex(
                name,
                lo,
                lo + r.range(0, 2),
                Box::new(BE::Not(Box::new(p))),
            )));
            (pr_b(&all), everywhere(&all))
        }
        6 if !model.capturable_names().is_empty() => {
            // `\A <name> \in lo..hi : ENABLED A<i>`, the binder named like a
            // selector's parameter or a tuple pattern's component.
            let name = r.pick(&model.capturable_names());
            let calls: Vec<usize> = (0..n_actions)
                .filter(|&i| model.actions[i].draws_from_a_capturable_filter())
                .collect();
            let action = if calls.is_empty() {
                r.below(n_actions as u64) as usize
            } else {
                r.pick(&calls)
            };
            let lo = r.range(-1, 2);
            let all = BE::Not(Box::new(BE::Ex(
                name,
                lo,
                lo + r.range(0, 1),
                Box::new(BE::Not(Box::new(BE::Enabled(action)))),
            )));
            (pr_b(&all), everywhere(&all))
        }
        3 | 6 => {
            // Exclude a random reachable state: violated.
            let s = reach[r.below(reach.len() as u64) as usize];
            (format!("~{}", state_pred(&s)), false)
        }
        _ => {
            // The exact reachable set as a disjunction, or it minus one.
            let drop = (inv_kind == 5).then(|| r.below(reach.len() as u64) as usize);
            let members: Vec<String> = reach
                .iter()
                .enumerate()
                .filter(|(i, _)| Some(*i) != drop)
                .map(|(_, s)| state_pred(s))
                .collect();
            let text = if members.is_empty() {
                "FALSE".to_string()
            } else {
                members.join(" \\/ ")
            };
            (text, drop.is_none())
        }
    };
    let inv_enabled = inv.contains("ENABLED");

    let action_sc = Scope {
        primed: true,
        enabled: 0,
        ..state_sc.clone()
    };
    let p = gen_b(r, 2, &state_sc);
    let q = gen_b(r, 2, &state_sc);
    let fair =
        |region: &dyn Fn(&St) -> bool, starts: &[St]| !fair_escape(&reach, &edges, starts, region);
    let (prop, prop_holds, prop_kind): (Option<String>, bool, &str) = match r.below(11) {
        0..=2 => (None, true, "none"),
        3 => (Some(format!("[]{}", pr_b(&p))), everywhere(&p), "always"),
        4 => {
            let a = gen_b(r, 2, &action_sc);
            let holds = edges.iter().all(|(s, t)| {
                let mut env = Env::state(*s);
                env.t = Some(*t);
                s == t || ev_b(&a, &cx, &mut env)
            });
            (Some(format!("[][{}]_vars", pr_b(&a))), holds, "action")
        }
        5 => {
            // Each initial state may stutter forever.
            let holds = init.iter().all(|s| sat(&p, s));
            (Some(format!("<>{}", pr_b(&p))), holds, "eventually")
        }
        6 => (
            Some(format!("[]<>{}", pr_b(&p))),
            everywhere(&p),
            "infoften",
        ),
        7 => {
            let holds = reach.iter().all(|s| !sat(&p, s) || sat(&q, s));
            let text = format!("({}) ~> ({})", pr_b(&p), pr_b(&q));
            (Some(text), holds, "leadsto")
        }
        8 => {
            let holds = fair(&|s| !sat(&p, s), &init);
            let text = format!("WF_vars(Next) => <>{}", pr_b(&p));
            (Some(text), holds, "wf-eventually")
        }
        9 => {
            let holds = fair(&|s| !sat(&p, s), &reach);
            let text = format!("WF_vars(Next) => []<>{}", pr_b(&p));
            (Some(text), holds, "wf-infoften")
        }
        _ => {
            let starts: Vec<St> = reach.iter().copied().filter(|s| sat(&p, s)).collect();
            let holds = fair(&|s| !sat(&q, s), &starts);
            let text = format!("WF_vars(Next) => (({}) ~> ({}))", pr_b(&p), pr_b(&q));
            (Some(text), holds, "wf-leadsto")
        }
    };
    let prop_enabled = prop
        .as_deref()
        .is_some_and(|text| text.contains("ENABLED") || text.contains("WF_"));

    // A TypeOK over the reachable value ranges, sometimes one too tight.
    let typeok = r.chance(1, 2).then(|| {
        let lo_hi = |f: &dyn Fn(&St) -> i64| {
            let values = reach.iter().map(f);
            (values.clone().min().unwrap_or(0), values.max().unwrap_or(0))
        };
        let (mut xl, mut xh) = lo_hi(&|s| s.x);
        let (mut yl, mut yh) = lo_hi(&|s| s.y);
        match r.below(6) {
            0 => xl += 1,
            1 => xh -= 1,
            2 => yl += 1,
            3 => yh -= 1,
            _ => {}
        }
        let holds = reach
            .iter()
            .all(|s| xl <= s.x && s.x <= xh && yl <= s.y && s.y <= yh);
        let text = format!(
            "x \\in {}..{} /\\ y \\in {}..{} /\\ b \\in BOOLEAN /\\ c \\in SUBSET (0..{C_MAX})",
            int(xl),
            int(xh),
            int(yl),
            int(yh)
        );
        (text, holds)
    });
    let check_deadlock = r.chance(1, 3);

    let mut violated = BTreeSet::new();
    if let Some((_, false)) = &typeok {
        violated.insert("TypeOK");
    }
    if !inv_holds {
        violated.insert("Inv");
    }
    if !prop_holds {
        violated.insert("Prop");
    }
    if check_deadlock && deadlock {
        violated.insert("deadlock_freedom");
    }

    let set = |vals: Vec<String>| format!("{{{}}}", vals.join(", "));
    let bools = bs
        .iter()
        .map(|v| if *v { "TRUE" } else { "FALSE" }.to_string());
    let mut spec =
        String::from("---- MODULE F ----\nEXTENDS Integers, FiniteSets\nVARIABLES x, y, b, c\n");
    spec.push_str("vars == <<x, y, b, c>>\n");
    let _ = writeln!(
        spec,
        "Init ==\n  /\\ x \\in {}\n  /\\ y \\in {}\n  /\\ b \\in {}\n  /\\ c \\in {}",
        set(xs.iter().map(|v| int(*v)).collect()),
        set(ys.iter().map(|v| int(*v)).collect()),
        set(bools.collect()),
        set(cs.iter().map(|mask| pr_set(*mask)).collect())
    );
    spec.push_str(&model.print());
    let disjuncts: Vec<String> = (0..n_actions).map(|i| format!("A{i}")).collect();
    let stutter_step = if stutter {
        " \\/ UNCHANGED <<x, y, b, c>>"
    } else {
        ""
    };
    let _ = writeln!(spec, "Next == {}{stutter_step}", disjuncts.join(" \\/ "));
    if let Some((text, _)) = &typeok {
        let _ = writeln!(spec, "TypeOK == {text}");
    }
    let _ = writeln!(spec, "Inv == {inv}");
    if let Some(text) = &prop {
        let _ = writeln!(spec, "Prop == {text}");
    }
    spec.push_str("====\n");

    let mut config = String::from("INIT Init\nNEXT Next\n");
    if typeok.is_some() {
        config.push_str("INVARIANT TypeOK\n");
    }
    config.push_str("INVARIANT Inv\n");
    if prop.is_some() {
        config.push_str("PROPERTY Prop\n");
    }
    let deadlock_flag = if check_deadlock { "TRUE" } else { "FALSE" };
    let _ = writeln!(config, "CHECK_DEADLOCK {deadlock_flag}");

    let enabled_open_filter = (inv_enabled || prop_enabled) && model.has_open_filter();
    Case {
        spec,
        config,
        violated,
        enabled_open_filter,
        reachable: reach.len(),
        kind: format!(
            "inv{inv_kind}{}+{prop_kind}{}{}{}",
            if inv_enabled { "/enabled" } else { "" },
            if model.has_open_filter() {
                "+open-filter"
            } else {
                ""
            },
            if model.has_pair_filter() {
                "+pair-filter"
            } else {
                ""
            },
            if model.has_primed_filter() {
                "+primed-filter"
            } else {
                ""
            }
        ),
    }
}
