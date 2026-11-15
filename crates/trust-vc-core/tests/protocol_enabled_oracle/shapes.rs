// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The ENABLED review's shape classes a generated module contains: ty's
//! `judge::features` (`crates/tla-check/tests/enabled_semantic_oracle/judge.rs`
//! in ty), carried unchanged without the parts of that file that read ty's
//! own outcome.

use super::ast::{Module, Pat, E};
use std::collections::BTreeSet;

/// The review's shape classes a module contains (syntactic).
pub fn features(m: &Module) -> BTreeSet<&'static str> {
    let mut out = BTreeSet::new();
    let params: BTreeSet<String> = m.defs.iter().flat_map(|d| d.params.clone()).collect();
    walk(&m.next, false, true, &params, &mut out);
    walk(&m.inv, false, false, &params, &mut out);
    for d in &m.defs {
        walk(&d.body, false, false, &params, &mut out);
        if !d.params.is_empty() && matches!(d.body, E::Filter(..)) {
            out.insert("operator-parameter-filter");
        }
    }
    let mut all_defs: Vec<&super::ast::Def> = m.defs.iter().collect();
    for root in [&m.next, &m.inv] {
        let_defs(root, &mut all_defs);
    }
    for d in m.defs.iter() {
        let_defs(&d.body, &mut all_defs);
    }
    for d in all_defs {
        let is_formal = |n: &str| d.params.iter().any(|p| p == n);
        if any_node(&d.body, &|e| match e {
            E::Let(defs, _) => defs
                .iter()
                .any(|ld| ld.params.is_empty() && matches!(&ld.body, E::Name(n) if is_formal(n))),
            _ => false,
        }) {
            out.insert("let-alias-of-formal");
        }
        if any_node(&d.body, &|e| match e {
            E::Eq(lhs, _) | E::In(lhs, _) => {
                matches!(lhs.as_ref(), E::Prime(inner) if matches!(inner.as_ref(), E::Name(n) if is_formal(n)))
            }
            _ => false,
        }) {
            out.insert("assigns-through-formal");
        }
    }
    out
}

/// Every LET definition under `e`.
fn let_defs<'a>(e: &'a E, out: &mut Vec<&'a super::ast::Def>) {
    if let E::Let(defs, _) = e {
        out.extend(defs.iter());
    }
    for c in children(e) {
        let_defs(c, out);
    }
}

/// Whether `pred` holds of `e` or any subexpression.
fn any_node(e: &E, pred: &dyn Fn(&E) -> bool) -> bool {
    pred(e) || children(e).into_iter().any(|c| any_node(c, pred))
}

/// The direct subexpressions of `e` (definition bodies included).
fn children(e: &E) -> Vec<&E> {
    match e {
        E::Int(_) | E::Bool(_) | E::Var(_) | E::Name(_) | E::Range(..) | E::Unchanged(_) => {
            vec![]
        }
        E::Prime(a)
        | E::Mod(a, _)
        | E::Card(a)
        | E::Index(a, _)
        | E::Subset(a)
        | E::Not(a)
        | E::Enabled(a)
        | E::UnchangedE(a)
        | E::Lambda(_, a) => vec![a.as_ref()],
        E::Add(a, c)
        | E::Cup(a, c)
        | E::Cap(a, c)
        | E::Diff(a, c)
        | E::Times(a, c)
        | E::Eq(a, c)
        | E::Lt(a, c)
        | E::In(a, c)
        | E::NotIn(a, c)
        | E::Subseteq(a, c)
        | E::AngleAction(a, c) => vec![a.as_ref(), c.as_ref()],
        E::Filter(_, s, p) | E::Exists(_, s, p) | E::Forall(_, s, p) => {
            vec![s.as_ref(), p.as_ref()]
        }
        E::Apply(_, es) | E::Tuple(es) | E::SetEnum(es) | E::And(es) | E::Or(es) => {
            es.iter().collect()
        }
        E::If(c, t, f) => vec![c.as_ref(), t.as_ref(), f.as_ref()],
        E::Let(defs, body) => defs
            .iter()
            .map(|d| &d.body)
            .chain(std::iter::once(body.as_ref()))
            .collect(),
    }
}

/// Whether `e` reads a primed variable (an action-level actual).
fn reads_successor(e: &E) -> bool {
    match e {
        E::Prime(_) => true,
        E::Add(a, c) => reads_successor(a) || reads_successor(c),
        E::Mod(a, _) | E::Index(a, _) | E::Card(a) => reads_successor(a),
        _ => false,
    }
}

fn walk(
    e: &E,
    in_enabled: bool,
    in_next: bool,
    params: &BTreeSet<String>,
    out: &mut BTreeSet<&'static str>,
) {
    let mut children: Vec<(&E, bool)> = Vec::new();
    match e {
        E::Enabled(a) => {
            if in_next {
                out.insert("enabled-in-action");
            }
            children.push((a, true));
        }
        E::Let(defs, body) => {
            if in_enabled {
                out.insert("let-in-enabled");
            }
            if defs.iter().any(|d| !d.params.is_empty()) {
                out.insert("let-operator");
            }
            if defs.iter().any(|d| matches!(d.body, E::Filter(..))) {
                out.insert("let-bound-filter");
            }
            for d in defs {
                children.push((&d.body, in_enabled));
            }
            children.push((body, in_enabled));
        }
        E::Prime(inner) => {
            match inner.as_ref() {
                E::Name(_) => {
                    out.insert("primed-definition");
                }
                E::Apply(..) => {
                    out.insert("primed-operator");
                }
                E::Filter(..) => {
                    out.insert("primed-inline-filter");
                }
                _ => {}
            }
            children.push((inner, in_enabled));
        }
        E::Filter(p, s, pred) | E::Exists(p, s, pred) | E::Forall(p, s, pred) => {
            if matches!(p, Pat::Tup(_)) {
                out.insert("tuple-pattern");
            }
            if p.names().iter().any(|n| params.contains(n)) {
                out.insert("captured-local");
            }
            children.push((s, in_enabled));
            children.push((pred, in_enabled));
        }
        E::Apply(op, args) => {
            if args.iter().any(|a| matches!(a, E::Lambda(..))) {
                out.insert("higher-order-operator");
            }
            if in_enabled && args.iter().any(reads_successor) {
                out.insert("action-level-actual");
            }
            if args.iter().any(|a| matches!(a, E::Var(_)))
                && op.chars().next().is_some_and(|c| c.is_uppercase())
            {
                out.insert("state-variable-actual");
            }
            for a in args {
                children.push((a, in_enabled));
            }
        }
        E::UnchangedE(inner) => {
            out.insert("unchanged-expression");
            children.push((inner, in_enabled));
        }
        E::AngleAction(a, sub) => {
            out.insert("angle-action");
            children.push((a, in_enabled));
            children.push((sub, in_enabled));
        }
        E::Lambda(_, body) => {
            children.push((body, in_enabled));
        }
        E::Add(a, c)
        | E::Cup(a, c)
        | E::Cap(a, c)
        | E::Diff(a, c)
        | E::Times(a, c)
        | E::Eq(a, c)
        | E::Lt(a, c)
        | E::In(a, c)
        | E::NotIn(a, c)
        | E::Subseteq(a, c) => {
            children.push((a, in_enabled));
            children.push((c, in_enabled));
        }
        E::Mod(a, _) | E::Card(a) | E::Index(a, _) | E::Subset(a) | E::Not(a) => {
            children.push((a, in_enabled));
        }
        E::Tuple(es) | E::SetEnum(es) | E::And(es) | E::Or(es) => {
            for c in es {
                children.push((c, in_enabled));
            }
        }
        E::If(c, t, f) => {
            children.push((c, in_enabled));
            children.push((t, in_enabled));
            children.push((f, in_enabled));
        }
        E::Int(_) | E::Bool(_) | E::Var(_) | E::Name(_) | E::Range(..) | E::Unchanged(_) => {}
    }
    for (c, en) in children {
        walk(c, en, in_next, params, out);
    }
}
