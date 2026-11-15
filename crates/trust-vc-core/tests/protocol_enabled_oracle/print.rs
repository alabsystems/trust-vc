// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Print the oracle's tree as a TLA+ module (fully parenthesized, so no
//! precedence rule of TLA+ is relied on).

use super::ast::{Def, Module, Pat, St, Var, E, V, VARS};

pub fn module_text(m: &Module, name: &str) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "---- MODULE {name} ----\nEXTENDS Naturals, FiniteSets\nVARIABLES x, y, z\n"
    ));
    for d in &m.defs {
        out.push_str(&def_text(d));
        out.push('\n');
    }
    out.push_str(&format!("Init == {}\n", init_text(&m.init)));
    out.push_str(&format!("Next == {}\n", expr(&m.next)));
    out.push_str(&format!("Inv == {}\n", expr(&m.inv)));
    out.push_str("====\n");
    out
}

pub const CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\n";

fn init_text(s: &St) -> String {
    VARS.iter()
        .map(|v| format!("{} = {}", v.name(), value(&s[v.index()])))
        .collect::<Vec<_>>()
        .join(" /\\ ")
}

pub fn value(v: &V) -> String {
    match v {
        V::Bool(true) => "TRUE".into(),
        V::Bool(false) => "FALSE".into(),
        V::Int(i) => i.to_string(),
        V::Tup(items) => format!(
            "<<{}>>",
            items.iter().map(value).collect::<Vec<_>>().join(", ")
        ),
        V::Set(items) => format!(
            "{{{}}}",
            items.iter().map(value).collect::<Vec<_>>().join(", ")
        ),
    }
}

pub fn state(s: &St) -> String {
    format!(
        "x = {}, y = {}, z = {}",
        value(&s[0]),
        value(&s[1]),
        value(&s[2])
    )
}

fn def_text(d: &Def) -> String {
    if d.params.is_empty() {
        format!("{} == {}", d.name, expr(&d.body))
    } else {
        let params: Vec<String> = d
            .params
            .iter()
            .enumerate()
            .map(|(i, p)| match d.arity(i) {
                0 => p.clone(),
                n => format!("{p}({})", vec!["_"; n].join(", ")),
            })
            .collect();
        format!("{}({}) == {}", d.name, params.join(", "), expr(&d.body))
    }
}

fn pat(p: &Pat) -> String {
    match p {
        Pat::One(n) => n.clone(),
        Pat::Tup(ns) => format!("<<{}>>", ns.join(", ")),
    }
}

fn var(v: Var) -> &'static str {
    v.name()
}

fn join(es: &[E], sep: &str) -> String {
    es.iter().map(expr).collect::<Vec<_>>().join(sep)
}

pub fn expr(e: &E) -> String {
    match e {
        E::Int(i) => i.to_string(),
        E::Bool(true) => "TRUE".into(),
        E::Bool(false) => "FALSE".into(),
        E::Var(v) => var(*v).into(),
        E::Prime(inner) => match inner.as_ref() {
            E::Var(v) => format!("{}'", var(*v)),
            E::Name(n) => format!("{n}'"),
            other => format!("({})'", expr(other)),
        },
        E::Name(n) => n.clone(),
        E::Apply(op, args) => format!("{op}({})", join(args, ", ")),
        E::Add(a, c) => format!("({} + {})", expr(a), expr(c)),
        E::Mod(a, m) => format!("({} % {m})", expr(a)),
        E::Card(s) => format!("Cardinality({})", expr(s)),
        E::Index(t, i) => match t.as_ref() {
            E::Var(_) | E::Name(_) => format!("{}[{i}]", expr(t)),
            E::Prime(inner) if matches!(inner.as_ref(), E::Var(_) | E::Name(_)) => {
                format!("{}[{i}]", expr(t))
            }
            _ => format!("({})[{i}]", expr(t)),
        },
        E::Tuple(es) => format!("<<{}>>", join(es, ", ")),
        E::SetEnum(es) => format!("{{{}}}", join(es, ", ")),
        E::Range(lo, hi) => format!("({lo}..{hi})"),
        E::Cup(a, c) => format!("({} \\cup {})", expr(a), expr(c)),
        E::Cap(a, c) => format!("({} \\cap {})", expr(a), expr(c)),
        E::Diff(a, c) => format!("({} \\ {})", expr(a), expr(c)),
        E::Subset(s) => format!("(SUBSET {})", expr(s)),
        E::Times(a, c) => format!("({} \\X {})", expr(a), expr(c)),
        E::Filter(p, s, pred) => format!("{{{} \\in {} : {}}}", pat(p), expr(s), expr(pred)),
        E::Eq(a, c) => format!("({} = {})", expr(a), expr(c)),
        E::Lt(a, c) => format!("({} < {})", expr(a), expr(c)),
        E::In(a, c) => format!("({} \\in {})", expr(a), expr(c)),
        E::NotIn(a, c) => format!("({} \\notin {})", expr(a), expr(c)),
        E::Subseteq(a, c) => format!("({} \\subseteq {})", expr(a), expr(c)),
        E::Not(a) => format!("(~({}))", expr(a)),
        E::And(es) if es.is_empty() => "TRUE".into(),
        E::And(es) => format!("({})", join(es, " /\\ ")),
        E::Or(es) if es.is_empty() => "FALSE".into(),
        E::Or(es) => format!("({})", join(es, " \\/ ")),
        E::If(c, t, f) => format!("(IF {} THEN {} ELSE {})", expr(c), expr(t), expr(f)),
        E::Exists(p, s, body) => format!("(\\E {} \\in {} : {})", pat(p), expr(s), expr(body)),
        E::Forall(p, s, body) => format!("(\\A {} \\in {} : {})", pat(p), expr(s), expr(body)),
        E::Let(defs, body) => {
            let defs = defs
                .iter()
                .map(def_text)
                .collect::<Vec<_>>()
                .join("\n        ");
            format!("(LET {defs}\n    IN {})", expr(body))
        }
        E::Enabled(a) => format!("(ENABLED ({}))", expr(a)),
        E::Unchanged(v) => format!("(UNCHANGED {})", var(*v)),
        E::UnchangedE(e) => format!("(UNCHANGED {})", expr(e)),
        E::AngleAction(a, sub) => format!("(<<{}>>_{})", expr(a), expr(sub)),
        E::Lambda(params, body) => format!("(LAMBDA {} : {})", params.join(", "), expr(body)),
    }
}
