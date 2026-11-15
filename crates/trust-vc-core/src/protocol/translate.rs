//! Rust protocol components to a TLA+ module and TLC configuration.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Converts `#[protocol]`/`#[action]`/`#[safety]`/`#[liveness]` registrations
//! into TLA+ module text and TLC configuration text for model checking. Each
//! body is translated by [`super::rust_expr`], which refuses what it cannot
//! translate exactly. Every name placed in the module is checked to be a TLA+
//! identifier used once, and the module `ty` reads must declare exactly the
//! variables and define exactly the operators emitted here
//! ([`ProtocolShape`], checked against `ty`'s `source.units`).

use std::collections::BTreeSet;
use std::fmt::Write as _;

use super::rust_expr::{self, Ty};
use super::ProtocolShape;
use crate::error::{TrustVcError, TrustVcResult};
use crate::verification_bridge::{
    ProtocolActionDef, ProtocolInitial, ProtocolInvariantDef, ProtocolLivenessDef,
    ProtocolStateVarDef,
};

/// Translation output: TLA+ module text, TLC config text, and what the module
/// declares and defines.
pub(crate) struct TranslatedProtocol {
    pub spec: String,
    pub config: String,
    pub shape: ProtocolShape,
}

/// Translate collected protocol components into a TLA+ module and config.
///
/// The module has:
/// - `VARIABLE` declarations from the `#[protocol]` struct's fields;
/// - `TypeOK`, bounding each variable by its Rust type's range;
/// - `Init`, each variable at its registered initial value: a `#[protocol]`
///   struct's `Default::default()`, read from Rust (a struct without
///   `Default`, or whose `Default::default()` is not one state, is refused);
/// - one operator per `#[action]`, and `Next`, their disjunction plus a
///   stutter step;
/// - `NoPanic_<action>` for each action that can overflow: running the action
///   in the state does not overflow;
/// - one operator per `#[safety]` invariant and per `#[liveness]` property.
///
/// The config checks `TypeOK`, every `NoPanic_<action>` and every invariant,
/// and every liveness property.
pub(crate) fn translate_protocol(
    protocol_name: &str,
    state_vars: &[&ProtocolStateVarDef],
    actions: &[ProtocolActionDef],
    invariants: &[ProtocolInvariantDef],
    liveness: &[ProtocolLivenessDef],
) -> TrustVcResult<TranslatedProtocol> {
    translate(protocol_name, state_vars, actions, invariants, liveness).map_err(|detail| {
        TrustVcError::Internal {
            context: "protocol translation",
            detail: format!("protocol '{protocol_name}': {detail}"),
        }
    })
}

fn translate(
    protocol_name: &str,
    state_vars: &[&ProtocolStateVarDef],
    actions: &[ProtocolActionDef],
    invariants: &[ProtocolInvariantDef],
    liveness: &[ProtocolLivenessDef],
) -> Result<TranslatedProtocol, String> {
    let mut names = Names::default();
    names.check(protocol_name, "protocol")?;
    for generated in ["TypeOK", "Init", "Next"] {
        names.claim(generated, "generated operator")?;
    }
    let mut vars: Vec<(&str, Ty)> = Vec::new();
    let mut initial = Vec::new();
    for var in state_vars {
        let ty = Ty::parse(&var.rust_type).ok_or_else(|| {
            format!(
                "unsupported protocol state type '{}: {}' (bool and fixed-width integers only)",
                var.field_name, var.rust_type
            )
        })?;
        names.claim(&var.field_name, "state variable")?;
        vars.push((var.field_name.as_str(), ty));
        initial.push(initial_value(var, ty)?);
    }
    if vars.is_empty() {
        return Err("a protocol needs at least one state variable".to_string());
    }
    let var_list = vars.iter().map(|(name, _)| *name).collect::<Vec<_>>();
    let tuple = |names: &[&str]| match names {
        [one] => (*one).to_string(),
        many => format!("<<{}>>", many.join(", ")),
    };

    // An action, invariant or property registered twice (its function ran
    // twice) is one component; two different ones under one name are refused.
    let actions = distinct(actions, |a| (&a.name, &a.body));
    let invariants = distinct(invariants, |i| (&i.name, &i.expr));
    let liveness = distinct(liveness, |l| (&l.name, &l.expr));

    let mut spec = format!("---- MODULE {protocol_name} ----\n");
    let _ = write!(spec, "VARIABLE {}\n\n", var_list.join(", "));
    let domains = vars
        .iter()
        .map(|(name, ty)| format!("  /\\ {name} \\in {}", ty.domain()));
    let _ = write!(
        spec,
        "TypeOK ==\n{}\n\n",
        domains.collect::<Vec<_>>().join("\n")
    );
    let starts = vars
        .iter()
        .zip(&initial)
        .map(|((name, _), value)| format!("  /\\ {name} = {value}"));
    let _ = write!(
        spec,
        "Init ==\n{}\n\n",
        starts.collect::<Vec<_>>().join("\n")
    );

    let mut operators = vec!["TypeOK", "Init", "Next"];
    let mut checked = vec!["TypeOK".to_string()];
    let mut panic_free = Vec::new();
    for action in &actions {
        names.claim(&action.name, "action")?;
        let translated = rust_expr::action(&action.body, &vars)
            .map_err(|detail| format!("cannot translate action '{}': {detail}", action.name))?;
        let unchanged: Vec<&str> = var_list
            .iter()
            .copied()
            .filter(|var| !translated.assigned.iter().any(|done| done == var))
            .collect();
        let mut clauses = translated.clauses;
        if !unchanged.is_empty() {
            clauses.push(format!("UNCHANGED {}", tuple(&unchanged)));
        }
        let body = clauses
            .iter()
            .map(|clause| format!("  /\\ {clause}"))
            .collect::<Vec<_>>()
            .join("\n");
        let _ = write!(spec, "{} ==\n{body}\n\n", action.name);
        operators.push(&action.name);
        if let Some(condition) = translated.panic_free {
            let name = format!("NoPanic_{}", action.name);
            names.claim(&name, "generated operator")?;
            panic_free.push((name, condition));
        }
    }

    // Next: every action, plus a stutter step so that a state where every
    // action is disabled is not reported as a deadlock.
    if actions.is_empty() {
        spec.push_str("Next == FALSE\n\n");
    } else {
        let disjuncts = actions
            .iter()
            .map(|action| format!("  \\/ {}", action.name))
            .collect::<Vec<_>>()
            .join("\n");
        let _ = write!(
            spec,
            "Next ==\n{disjuncts}\n  \\/ UNCHANGED {}\n\n",
            tuple(&var_list)
        );
    }

    for (name, condition) in &panic_free {
        let _ = write!(spec, "{name} ==\n  {condition}\n\n");
        checked.push(name.clone());
    }
    for inv in &invariants {
        names.claim(&inv.name, "safety invariant")?;
        let body = rust_expr::invariant(&inv.expr, &vars)
            .map_err(|detail| format!("cannot translate invariant '{}': {detail}", inv.name))?;
        let _ = write!(spec, "{} ==\n  {body}\n\n", inv.name);
        checked.push(inv.name.clone());
    }
    for prop in &liveness {
        names.claim(&prop.name, "liveness property")?;
        let body = rust_expr::temporal(&prop.expr).map_err(|detail| {
            format!(
                "cannot translate liveness property '{}': {detail}",
                prop.name
            )
        })?;
        let _ = write!(spec, "{} ==\n  {body}\n\n", prop.name);
    }
    spec.push_str("====\n");

    let mut config = String::from("INIT Init\nNEXT Next\n");
    for name in &checked {
        let _ = writeln!(config, "INVARIANT {name}");
    }
    for prop in &liveness {
        let _ = writeln!(config, "PROPERTY {}", prop.name);
    }

    let mut defined: Vec<&str> = operators;
    defined.extend(panic_free.iter().map(|(name, _)| name.as_str()));
    defined.extend(invariants.iter().map(|inv| inv.name.as_str()));
    defined.extend(liveness.iter().map(|prop| prop.name.as_str()));
    let shape = ProtocolShape {
        variables: var_list.iter().map(|v| v.to_string()).collect(),
        operators: defined.iter().map(|o| o.to_string()).collect(),
    };
    Ok(TranslatedProtocol {
        spec,
        config,
        shape,
    })
}

/// The TLA+ value `var` starts at (see [`ProtocolInitial`]).
fn initial_value(var: &ProtocolStateVarDef, ty: Ty) -> Result<String, String> {
    let field = &var.field_name;
    match &var.initial {
        ProtocolInitial::Zero => Ok(ty.zero().to_string()),
        ProtocolInitial::NoDefault => Err(format!(
            "no initial state: the model starts from `Default::default()`, and the \
             protocol struct does not implement `Default` (field '{field}')"
        )),
        ProtocolInitial::Default([first, second]) if first != second => Err(format!(
            "no one initial state: two `Default::default()` calls gave field '{field}' \
             {first:?}, then {second:?}"
        )),
        ProtocolInitial::Default([value, _]) => {
            value.and_then(|value| ty.value(value)).ok_or_else(|| {
                format!(
                    "field '{field}' is {value:?} in `Default::default()`, not a value of \
                     its type {}",
                    var.rust_type
                )
            })
        }
    }
}

/// The registrations with exact repeats removed; a name that repeats with a
/// different body is kept twice, so that [`Names::claim`] refuses it.
fn distinct<'a, T, K: PartialEq>(items: &'a [T], key: impl Fn(&'a T) -> K) -> Vec<&'a T> {
    let mut kept: Vec<&T> = Vec::new();
    for item in items {
        if !kept.iter().any(|seen| key(seen) == key(item)) {
            kept.push(item);
        }
    }
    kept
}

/// The TLA+ identifiers placed in one module.
#[derive(Default)]
struct Names(BTreeSet<String>);

impl Names {
    /// `name` is a TLA+ identifier that is not a reserved word.
    fn check(&self, name: &str, what: &str) -> Result<(), String> {
        let identifier = name.chars().all(|c| c == '_' || c.is_ascii_alphanumeric())
            && name.chars().any(|c| c.is_ascii_alphabetic())
            && !name.starts_with("WF_")
            && !name.starts_with("SF_")
            && !TLA_RESERVED.contains(&name);
        if identifier {
            Ok(())
        } else {
            Err(format!("{what} name '{name}' is not a TLA+ identifier"))
        }
    }

    /// `name` is a TLA+ identifier not yet used in this module.
    fn claim(&mut self, name: &str, what: &str) -> Result<(), String> {
        self.check(name, what)?;
        if self.0.insert(name.to_string()) {
            Ok(())
        } else {
            Err(format!(
                "{what} name '{name}' is already a name in this protocol's TLA+ module"
            ))
        }
    }
}

/// TLA+ reserved words (TLA+ 2, including the proof language).
const TLA_RESERVED: [&str; 56] = [
    "ACTION",
    "ASSUME",
    "ASSUMPTION",
    "AXIOM",
    "BOOLEAN",
    "BY",
    "CASE",
    "CHOOSE",
    "CONSTANT",
    "CONSTANTS",
    "COROLLARY",
    "DEF",
    "DEFINE",
    "DEFS",
    "DOMAIN",
    "ELSE",
    "ENABLED",
    "EXCEPT",
    "EXTENDS",
    "FALSE",
    "HAVE",
    "HIDE",
    "IF",
    "IN",
    "INSTANCE",
    "LAMBDA",
    "LEMMA",
    "LET",
    "LOCAL",
    "MODULE",
    "NEW",
    "OBVIOUS",
    "OMITTED",
    "ONLY",
    "OTHER",
    "PICK",
    "PROOF",
    "PROPOSITION",
    "PROVE",
    "QED",
    "RECURSIVE",
    "STATE",
    "STRING",
    "SUBSET",
    "SUFFICES",
    "TAKE",
    "TEMPORAL",
    "THEN",
    "THEOREM",
    "TRUE",
    "UNCHANGED",
    "UNION",
    "USE",
    "VARIABLE",
    "VARIABLES",
    "WITH",
];

#[cfg(test)]
#[path = "translate_tests.rs"]
mod tests;
