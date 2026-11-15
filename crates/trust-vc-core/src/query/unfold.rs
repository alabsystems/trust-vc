//! Ground instantiation of definitional equations.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! For every call `f(a1, .., an)` of a defined function that occurs in the
//! hypotheses or the goal, the unfolder adds the hypothesis
//! `f(a1, .., an) == body[params := args]`. Calls inside those instances are
//! instantiated in the next round. Admitted expressions have no binders, so
//! every call is ground and every instance is a plain consequence of the
//! definition.
//!
//! Unfolding stops at a fixpoint (a non-recursive definition always reaches
//! one) or when [`Limits::unfold_rounds`] or [`Limits::max_instances`] runs
//! out. In the second case the query is marked incomplete; see the parent
//! module for what that does to a `sat` answer.

use std::collections::{HashMap, HashSet};

use super::admit::substitute;
use super::{AdmittedQuery, Definition, Hypothesis, HypothesisSource, Limits, UnfoldedQuery};
use crate::ir::{CompareOp, TrustVcExpr};

/// Label prefix of the hypotheses this module adds. Admission refuses caller
/// labels with this prefix, so the two never collide.
pub(super) const DEFINITION_LABEL_PREFIX: &str = "def:";

/// Push every call of a defined function in `expr`, outermost first.
fn collect_calls(
    expr: &TrustVcExpr,
    definitions: &HashMap<&str, &Definition>,
    out: &mut Vec<TrustVcExpr>,
) {
    match expr {
        TrustVcExpr::FnCall { name, args, .. } => {
            if definitions.contains_key(name.as_str()) {
                out.push(expr.clone());
            }
            for arg in args {
                collect_calls(arg, definitions, out);
            }
        }
        TrustVcExpr::Arith { left, right, .. }
        | TrustVcExpr::Compare { left, right, .. }
        | TrustVcExpr::Logic { left, right, .. } => {
            collect_calls(left, definitions, out);
            collect_calls(right, definitions, out);
        }
        TrustVcExpr::Neg(inner) | TrustVcExpr::Not(inner) => {
            collect_calls(inner, definitions, out);
        }
        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => {
            collect_calls(premise, definitions, out);
            collect_calls(conclusion, definitions, out);
        }
        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_calls(cond, definitions, out);
            collect_calls(then_branch, definitions, out);
            collect_calls(else_branch, definitions, out);
        }
        _ => {}
    }
}

/// Identity of a call for deduplication. Admitted terms are small, and the
/// derived `Debug` form is structural, so it is an exact key.
fn call_key(call: &TrustVcExpr) -> String {
    format!("{call:?}")
}

/// Add definition instances to an admitted query.
pub(super) fn unfold(query: &AdmittedQuery, limits: &Limits) -> Result<UnfoldedQuery, String> {
    for hypothesis in &query.hypotheses {
        if hypothesis.label.starts_with(DEFINITION_LABEL_PREFIX) {
            return Err(format!(
                "hypothesis label `{}` uses the reserved prefix `{DEFINITION_LABEL_PREFIX}`",
                hypothesis.label
            ));
        }
    }
    let definitions: HashMap<&str, &Definition> = query
        .definitions
        .iter()
        .map(|definition| (definition.function.as_str(), definition))
        .collect();

    let mut frontier = Vec::new();
    for hypothesis in &query.hypotheses {
        collect_calls(&hypothesis.expr, &definitions, &mut frontier);
    }
    collect_calls(&query.goal, &definitions, &mut frontier);

    let mut hypotheses = query.hypotheses.clone();
    let mut instantiated: HashSet<String> = HashSet::new();
    let mut instances = 0usize;
    let mut rounds = 0u32;
    let mut budget_exhausted = false;
    while !frontier.is_empty() && rounds < limits.unfold_rounds && !budget_exhausted {
        rounds += 1;
        let mut next = Vec::new();
        for call in std::mem::take(&mut frontier) {
            if instantiated.contains(&call_key(&call)) {
                continue;
            }
            if instances >= limits.max_instances {
                budget_exhausted = true;
                next.push(call);
                continue;
            }
            let TrustVcExpr::FnCall { name, args, .. } = &call else {
                continue;
            };
            let Some(definition) = definitions.get(name.as_str()) else {
                continue;
            };
            let bindings: HashMap<&str, &TrustVcExpr> = definition
                .params
                .iter()
                .map(|(param, _)| param.as_str())
                .zip(args.iter())
                .collect();
            let instance = substitute(&definition.body, &bindings);
            collect_calls(&instance, &definitions, &mut next);
            instantiated.insert(call_key(&call));
            hypotheses.push(Hypothesis {
                label: format!("{DEFINITION_LABEL_PREFIX}{name}#{instances}"),
                source: HypothesisSource::Definition,
                expr: TrustVcExpr::Compare {
                    op: CompareOp::Eq,
                    left: Box::new(call),
                    right: Box::new(instance),
                },
            });
            instances += 1;
        }
        frontier = next;
    }
    let complete = frontier
        .iter()
        .all(|call| instantiated.contains(&call_key(call)));

    Ok(UnfoldedQuery {
        label: query.label.clone(),
        symbols: query.symbols.clone(),
        functions: query.functions.clone(),
        hypotheses,
        goal: query.goal.clone(),
        complete,
    })
}
