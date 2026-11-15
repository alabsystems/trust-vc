//! Answering generated queries with trust-vc-core (feature `solve`).
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! [`to_core`] translates one scalar [`Query`] into
//! `trust_vc_core::query::Query`: sorts become `Bool`/`MathInt` or registered
//! `NamedCarrier` values, terms become
//! `TrustVcExpr` nodes of the query API's scalar fragment, hypotheses keep
//! their labels. [`check`] answers it. The query API admits the query
//! (names, sorts, fragment) before any solver work and reports anything it
//! does not admit as `Verdict::Error`, never as a weaker question.
//!
//! ay may print diagnostics of its own on the process's standard error while
//! it solves. A caller whose standard error is machine-read (the `rust_verify`
//! shim) must redirect it around [`check`].

use trust_vc_core::ir::{ArithOp as CoreArith, CompareOp, LogicOp, TrustVcExpr, TrustVcType};
use trust_vc_core::query as core;

pub use trust_vc_core::query::{Limits, ModelEntry, Verdict};
pub use trust_vc_core::UnknownCategory;

use crate::vcgen::term::{ArithOp, CmpOp, Sort, Term};
use crate::vcgen::{Query, Source};

fn ty(sort: Sort) -> TrustVcType {
    match sort {
        Sort::Bool => TrustVcType::Bool,
        Sort::Int => TrustVcType::MathInt,
        Sort::Nominal(index) => TrustVcType::NamedCarrier(format!("nominal{index}")),
        Sort::Poly => TrustVcType::Poly,
        Sort::TypeId => TrustVcType::NamedCarrier("poly_type".into()),
        Sort::Decoration => TrustVcType::NamedCarrier("poly_dec".into()),
    }
}

fn source(source: Source) -> core::HypothesisSource {
    match source {
        Source::Requires => core::HypothesisSource::Requires,
        Source::Assume => core::HypothesisSource::Assume,
        Source::Assert | Source::CheckAssumed | Source::CallRequires | Source::LoopInvariant => {
            core::HypothesisSource::Assert
        }
        Source::CalleeEnsures => core::HypothesisSource::CalleeEnsures,
        Source::PathCondition | Source::LoopExit => core::HypothesisSource::PathCondition,
        Source::Binding => core::HypothesisSource::Binding,
        Source::TypeFact | Source::Axiom => core::HypothesisSource::TypeFact,
    }
}

/// Fold a list with a binary logical operator; `unit` for an empty list.
fn fold(op: LogicOp, terms: &[Term], unit: bool) -> TrustVcExpr {
    let mut iter = terms.iter().rev();
    let Some(last) = iter.next() else {
        return TrustVcExpr::BoolLit(unit);
    };
    iter.fold(expr(last), |acc, term| TrustVcExpr::Logic {
        op,
        left: Box::new(expr(term)),
        right: Box::new(acc),
    })
}

/// A term as a query-API expression.
#[must_use]
pub fn expr(term: &Term) -> TrustVcExpr {
    let b = |t: &Term| Box::new(expr(t));
    match term {
        Term::Bool(value) => TrustVcExpr::BoolLit(*value),
        Term::Int(value) => TrustVcExpr::IntLit {
            value: *value,
            ty: TrustVcType::MathInt,
        },
        Term::Var { name, sort } => TrustVcExpr::Var {
            name: name.clone(),
            ty: ty(*sort),
        },
        Term::Not(inner) => TrustVcExpr::Not(b(inner)),
        Term::And(terms) => fold(LogicOp::And, terms, true),
        Term::Or(terms) => fold(LogicOp::Or, terms, false),
        Term::Implies(premise, conclusion) => TrustVcExpr::Implies {
            premise: b(premise),
            conclusion: b(conclusion),
        },
        Term::Cmp(op, left, right) => TrustVcExpr::Compare {
            op: match op {
                CmpOp::Eq => CompareOp::Eq,
                CmpOp::Lt => CompareOp::Lt,
                CmpOp::Le => CompareOp::Le,
            },
            left: b(left),
            right: b(right),
        },
        Term::Arith(op, left, right) => TrustVcExpr::Arith {
            op: match op {
                ArithOp::Add => CoreArith::Add,
                ArithOp::Sub => CoreArith::Sub,
                ArithOp::Mul => CoreArith::Mul,
                ArithOp::Div => CoreArith::Div,
                ArithOp::Mod => CoreArith::Rem,
            },
            left: b(left),
            right: b(right),
            ty: TrustVcType::MathInt,
        },
        Term::Neg(inner) => TrustVcExpr::Neg(b(inner)),
        Term::Ite(cond, then_branch, else_branch, sort) => TrustVcExpr::Ite {
            cond: b(cond),
            then_branch: b(then_branch),
            else_branch: b(else_branch),
            ty: ty(*sort),
        },
        Term::Call { name, args, sort } => TrustVcExpr::FnCall {
            name: name.clone(),
            args: args.iter().map(expr).collect(),
            return_ty: ty(*sort),
        },
    }
}

/// Translate a scalar generated query into the query API's form.
///
/// Returns an error for isolated BV or complete-architecture envelopes;
/// [`check`] dispatches those through their respective native question types.
/// A caller must not export their scalar sentinel as the actual question.
#[must_use]
pub fn to_core(query: &Query, label: &str) -> Result<core::Query, &'static str> {
    if query.bitvector.is_some() || query.architectures.is_some() {
        return Err(
            "an isolated or architecture-batched query cannot be converted into one scalar query",
        );
    }
    let mut out = core::Query::new(label, expr(&query.goal));
    out.nominal_sorts = (0..query.nominal_types.len())
        .map(|index| format!("nominal{index}"))
        .collect();
    for (sort, name) in [(Sort::TypeId, "poly_type"), (Sort::Decoration, "poly_dec")] {
        if query.symbols.iter().any(|symbol| symbol.sort == sort)
            || query
                .functions
                .iter()
                .any(|function| function.ret == sort || function.params.contains(&sort))
        {
            out.nominal_sorts.push(name.into());
        }
    }
    out.symbols = query
        .symbols
        .iter()
        .map(|s| core::Symbol::with_display(s.name.clone(), ty(s.sort), s.display.clone()))
        .collect();
    out.functions = query
        .functions
        .iter()
        .map(|f| core::Function {
            name: f.name.clone(),
            params: f.params.iter().copied().map(ty).collect(),
            ret: ty(f.ret),
        })
        .collect();
    out.definitions = query
        .definitions
        .iter()
        .map(|d| core::Definition {
            function: d.function.clone(),
            params: d
                .params
                .iter()
                .map(|(name, sort)| (name.clone(), ty(*sort)))
                .collect(),
            body: expr(&d.body),
        })
        .collect();
    out.hypotheses = query
        .hypotheses
        .iter()
        .map(|h| core::Hypothesis::new(h.label.clone(), source(h.source), expr(&h.term)))
        .collect();
    Ok(out)
}

/// A native answer and, only for a genuine BV refutation, the architecture
/// of the query that actually refuted. Core's verdict semantics are unchanged.
#[derive(Debug)]
pub struct DetailedVerdict {
    pub verdict: Verdict,
    pub refuted_architecture: Option<u32>,
}

impl DetailedVerdict {
    fn plain(verdict: Verdict) -> Self {
        Self {
            verdict,
            refuted_architecture: None,
        }
    }
    fn at(verdict: Verdict, width: u32) -> Self {
        let refuted_architecture = matches!(&verdict, Verdict::Refuted { .. }).then_some(width);
        Self {
            verdict,
            refuted_architecture,
        }
    }
}

/// Answer a generated query without changing the shared Core verdict API.
#[must_use]
pub fn check(query: &Query, label: &str, limits: &Limits) -> Verdict {
    check_detailed(query, label, limits).verdict
}

/// The ordinary dispatcher with actual native failure provenance retained.
#[must_use]
pub fn check_detailed(query: &Query, label: &str, limits: &Limits) -> DetailedVerdict {
    if let Some(cases) = &query.architectures {
        if let Err(message) = admit_complete(query, label) {
            return DetailedVerdict::plain(Verdict::Error { message });
        }
        for (width, case) in cases {
            let result = check_detailed(case, &format!("{label}_arch{width}"), limits);
            if !matches!(&result.verdict, Verdict::Proved { .. }) {
                return result;
            }
        }
        return DetailedVerdict::plain(Verdict::Proved {
            used_hypotheses: None,
        });
    }
    if let Some(cases) = &query.bitvector {
        if let Err(message) = pre_admit(query, label) {
            return DetailedVerdict::plain(Verdict::Error { message });
        }
        for case in cases {
            let result = DetailedVerdict::at(
                core::check_bitvector(case, label, limits),
                case.architecture,
            );
            if !matches!(&result.verdict, Verdict::Proved { .. }) {
                return result;
            }
        }
        return DetailedVerdict::plain(Verdict::Proved {
            used_hypotheses: None,
        });
    }
    DetailedVerdict::plain(check_scalar(query, label, limits))
}

fn check_scalar(query: &Query, label: &str, limits: &Limits) -> Verdict {
    let mut nominal_types = std::collections::HashSet::new();
    for ty in &query.nominal_types {
        if !matches!(ty, crate::Ty::Adt(..)) || ty.has_param() || !nominal_types.insert(ty) {
            return Verdict::Error {
                message: "invalid, still-generic or duplicate nominal carrier identity".into(),
            };
        }
    }
    if query.goal == Term::Bool(true) {
        return Verdict::Proved {
            used_hypotheses: Some(Vec::new()),
        };
    }
    match to_core(query, label) {
        Ok(query) => core::check(&query, limits),
        Err(message) => Verdict::Error {
            message: message.into(),
        },
    }
}

fn admit_complete(query: &Query, label: &str) -> Result<(), String> {
    let Some(cases) = &query.architectures else {
        return pre_admit(query, label);
    };
    if query.bitvector.is_some()
        || !query.nominal_types.is_empty()
        || !query.symbols.is_empty()
        || !query.functions.is_empty()
        || !query.definitions.is_empty()
        || !query.hypotheses.is_empty()
        || query.goal != Term::Bool(false)
        || cases.len() != 2
        || cases[0].0 != 32
        || cases[1].0 != 64
    {
        return Err("an invalid complete architecture envelope".into());
    }
    for (width, case) in cases {
        if case
            .bitvector
            .as_ref()
            .is_some_and(|questions| questions.len() != 1 || questions[0].architecture != *width)
        {
            return Err("an isolated question has the wrong enclosing architecture".into());
        }
        pre_admit(case, label)?;
    }
    Ok(())
}

mod bitvector_group;
pub use bitvector_group::check_bitvector_group;

fn pre_admit(query: &Query, label: &str) -> Result<(), String> {
    if query.architectures.is_some() {
        return Err("nested architecture envelopes are not admitted".into());
    }
    if let Some(cases) = &query.bitvector {
        if !query.nominal_types.is_empty()
            || !query.symbols.is_empty()
            || !query.functions.is_empty()
            || !query.definitions.is_empty()
            || !query.hypotheses.is_empty()
            || query.goal != Term::Bool(false)
            || cases.is_empty()
            || cases.len() > 2
            || (cases.len() == 2 && cases[0].architecture == cases[1].architecture)
        {
            return Err("an invalid isolated BV architecture case".into());
        }
        for case in cases {
            case.validate().map_err(str::to_owned)?;
        }
        return Ok(());
    }
    let mut nominal_types = std::collections::HashSet::new();
    for ty in &query.nominal_types {
        if !matches!(ty, crate::Ty::Adt(..)) || ty.has_param() || !nominal_types.insert(ty) {
            return Err("invalid, still-generic or duplicate nominal carrier identity".into());
        }
    }
    core::validate(&to_core(query, label).map_err(str::to_owned)?)
}
