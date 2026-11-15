//! Query admission: names, types and the scalar fragment, and `let`
//! elimination.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Admission runs before any solver work. It type-checks every expression
//! against the declarations and rejects everything outside the fragment
//! documented on the parent module. The admitted expressions are then
//! rewritten without `let`, by substitution, so the unfolder and the encoder
//! see one shape only.

use std::collections::{HashMap, HashSet};

use super::{is_admitted_name, AdmittedQuery, Definition, Hypothesis, Query};
use crate::ir::{CompareOp, TrustVcExpr, TrustVcType};

/// Solver sorts of the fragment. `MathInt` and `Nat` are both `Int`.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Sort {
    Bool,
    Int,
    Nominal(String),
    Poly,
}

/// Sort of a declared type, or `None` when the type is not admitted.
fn sort_of_type(ty: &TrustVcType, nominal_sorts: &HashSet<&str>) -> Option<Sort> {
    match ty {
        TrustVcType::Bool => Some(Sort::Bool),
        TrustVcType::MathInt | TrustVcType::Nat => Some(Sort::Int),
        TrustVcType::Poly => Some(Sort::Poly),
        TrustVcType::NamedCarrier(name) if nominal_sorts.contains(name.as_str()) => {
            Some(Sort::Nominal(name.clone()))
        }
        _ => None,
    }
}

/// Types allowed on `let` and `if` annotations: `Nat` is left out there,
/// because nothing checks that an arbitrary expression is non-negative.
fn is_value_annotation(ty: &TrustVcType, nominal_sorts: &HashSet<&str>) -> bool {
    !matches!(ty, TrustVcType::Nat) && sort_of_type(ty, nominal_sorts).is_some()
}

/// Declared function signature: parameter types and result type.
type Signature = (Vec<TrustVcType>, TrustVcType);

/// What an expression may refer to while it is being type-checked.
struct Scope<'a> {
    nominal_sorts: &'a HashSet<&'a str>,
    /// Free variables: the query's symbols, or a definition's parameters.
    free: &'a HashMap<String, TrustVcType>,
    functions: &'a HashMap<String, Signature>,
    /// `let`-bound names, innermost last.
    locals: Vec<(String, TrustVcType)>,
}

impl Scope<'_> {
    fn lookup(&self, name: &str) -> Option<&TrustVcType> {
        self.locals
            .iter()
            .rev()
            .find(|(local, _)| local == name)
            .map(|(_, ty)| ty)
            .or_else(|| self.free.get(name))
    }
}

/// A short name for an expression form, for error messages.
fn form_name(expr: &TrustVcExpr) -> &'static str {
    match expr {
        TrustVcExpr::UnitLit => "unit literal",
        TrustVcExpr::BoolLit(_) => "bool literal",
        TrustVcExpr::StringLit(_) => "string literal",
        TrustVcExpr::IntLit { .. } => "integer literal",
        TrustVcExpr::IntConst { .. } => "integer constant",
        TrustVcExpr::Var { .. } => "variable",
        TrustVcExpr::Arith { .. } => "arithmetic",
        TrustVcExpr::Neg(_) => "negation",
        TrustVcExpr::Compare { .. } => "comparison",
        TrustVcExpr::Logic { .. } => "logical operator",
        TrustVcExpr::Not(_) => "not",
        TrustVcExpr::Implies { .. } => "implication",
        TrustVcExpr::Ite { .. } => "if-then-else",
        TrustVcExpr::Match { .. } => "match",
        TrustVcExpr::Let { .. } => "let",
        TrustVcExpr::Cast { .. } => "cast",
        TrustVcExpr::CollectionOp { .. } => "collection operation",
        TrustVcExpr::Index { .. } => "index",
        TrustVcExpr::Quantifier { .. } => "quantifier",
        TrustVcExpr::FnCall { .. } => "function call",
        TrustVcExpr::SpecClosure { .. } => "spec closure",
        TrustVcExpr::SpecialArith { .. } => "bitwise or shift operator",
        TrustVcExpr::WrappingArith { .. } => "wrapping arithmetic",
        TrustVcExpr::Choose { .. } => "choose",
        TrustVcExpr::ReadPlace { .. } => "place read",
        TrustVcExpr::PlaceDisjoint { .. } => "place disjointness",
        TrustVcExpr::ProphecyNew { .. } => "prophecy",
        TrustVcExpr::ProphecyResolve { .. } => "prophecy resolution",
    }
}

fn expect_sort(expr: &TrustVcExpr, scope: &mut Scope<'_>, want: Sort) -> Result<(), String> {
    let got = sort_of(expr, scope)?;
    if got == want {
        Ok(())
    } else {
        Err(format!(
            "{} has sort {got:?} where {want:?} is required",
            form_name(expr)
        ))
    }
}

/// Type-check `expr` in `scope` and return its sort.
fn sort_of(expr: &TrustVcExpr, scope: &mut Scope<'_>) -> Result<Sort, String> {
    match expr {
        TrustVcExpr::BoolLit(_) => Ok(Sort::Bool),
        TrustVcExpr::IntLit { value, ty } => match ty {
            TrustVcType::MathInt => Ok(Sort::Int),
            TrustVcType::Nat if *value >= 0 => Ok(Sort::Int),
            _ => Err(format!(
                "integer literal {value} has type {ty:?}; only MathInt (or a non-negative Nat) is admitted"
            )),
        },
        TrustVcExpr::Var { name, ty } => {
            let declared = scope
                .lookup(name)
                .ok_or_else(|| format!("variable `{name}` is not declared"))?;
            if declared != ty {
                return Err(format!(
                    "variable `{name}` is used at type {ty:?} but declared {declared:?}"
                ));
            }
            sort_of_type(ty, scope.nominal_sorts).ok_or_else(|| format!("variable `{name}` has type {ty:?}, which is not admitted"))
        }
        TrustVcExpr::Arith {
            left, right, ty, ..
        } => {
            if *ty != TrustVcType::MathInt {
                return Err(format!(
                    "arithmetic at type {ty:?} is not admitted; queries compute in MathInt"
                ));
            }
            expect_sort(left, scope, Sort::Int)?;
            expect_sort(right, scope, Sort::Int)?;
            Ok(Sort::Int)
        }
        TrustVcExpr::Neg(inner) => {
            expect_sort(inner, scope, Sort::Int)?;
            Ok(Sort::Int)
        }
        TrustVcExpr::Compare { op, left, right } => {
            let left_sort = sort_of(left, scope)?;
            let right_sort = sort_of(right, scope)?;
            if left_sort != right_sort {
                return Err(format!(
                    "comparison between {left_sort:?} and {right_sort:?}"
                ));
            }
            if !matches!(op, CompareOp::Eq | CompareOp::Ne) && left_sort != Sort::Int {
                return Err(format!("ordering comparison `{op}` on {left_sort:?}"));
            }
            Ok(Sort::Bool)
        }
        TrustVcExpr::Logic { left, right, .. } => {
            expect_sort(left, scope, Sort::Bool)?;
            expect_sort(right, scope, Sort::Bool)?;
            Ok(Sort::Bool)
        }
        TrustVcExpr::Not(inner) => {
            expect_sort(inner, scope, Sort::Bool)?;
            Ok(Sort::Bool)
        }
        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => {
            expect_sort(premise, scope, Sort::Bool)?;
            expect_sort(conclusion, scope, Sort::Bool)?;
            Ok(Sort::Bool)
        }
        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ty,
        } => {
            expect_sort(cond, scope, Sort::Bool)?;
            if !is_value_annotation(ty, scope.nominal_sorts) {
                return Err(format!("if-then-else annotated {ty:?}; a declared non-Nat value type is required"));
            }
            let sort = sort_of_type(ty, scope.nominal_sorts).unwrap_or(Sort::Bool);
            expect_sort(then_branch, scope, sort.clone())?;
            expect_sort(else_branch, scope, sort.clone())?;
            Ok(sort)
        }
        TrustVcExpr::Let {
            name,
            ty,
            value,
            body,
        } => {
            if !is_admitted_name(name) {
                return Err(format!("let-bound name `{name}` is not an admitted name"));
            }
            if !is_value_annotation(ty, scope.nominal_sorts) {
                return Err(format!("let `{name}` annotated {ty:?}; a declared non-Nat value type is required"));
            }
            let sort = sort_of_type(ty, scope.nominal_sorts).unwrap_or(Sort::Bool);
            expect_sort(value, scope, sort)?;
            scope.locals.push((name.clone(), ty.clone()));
            let body_sort = sort_of(body, scope);
            scope.locals.pop();
            body_sort
        }
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => {
            let (params, ret) = scope
                .functions
                .get(name)
                .cloned()
                .ok_or_else(|| format!("function `{name}` is not declared"))?;
            if args.len() != params.len() {
                return Err(format!(
                    "function `{name}` takes {} arguments but is called with {}",
                    params.len(),
                    args.len()
                ));
            }
            for (arg, param) in args.iter().zip(&params) {
                // Declarations were admitted, so every parameter has a sort.
                let want = sort_of_type(param, scope.nominal_sorts).unwrap_or(Sort::Bool);
                expect_sort(arg, scope, want)?;
            }
            if *return_ty != ret {
                return Err(format!(
                    "function `{name}` returns {ret:?} but the call is annotated {return_ty:?}"
                ));
            }
            sort_of_type(&ret, scope.nominal_sorts).ok_or_else(|| format!("function `{name}` has an unadmitted result type"))
        }
        other => Err(format!(
            "{} is not in the admitted query fragment",
            form_name(other)
        )),
    }
}

/// Replace free occurrences of `name` in a `let`-free expression.
///
/// The expression has no binders, so there is nothing to capture.
pub(super) fn substitute(
    expr: &TrustVcExpr,
    bindings: &HashMap<&str, &TrustVcExpr>,
) -> TrustVcExpr {
    let recur = |inner: &TrustVcExpr| Box::new(substitute(inner, bindings));
    match expr {
        TrustVcExpr::Var { name, .. } => match bindings.get(name.as_str()) {
            Some(value) => (*value).clone(),
            None => expr.clone(),
        },
        TrustVcExpr::Arith {
            op,
            left,
            right,
            ty,
        } => TrustVcExpr::Arith {
            op: *op,
            left: recur(left),
            right: recur(right),
            ty: ty.clone(),
        },
        TrustVcExpr::Neg(inner) => TrustVcExpr::Neg(recur(inner)),
        TrustVcExpr::Compare { op, left, right } => TrustVcExpr::Compare {
            op: *op,
            left: recur(left),
            right: recur(right),
        },
        TrustVcExpr::Logic { op, left, right } => TrustVcExpr::Logic {
            op: *op,
            left: recur(left),
            right: recur(right),
        },
        TrustVcExpr::Not(inner) => TrustVcExpr::Not(recur(inner)),
        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => TrustVcExpr::Implies {
            premise: recur(premise),
            conclusion: recur(conclusion),
        },
        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ty,
        } => TrustVcExpr::Ite {
            cond: recur(cond),
            then_branch: recur(then_branch),
            else_branch: recur(else_branch),
            ty: ty.clone(),
        },
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => TrustVcExpr::FnCall {
            name: name.clone(),
            args: args.iter().map(|arg| substitute(arg, bindings)).collect(),
            return_ty: return_ty.clone(),
        },
        // Literals, and (after admission) nothing else.
        _ => expr.clone(),
    }
}

/// Rewrite an admitted expression without `let`.
///
/// Inner `let`s are eliminated first, so the body a binding is substituted
/// into has no binders left and substitution cannot capture.
fn eliminate_lets(expr: &TrustVcExpr) -> TrustVcExpr {
    let recur = |inner: &TrustVcExpr| Box::new(eliminate_lets(inner));
    match expr {
        TrustVcExpr::Let {
            name, value, body, ..
        } => {
            let value = eliminate_lets(value);
            let body = eliminate_lets(body);
            let bindings = HashMap::from([(name.as_str(), &value)]);
            substitute(&body, &bindings)
        }
        TrustVcExpr::Arith {
            op,
            left,
            right,
            ty,
        } => TrustVcExpr::Arith {
            op: *op,
            left: recur(left),
            right: recur(right),
            ty: ty.clone(),
        },
        TrustVcExpr::Neg(inner) => TrustVcExpr::Neg(recur(inner)),
        TrustVcExpr::Compare { op, left, right } => TrustVcExpr::Compare {
            op: *op,
            left: recur(left),
            right: recur(right),
        },
        TrustVcExpr::Logic { op, left, right } => TrustVcExpr::Logic {
            op: *op,
            left: recur(left),
            right: recur(right),
        },
        TrustVcExpr::Not(inner) => TrustVcExpr::Not(recur(inner)),
        TrustVcExpr::Implies {
            premise,
            conclusion,
        } => TrustVcExpr::Implies {
            premise: recur(premise),
            conclusion: recur(conclusion),
        },
        TrustVcExpr::Ite {
            cond,
            then_branch,
            else_branch,
            ty,
        } => TrustVcExpr::Ite {
            cond: recur(cond),
            then_branch: recur(then_branch),
            else_branch: recur(else_branch),
            ty: ty.clone(),
        },
        TrustVcExpr::FnCall {
            name,
            args,
            return_ty,
        } => TrustVcExpr::FnCall {
            name: name.clone(),
            args: args.iter().map(eliminate_lets).collect(),
            return_ty: return_ty.clone(),
        },
        _ => expr.clone(),
    }
}

fn check_declared_type(
    what: &str,
    ty: &TrustVcType,
    nominal_sorts: &HashSet<&str>,
) -> Result<(), String> {
    if sort_of_type(ty, nominal_sorts).is_some() {
        Ok(())
    } else {
        Err(format!(
            "{what} has type {ty:?}; only Bool, MathInt, Nat and registered nominal sorts are admitted"
        ))
    }
}

/// Check a query and return it with every `let` eliminated.
pub(super) fn admit(query: &Query) -> Result<AdmittedQuery, String> {
    let mut nominal_sorts = HashSet::new();
    for name in &query.nominal_sorts {
        if !is_admitted_name(name) || !nominal_sorts.insert(name.as_str()) {
            return Err(format!(
                "nominal sort `{name}` is not an admitted unique name"
            ));
        }
    }
    let mut symbols: HashMap<String, TrustVcType> = HashMap::new();
    for symbol in &query.symbols {
        if !is_admitted_name(&symbol.name) {
            return Err(format!(
                "symbol name `{}` is not an admitted name",
                symbol.name
            ));
        }
        check_declared_type(
            &format!("symbol `{}`", symbol.name),
            &symbol.ty,
            &nominal_sorts,
        )?;
        if symbols
            .insert(symbol.name.clone(), symbol.ty.clone())
            .is_some()
        {
            return Err(format!("symbol `{}` is declared twice", symbol.name));
        }
    }

    let mut functions: HashMap<String, Signature> = HashMap::new();
    for function in &query.functions {
        if !is_admitted_name(&function.name) {
            return Err(format!(
                "function name `{}` is not an admitted name",
                function.name
            ));
        }
        if symbols.contains_key(&function.name) {
            return Err(format!(
                "`{}` is declared as both a symbol and a function",
                function.name
            ));
        }
        for (index, param) in function.params.iter().enumerate() {
            check_declared_type(
                &format!("parameter {index} of `{}`", function.name),
                param,
                &nominal_sorts,
            )?;
        }
        check_declared_type(
            &format!("result of `{}`", function.name),
            &function.ret,
            &nominal_sorts,
        )?;
        let signature = (function.params.clone(), function.ret.clone());
        if functions.insert(function.name.clone(), signature).is_some() {
            return Err(format!("function `{}` is declared twice", function.name));
        }
    }

    let mut defined: HashSet<&str> = HashSet::new();
    let mut definitions = Vec::with_capacity(query.definitions.len());
    for definition in &query.definitions {
        let name = definition.function.as_str();
        let (params, ret) = functions
            .get(name)
            .ok_or_else(|| format!("definition of undeclared function `{name}`"))?;
        if !defined.insert(name) {
            return Err(format!("function `{name}` has two definitions"));
        }
        if definition.params.len() != params.len()
            || definition
                .params
                .iter()
                .zip(params)
                .any(|((_, declared), expected)| declared != expected)
        {
            return Err(format!(
                "definition of `{name}` does not match its declared parameter types"
            ));
        }
        let mut free: HashMap<String, TrustVcType> = HashMap::new();
        for (param, ty) in &definition.params {
            if !is_admitted_name(param) {
                return Err(format!(
                    "parameter `{param}` of `{name}` is not an admitted name"
                ));
            }
            if free.insert(param.clone(), ty.clone()).is_some() {
                return Err(format!(
                    "definition of `{name}` repeats parameter `{param}`"
                ));
            }
        }
        let want = sort_of_type(ret, &nominal_sorts).unwrap_or(Sort::Bool);
        let mut scope = Scope {
            nominal_sorts: &nominal_sorts,
            free: &free,
            functions: &functions,
            locals: Vec::new(),
        };
        expect_sort(&definition.body, &mut scope, want)
            .map_err(|error| format!("definition of `{name}`: {error}"))?;
        definitions.push(Definition {
            function: definition.function.clone(),
            params: definition.params.clone(),
            body: eliminate_lets(&definition.body),
        });
    }

    let mut labels: HashSet<&str> = HashSet::new();
    let mut hypotheses = Vec::with_capacity(query.hypotheses.len());
    for hypothesis in &query.hypotheses {
        if hypothesis.label.is_empty() {
            return Err("a hypothesis has an empty label".to_string());
        }
        if !labels.insert(hypothesis.label.as_str()) {
            return Err(format!(
                "hypothesis label `{}` is used twice",
                hypothesis.label
            ));
        }
        let mut scope = Scope {
            nominal_sorts: &nominal_sorts,
            free: &symbols,
            functions: &functions,
            locals: Vec::new(),
        };
        expect_sort(&hypothesis.expr, &mut scope, Sort::Bool)
            .map_err(|error| format!("hypothesis `{}`: {error}", hypothesis.label))?;
        hypotheses.push(Hypothesis {
            label: hypothesis.label.clone(),
            source: hypothesis.source,
            expr: eliminate_lets(&hypothesis.expr),
        });
    }

    let mut scope = Scope {
        nominal_sorts: &nominal_sorts,
        free: &symbols,
        functions: &functions,
        locals: Vec::new(),
    };
    expect_sort(&query.goal, &mut scope, Sort::Bool).map_err(|error| format!("goal: {error}"))?;

    Ok(AdmittedQuery {
        label: query.label.clone(),
        symbols: query.symbols.clone(),
        functions: query.functions.clone(),
        definitions,
        hypotheses,
        goal: eliminate_lets(&query.goal),
    })
}
