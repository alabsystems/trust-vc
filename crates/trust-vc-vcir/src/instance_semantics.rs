//! Check a generic instance's value semantics before sharing its logical UF.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::cell::Cell;
use std::collections::{HashMap, HashSet, VecDeque};

use crate::{Body, Clause, Expr, ExprKind, FnDecl, FnId, FnRole, Mode, Ty};

type Functions<'a> = HashMap<FnId, &'a FnDecl>;

mod exec_contracts;
mod types;
pub(crate) use exec_contracts::matches as exec_contract_matches;
mod unwind;
use types::{canonical_call, type_work};
pub(crate) use unwind::matches as unwind_matches;
const MATCH_WORK: usize = 16_384;

pub(crate) fn price_type(ty: &Ty, work: &mut usize) -> Option<()> {
    types::type_work(ty, work, 0).then_some(())
}

/// Local structural substitution plus closure over all instance-call edges.
/// Cycles survive only when every member has a matching substituted body.
pub(crate) fn validated_origins(functions: &Functions<'_>) -> HashSet<FnId> {
    validated_origins_with_definitions(functions, None)
}

pub(crate) fn validated_origins_with_definitions<'a>(functions: &Functions<'a>, definitions: Option<&crate::projection_types::Definitions<'a>>) -> HashSet<FnId> {
    let mut candidates = HashMap::new();
    for declaration in functions.values() {
        let mut work = MATCH_WORK;
        if let Some(dependencies) = candidate_with_definitions(functions, declaration, definitions, &mut work) {
            candidates.insert(declaration.id, dependencies);
        }
    }
    let mut callers: HashMap<FnId, Vec<FnId>> = HashMap::new();
    let mut remove = VecDeque::new();
    for (id, dependencies) in &candidates {
        if dependencies
            .iter()
            .any(|dependency| !candidates.contains_key(dependency))
        {
            remove.push_back(*id);
        }
        for dependency in dependencies {
            callers.entry(*dependency).or_default().push(*id);
        }
    }
    while let Some(id) = remove.pop_front() {
        if candidates.remove(&id).is_some() {
            remove.extend(callers.get(&id).into_iter().flatten().copied());
        }
    }
    candidates.into_keys().collect()
}
fn candidate(functions: &Functions<'_>, instance: &FnDecl) -> Option<HashSet<FnId>> {
    let mut budget = MATCH_WORK;
    candidate_budgeted(functions, instance, &mut budget)
}

fn candidate_budgeted(
    functions: &Functions<'_>,
    instance: &FnDecl,
    budget: &mut usize,
) -> Option<HashSet<FnId>> {
    candidate_with_definitions(functions, instance, None, budget)
}

fn candidate_with_definitions<'a>(
    functions: &Functions<'a>, instance: &FnDecl,
    definitions: Option<&crate::projection_types::Definitions<'a>>,
    budget: &mut usize,
) -> Option<HashSet<FnId>> {
    let origin = instance.attrs.instance.as_ref()?;
    let original = functions.get(&origin.declaration)?;
    if instance.role != FnRole::Instance
        || original.role != FnRole::Item
        || original.attrs.instance.is_some()
        || original.attrs.is_trait_method_impl
        || original.mode != Mode::Spec
        || instance.mode != original.mode
        || instance.kind != original.kind
        || !instance.type_params.is_empty()
        || origin.type_args.len() != original.type_params.len()
        || origin.type_args.len() > 64
        || origin.type_args.iter().any(Ty::has_param)
        || instance.params != original.params
        || instance.ret != original.ret
        || instance.locals.len() != original.locals.len()
    {
        return None;
    }
    let attrs = instance.attrs.without_instance();
    if attrs != original.attrs {
        return None;
    }
    let matcher = Matcher {
        functions,
        definitions,
        arguments: &origin.type_args,
        checked_initializer: matches!(original.body, Body::Constant(_)),
        depth: Cell::new(0),
        parameters: None,
    };
    let mut dependencies = HashSet::new();
    if original.copy_premises.len() != instance.copy_premises.len()
        || original
            .copy_premises
            .iter()
            .zip(&instance.copy_premises)
            .any(|(formal, actual)| !matcher.ty(formal, actual, budget))
    {
        return None;
    }
    for (formal, actual) in original.locals.iter().zip(&instance.locals) {
        if formal.kind != actual.kind
            || formal.mode != actual.mode
            || formal.mutable != actual.mutable
            || formal.prophecy != actual.prophecy
            || !matcher.ty(&formal.ty, &actual.ty, budget)
        {
            return None;
        }
    }
    for (formal, actual) in [
        (&original.requires, &instance.requires),
        (&original.ensures, &instance.ensures),
        (&original.recommends, &instance.recommends),
    ] {
        if !matcher.clauses(formal, actual, budget, &mut dependencies) {
            return None;
        }
    }
    if !matcher.exprs(
        &original.decreases,
        &instance.decreases,
        budget,
        &mut dependencies,
    ) || original.decreases_by != instance.decreases_by
    {
        return None;
    }
    match (&original.decreases_when, &instance.decreases_when) {
        (None, None) => {}
        (Some(formal), Some(actual)) if matcher.expr(formal, actual, budget, &mut dependencies) => {
        }
        _ => return None,
    }
    if !matcher.unwind(
        &original.unwind,
        &instance.unwind,
        budget,
        &mut dependencies,
    ) {
        return None;
    }
    match (&original.body, &instance.body) {
        (Body::None, Body::None) => {}
        (Body::Spec(formal), Body::Spec(actual))
        | (Body::Constant(formal), Body::Constant(actual))
            if matcher.expr(formal, actual, budget, &mut dependencies) => {}
        _ => return None,
    }
    Some(dependencies)
}

struct Matcher<'a, 'b> {
    functions: &'a Functions<'b>,
    definitions: Option<&'a crate::projection_types::Definitions<'b>>,
    arguments: &'a [Ty],
    checked_initializer: bool,
    depth: Cell<u32>,
    parameters: Option<(&'a [crate::LocalId], &'a [crate::LocalId])>,
}

struct Depth<'a>(&'a Cell<u32>);
impl Drop for Depth<'_> {
    fn drop(&mut self) {
        self.0.set(self.0.get() - 1);
    }
}

impl Matcher<'_, '_> {
    fn expr(
        &self,
        formal: &Expr,
        actual: &Expr,
        budget: &mut usize,
        dependencies: &mut HashSet<FnId>,
    ) -> bool {
        if self.depth.get() >= 64 {
            return false;
        }
        self.depth.set(self.depth.get() + 1);
        let _depth = Depth(&self.depth);
        let Some(left) = budget.checked_sub(1) else {
            return false;
        };
        *budget = left;
        if !self.ty(&formal.ty, &actual.ty, budget) {
            return false;
        }
        use ExprKind as E;
        match (&formal.kind, &actual.kind) {
            (E::Lit(a), E::Lit(b)) => a == b,
            (E::IntegerConstant(a), E::IntegerConstant(b)) => a == b,
            (E::Read(a), E::Read(b)) | (E::Old(a), E::Old(b)) => {
                if a.projections.len() > *budget || b.projections.len() > *budget {
                    return false;
                }
                *budget -= a.projections.len().max(b.projections.len());
                a.projections == b.projections && self.local(a.local, b.local, budget)
            }
            (
                E::Unary {
                    op: a,
                    arg: x,
                    check: c,
                },
                E::Unary {
                    op: b,
                    arg: y,
                    check: d,
                },
            ) => {
                a == b
                    && (if self.checked_initializer {
                        c == d
                    } else {
                        c.is_none() && d.is_none()
                    })
                    && self.expr(x, y, budget, dependencies)
            }
            (
                E::Binary {
                    op: a,
                    lhs: x,
                    rhs: y,
                    check: c,
                },
                E::Binary {
                    op: b,
                    lhs: z,
                    rhs: w,
                    check: d,
                },
            ) => {
                a == b
                    && (if self.checked_initializer {
                        c == d
                    } else {
                        c.is_none() && d.is_none()
                    })
                    && self.expr(x, z, budget, dependencies)
                    && self.expr(y, w, budget, dependencies)
            }
            (
                E::If {
                    cond: a,
                    then_expr: b,
                    else_expr: c,
                },
                E::If {
                    cond: x,
                    then_expr: y,
                    else_expr: z,
                },
            ) => {
                self.expr(a, x, budget, dependencies)
                    && self.expr(b, y, budget, dependencies)
                    && self.expr(c, z, budget, dependencies)
            }
            (
                E::Let {
                    local: a,
                    value: x,
                    body: y,
                },
                E::Let {
                    local: b,
                    value: z,
                    body: w,
                },
            ) => {
                a == b
                    && self.expr(x, z, budget, dependencies)
                    && self.expr(y, w, budget, dependencies)
            }
            (
                E::Call {
                    callee: a,
                    type_args: x,
                    args: y,
                },
                E::Call {
                    callee: b,
                    type_args: z,
                    args: w,
                },
            ) => {
                let Some((a, x, left_dependency)) = canonical_call(self.functions, *a, x) else {
                    return false;
                };
                let Some((b, z, right_dependency)) = canonical_call(self.functions, *b, z) else {
                    return false;
                };
                if a != b
                    || x.len() != z.len()
                    || x.len() > *budget
                    || !x.iter().zip(z).all(|(x, z)| self.ty(x, z, budget))
                    || !self.exprs(y, w, budget, dependencies)
                {
                    return false;
                }
                dependencies.extend(left_dependency);
                dependencies.extend(right_dependency);
                true
            }
            (E::Cast { arg: a, kind: x }, E::Cast { arg: b, kind: y }) => {
                x == y && self.expr(a, b, budget, dependencies)
            }
            (
                E::Ctor {
                    adt: a,
                    variant: b,
                    fields: x,
                },
                E::Ctor {
                    adt: c,
                    variant: d,
                    fields: y,
                },
            ) => a == c && b == d && self.exprs(x, y, budget, dependencies),
            (E::Tuple(a), E::Tuple(b)) => self.exprs(a, b, budget, dependencies),
            (
                E::Field {
                    base: a,
                    variant: b,
                    field: c,
                },
                E::Field {
                    base: x,
                    variant: y,
                    field: z,
                },
            ) => b == y && c == z && self.expr(a, x, budget, dependencies),
            (E::TupleField { base: a, index: b }, E::TupleField { base: x, index: y }) => {
                b == y && self.expr(a, x, budget, dependencies)
            }
            (E::Borrow(a), E::Borrow(b)) => self.expr(a, b, budget, dependencies),
            (E::MutRefCurrent(a), E::MutRefCurrent(b))
            | (E::MutRefFuture(a), E::MutRefFuture(b))
            | (E::HasResolved(a), E::HasResolved(b)) => self.expr(a, b, budget, dependencies),
            (
                E::MutRefUpdate {
                    reference: a,
                    value: x,
                },
                E::MutRefUpdate {
                    reference: b,
                    value: y,
                },
            ) => self.expr(a, b, budget, dependencies) && self.expr(x, y, budget, dependencies),
            (
                E::Quant {
                    kind: a,
                    vars: x,
                    triggers: y,
                    body: z,
                },
                E::Quant {
                    kind: b,
                    vars: u,
                    triggers: v,
                    body: w,
                },
            ) => {
                a == b
                    && self.variables(x, u, budget)
                    && self.groups(y, v, budget, dependencies)
                    && self.expr(z, w, budget, dependencies)
            }
            (
                E::Choose {
                    vars: a,
                    triggers: b,
                    cond: c,
                    result: d,
                },
                E::Choose {
                    vars: x,
                    triggers: y,
                    cond: z,
                    result: w,
                },
            ) => {
                self.variables(a, x, budget)
                    && self.groups(b, y, budget, dependencies)
                    && self.expr(c, z, budget, dependencies)
                    && self.expr(d, w, budget, dependencies)
            }
            // Proof blocks require their own statement and ownership correspondence.
            // An unexamined block never authorizes a shared function definition.
            _ => false,
        }
    }

    fn variables(
        &self,
        formal: &[(crate::LocalId, Ty)],
        actual: &[(crate::LocalId, Ty)],
        budget: &mut usize,
    ) -> bool {
        formal.len() == actual.len()
            && formal.len() <= *budget
            && formal
                .iter()
                .zip(actual)
                .all(|((a, x), (b, y))| a == b && self.ty(x, y, budget))
    }

    fn ty(&self, formal: &Ty, actual: &Ty, budget: &mut usize) -> bool {
        if !type_work(formal, budget, 0) || !type_work(actual, budget, 0) {
            return false;
        }
        if let Some(definitions) = self.definitions.filter(|definitions| !definitions.is_empty()) {
            definitions.equal_substitution(formal, Some(self.arguments), actual, budget) == Some(true)
        } else { types::substituted(formal, self.arguments, actual) }
    }

    fn clauses(
        &self,
        formal: &[Clause],
        actual: &[Clause],
        budget: &mut usize,
        dependencies: &mut HashSet<FnId>,
    ) -> bool {
        formal.len() == actual.len()
            && formal.len() <= *budget
            && formal.iter().zip(actual).all(|(formal, actual)| {
                formal.attrs == actual.attrs
                    && self.expr(&formal.expr, &actual.expr, budget, dependencies)
            })
    }

    fn exprs(
        &self,
        formal: &[Expr],
        actual: &[Expr],
        budget: &mut usize,
        dependencies: &mut HashSet<FnId>,
    ) -> bool {
        formal.len() == actual.len()
            && formal.len() <= *budget
            && formal
                .iter()
                .zip(actual)
                .all(|(formal, actual)| self.expr(formal, actual, budget, dependencies))
    }

    fn groups(
        &self,
        formal: &[Vec<Expr>],
        actual: &[Vec<Expr>],
        budget: &mut usize,
        dependencies: &mut HashSet<FnId>,
    ) -> bool {
        formal.len() == actual.len()
            && formal.len() <= *budget
            && formal
                .iter()
                .zip(actual)
                .all(|(formal, actual)| self.exprs(formal, actual, budget, dependencies))
    }
}
