//! Ground instances of the pinned opaque mutable-reference prelude.
//!
//! In particular there is no constructor or component extensionality axiom.

use super::{Sort, Term, TypeArgument, Vocabulary};
use std::collections::{HashMap, HashSet};

pub(super) const CURRENT: &str = "mut_ref_current";
pub(super) const FUTURE: &str = "mut_ref_future";
pub(super) const UPDATE: &str = "mut_ref_update_current";
const RESOLVED: &str = "has_resolved";

/// Type binders already present in one query. A registered axiom instance may
/// use these variables but must never import another function's free binders.
fn type_variables(term: &Term, budget: &mut usize) -> Option<HashSet<(String, Sort)>> {
    let mut result = HashSet::new();
    let mut work = vec![term];
    while let Some(term) = work.pop() {
        *budget = budget.checked_sub(1)?;
        match term {
            Term::Var { name, sort } if matches!(sort, Sort::TypeId | Sort::Decoration) => {
                *budget = budget.checked_sub(name.len().checked_add(1)?)?;
                result.insert((name.clone(), *sort));
            }
            Term::Not(inner) | Term::Neg(inner) => work.push(inner),
            Term::And(terms) | Term::Or(terms) | Term::Call { args: terms, .. } => {
                work.extend(terms)
            }
            Term::Implies(a, b) | Term::Cmp(_, a, b) | Term::Arith(_, a, b) => {
                work.push(a);
                work.push(b);
            }
            Term::Ite(condition, a, b, _) => {
                work.push(condition);
                work.push(a);
                work.push(b);
            }
            Term::Bool(_) | Term::Int(_) | Term::Var { .. } => {}
        }
    }
    Some(result)
}

#[derive(Default)]
pub(super) struct MutRefs {
    pub(super) types: HashMap<Term, TypeArgument>,
}

impl Vocabulary {
    pub(crate) fn mut_ref_projection(&mut self, reference: Term, future: bool) -> Option<Term> {
        if reference.sort() != Sort::Poly {
            return None;
        }
        Some(self.call(
            if future { FUTURE } else { CURRENT }.into(),
            vec![reference],
            Sort::Poly,
        ))
    }

    pub(crate) fn mut_ref_update(&mut self, reference: Term, value: Term) -> Option<Term> {
        if reference.sort() != Sort::Poly || value.sort() != Sort::Poly {
            return None;
        }
        Some(self.call(UPDATE.into(), vec![reference, value], Sort::Poly))
    }

    pub(crate) fn has_resolved(&mut self, ty: TypeArgument, value: Term) -> Option<Term> {
        if value.sort() != Sort::Poly {
            return None;
        }
        let mut args = ty.terms().to_vec();
        args.push(value);
        Some(self.call(RESOLVED.into(), args, Sort::Bool))
    }

    pub(super) fn mut_ref_bridge_axioms(
        &mut self,
        roots: &[&Term],
        budget: &mut usize,
    ) -> Option<Vec<Term>> {
        if self.mut_refs.types.is_empty() {
            return Some(Vec::new());
        }
        // Freeze the source query's finite trigger universe. Scalar boxing
        // round trips and product reconstruction facts are consequences, not
        // additional demands for constructing ever larger round-trip terms.
        let mut applications = Vec::new();
        let mut seen = HashSet::new();
        let mut exhausted = false;
        for root in roots {
            *budget = budget.checked_sub(root.size())?;
            root.for_each_call(&mut |name, args| {
                if !matches!(name, CURRENT | FUTURE | UPDATE | RESOLVED) {
                    return;
                }
                let Some(size) = args
                    .iter()
                    .try_fold(1usize, |n, arg| n.checked_add(arg.size()))
                else {
                    exhausted = true;
                    return;
                };
                let Some(cost) = size.checked_mul(4) else {
                    exhausted = true;
                    return;
                };
                let Some(left) = budget.checked_sub(cost) else {
                    exhausted = true;
                    return;
                };
                *budget = left;
                let row = (name.to_owned(), args.to_vec());
                if seen.insert(row.clone()) {
                    applications.push(row);
                }
            });
        }
        if exhausted {
            return None;
        }
        if applications.is_empty() {
            return Some(Vec::new());
        }
        let mut variables = HashSet::new();
        for root in roots {
            variables.extend(type_variables(root, budget)?);
        }
        let mut cases = Vec::new();
        for (identity, inner) in &self.mut_refs.types {
            let binders = type_variables(identity, budget)?;
            if !binders.is_subset(&variables) {
                continue;
            }
            *budget = budget.checked_sub(
                identity
                    .size()
                    .checked_add(inner.identity().size())?
                    .checked_add(1)?,
            )?;
            cases.push((identity.clone(), inner.clone()));
        }
        cases.sort_by_key(|(identity, _)| format!("{identity:?}"));
        let mut projections = HashSet::<(Term, bool)>::new();
        let mut facts = Vec::new();
        for (name, args) in applications {
            let input_size = args
                .iter()
                .try_fold(1usize, |n, arg| n.checked_add(arg.size()))?;
            *budget = budget.checked_sub(input_size.checked_mul(16)?.checked_add(64)?)?;
            match name.as_str() {
                CURRENT | FUTURE => {
                    let [reference] = args.as_slice() else {
                        return None;
                    };
                    projections.insert((reference.clone(), name == FUTURE));
                }
                UPDATE => {
                    let [reference, value] = args.as_slice() else {
                        return None;
                    };
                    let updated = self.call(UPDATE.into(), args.clone(), Sort::Poly);
                    let current = self.mut_ref_projection(updated.clone(), false)?;
                    let future = self.mut_ref_projection(updated.clone(), true)?;
                    let old_future = self.mut_ref_projection(reference.clone(), true)?;
                    facts.push(Term::eq(current, value.clone()));
                    facts.push(Term::eq(future, old_future));
                    projections.insert((updated.clone(), false));
                    projections.insert((updated.clone(), true));
                    projections.insert((reference.clone(), true));
                    for (identity, inner) in &cases {
                        let size = input_size
                            .checked_add(identity.size())?
                            .checked_add(inner.identity().size())?;
                        *budget = budget.checked_sub(size.checked_mul(8)?.checked_add(32)?)?;
                        let typed = self.membership(reference.clone(), identity.clone())?;
                        let value_typed =
                            self.membership(value.clone(), inner.identity().clone())?;
                        let update_typed = self.membership(updated.clone(), identity.clone())?;
                        facts.push(Term::implies(Term::and([typed, value_typed]), update_typed));
                    }
                }
                RESOLVED => {
                    let [decoration, identity, reference] = args.as_slice() else {
                        return None;
                    };
                    let nil = self.call("ty_dec_nil".into(), vec![], Sort::Decoration);
                    if *decoration != nil || !self.mut_refs.types.contains_key(identity) {
                        continue;
                    }
                    let resolved = self.call(RESOLVED.into(), args.clone(), Sort::Bool);
                    let typed = self.membership(reference.clone(), identity.clone())?;
                    let current = self.mut_ref_projection(reference.clone(), false)?;
                    let future = self.mut_ref_projection(reference.clone(), true)?;
                    facts.push(Term::implies(
                        Term::and([typed, resolved]),
                        Term::eq(current, future),
                    ));
                    projections.insert((reference.clone(), false));
                    projections.insert((reference.clone(), true));
                }
                _ => return None,
            }
        }
        let mut projections: Vec<_> = projections.into_iter().collect();
        projections.sort_by_key(|projection| format!("{projection:?}"));
        // Instantiate the pinned projection axiom independently of whether its
        // membership PREMISE is already known. This finite Cartesian product
        // supplies nested-reference and product-field typing chains without
        // asserting any extracted membership atom or rescanning consequences.
        // Closed field types can be absent from a struct's original type-id
        // term, hence cases come from registered types in this query's binder
        // scope rather than only type-id subterms of the original roots.
        for (reference, future) in projections {
            for (identity, inner) in &cases {
                let size = reference
                    .size()
                    .checked_add(identity.size())?
                    .checked_add(inner.identity().size())?;
                *budget = budget.checked_sub(size.checked_mul(8)?.checked_add(32)?)?;
                let typed = self.membership(reference.clone(), identity.clone())?;
                let projection = self.mut_ref_projection(reference.clone(), future)?;
                let projection_typed = self.membership(projection, inner.identity().clone())?;
                facts.push(Term::implies(typed, projection_typed));
            }
        }
        facts.retain(|fact| *fact != Term::Bool(true));
        Some(facts)
    }
}
