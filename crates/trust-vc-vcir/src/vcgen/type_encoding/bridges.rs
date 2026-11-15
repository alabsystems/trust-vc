//! Ground instances of the pinned box, unbox and membership axioms.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{HashMap, HashSet};

use super::{Sort, Term, Vocabulary};

#[derive(Debug, Clone, Copy)]
struct NativeType {
    sort: Sort,
    bounds: (Option<i128>, Option<u128>),
}

#[derive(Default)]
pub(super) struct Bridges {
    native_types: HashMap<Term, NativeType>,
    boxes: HashMap<String, Sort>,
}

impl Vocabulary {
    /// Pinned ordinary bitwise ABI: primitive integer values are boxed, and
    /// only the uninterpreted operation is declared. This introduces no type
    /// membership or exact BV law into the mathematical query.
    pub(crate) fn integer_bitwise(
        &mut self,
        operation: crate::vcgen::bitwise::Operation,
        values: Vec<Term>,
    ) -> Option<Term> {
        if values.len() != operation.arity() || values.iter().any(|value| value.sort() != Sort::Int)
        {
            return None;
        }
        let (box_name, _) = self.bridge_names(Sort::Int)?;
        let args = values
            .into_iter()
            .map(|value| self.call(box_name.clone(), vec![value], Sort::Poly))
            .collect();
        Some(self.call(operation.name().into(), args, Sort::Int))
    }

    fn register_native(
        &mut self,
        identity: Term,
        sort: Sort,
        bounds: (Option<i128>, Option<u128>),
    ) -> Option<()> {
        if let Some(previous) = self.bridges.native_types.get(&identity) {
            return (previous.sort == sort && previous.bounds == bounds).then_some(());
        }
        self.bridges
            .native_types
            .insert(identity, NativeType { sort, bounds });
        Some(())
    }

    fn bridge_names(&mut self, sort: Sort) -> Option<(String, String)> {
        let suffix = match sort {
            Sort::Bool => "bool".into(),
            Sort::Int => "int".into(),
            Sort::Nominal(index) => format!("nominal{index}"),
            _ => return None,
        };
        let box_name = format!("box_{suffix}");
        let unbox_name = format!("unbox_{suffix}");
        self.bridges.boxes.insert(box_name.clone(), sort);
        self.functions
            .entry(box_name.clone())
            .or_insert(super::Function {
                name: box_name.clone(),
                params: vec![sort],
                ret: Sort::Poly,
            });
        self.functions
            .entry(unbox_name.clone())
            .or_insert(super::Function {
                name: unbox_name.clone(),
                params: vec![Sort::Poly],
                ret: sort,
            });
        Some((box_name, unbox_name))
    }

    pub(crate) fn box_value(
        &mut self,
        sort: Sort,
        identity: Term,
        bounds: (Option<i128>, Option<u128>),
        value: Term,
    ) -> Option<Term> {
        if value.sort() != sort
            || identity.sort() != Sort::TypeId
            || !matches!(sort, Sort::Bool | Sort::Int | Sort::Nominal(_))
        {
            return None;
        }
        self.register_native(identity, sort, bounds)?;
        let (box_name, _) = self.bridge_names(sort)?;
        Some(self.call(box_name, vec![value], Sort::Poly))
    }

    pub(crate) fn unbox_value(
        &mut self,
        sort: Sort,
        identity: Term,
        bounds: (Option<i128>, Option<u128>),
        value: Term,
    ) -> Option<Term> {
        if value.sort() != Sort::Poly
            || identity.sort() != Sort::TypeId
            || !matches!(sort, Sort::Bool | Sort::Int | Sort::Nominal(_))
        {
            return None;
        }
        self.register_native(identity, sort, bounds)?;
        let (box_name, unbox_name) = self.bridge_names(sort)?;
        if let Term::Call { name, args, .. } = &value {
            if *name == box_name && args.len() == 1 && args[0].sort() == sort {
                return Some(args[0].clone());
            }
        }
        Some(self.call(unbox_name, vec![value], sort))
    }

    pub(super) fn scalar_bridge_axioms(
        &mut self,
        roots: &[&Term],
        budget: &mut usize,
    ) -> Option<Vec<Term>> {
        if self.bridges.boxes.is_empty() {
            return Some(Vec::new());
        }
        let mut applications = Vec::new();
        let mut seen = HashSet::new();
        for root in roots {
            *budget = budget.checked_sub(root.size())?;
            root.for_each_call(&mut |name, args| {
                if self.functions.contains_key(name) {
                    let row = (name.to_string(), args.to_vec());
                    if seen.insert(row.clone()) {
                        applications.push(row);
                    }
                }
            });
        }
        let mut identities: Vec<_> = self
            .bridges
            .native_types
            .iter()
            .filter(|(identity, _)| match identity {
                Term::Call { name, args, .. } => seen.contains(&(name.clone(), args.clone())),
                _ => false,
            })
            .map(|(identity, native)| (identity.clone(), *native))
            .collect();
        identities.sort_by_key(|(identity, _)| format!("{identity:?}"));
        let mut facts = Vec::new();
        for (name, args) in applications {
            if let Some(sort) = self.bridges.boxes.get(&name).copied() {
                let [value] = args.as_slice() else {
                    return None;
                };
                let boxed = self.call(name, args.clone(), Sort::Poly);
                let (_, unbox) = self.bridge_names(sort)?;
                let recovered = self.call(unbox, vec![boxed.clone()], sort);
                facts.push(Term::eq(recovered, value.clone()));
                for (identity, native) in &identities {
                    if native.sort == sort {
                        let membership = self.membership(boxed.clone(), identity.clone())?;
                        facts.push(Term::implies(
                            value.within_type_bounds(native.bounds.0, native.bounds.1),
                            membership,
                        ));
                    }
                }
            } else if name == "has_type" {
                let [value, identity] = args.as_slice() else {
                    return None;
                };
                let Some(native) = self.bridges.native_types.get(identity).copied() else {
                    continue;
                };
                let (box_name, unbox) = self.bridge_names(native.sort)?;
                let recovered = self.call(unbox, vec![value.clone()], native.sort);
                let boxed = self.call(box_name, vec![recovered.clone()], Sort::Poly);
                let membership = self.membership(value.clone(), identity.clone())?;
                facts.push(Term::implies(
                    membership.clone(),
                    Term::eq(boxed, value.clone()),
                ));
                facts.push(Term::implies(
                    membership,
                    recovered.within_type_bounds(native.bounds.0, native.bounds.1),
                ));
            }
        }
        facts.retain(|fact| *fact != Term::Bool(true));
        for fact in &facts {
            *budget = budget.checked_sub(fact.size())?;
        }
        Some(facts)
    }
}
