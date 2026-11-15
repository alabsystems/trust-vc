//! Checked concrete-domain templates over the current typed call vocabulary.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::HashMap;

use crate::FnId;

use super::quant::Registry;
use super::query::Function;
use super::spec::SpecSig;
use super::term::{CmpOp, Sort, Term};
use super::type_encoding::TypeArgument;
use super::val::{Ctx, LeafTy, Shape};

/// Data from this Ctx's actual declarations and canonical type recipes. It
/// grants no body, import or membership fact and emits no material call.
pub(super) struct Vocabulary {
    functions: HashMap<String, Function>,
    generic_heads: HashMap<String, usize>,
    closed_arguments: Vec<TypeArgument>,
    nominal_count: usize,
}

pub(super) fn native_sort(sort: Sort) -> bool {
    matches!(sort, Sort::Bool | Sort::Int | Sort::Nominal(_))
}

/// Reserve the borrowed walk and a subsequent copy/hash/equality walk before
/// visiting children. Names are charged before their bytes are read or copied.
/// No size census traverses an unpaid tree to calculate its own charge.
pub(super) fn charge_term(term: &Term, pay: &mut impl FnMut(usize) -> bool) -> bool {
    if !pay(4) {
        return false;
    }
    match term {
        Term::Bool(_) | Term::Int(_) => true,
        Term::Var { name, .. } => pay(name.len().saturating_mul(4)),
        Term::Not(a) | Term::Neg(a) => charge_term(a, pay),
        Term::And(args) | Term::Or(args) => args.iter().all(|arg| charge_term(arg, pay)),
        Term::Call { name, args, .. } => {
            pay(name.len().saturating_mul(4)) && args.iter().all(|arg| charge_term(arg, pay))
        }
        Term::Implies(a, b) | Term::Cmp(_, a, b) | Term::Arith(_, a, b) => {
            charge_term(a, pay) && charge_term(b, pay)
        }
        Term::Ite(c, a, b, _) => charge_term(c, pay) && charge_term(a, pay) && charge_term(b, pay),
    }
}

fn shape_matches(
    shape: &Shape,
    params: &[Sort],
    at: &mut usize,
    pay: &mut impl FnMut(usize) -> bool,
) -> bool {
    if !pay(1) {
        return false;
    }
    match shape {
        Shape::Leaf(leaf) => {
            let found = params.get(*at) == Some(&leaf.sort());
            *at = (*at).saturating_add(1);
            found
        }
        Shape::Node(children) => children
            .iter()
            .all(|child| shape_matches(child, params, at, pay)),
    }
}

impl Vocabulary {
    /// Only the canonical complete pairs already in this vocabulary can
    /// close an inline body's environment. This is a signature/template
    /// check; it emits no membership, domain or witness fact.
    pub(super) fn closed_environment(
        &self,
        environment: &super::type_encoding::TypeEnv,
        pay: &mut impl FnMut(usize) -> bool,
    ) -> bool {
        for index in 0..environment.len() {
            if !pay(1) {
                return false;
            }
            let Ok(index) = u32::try_from(index) else {
                return false;
            };
            let Some(argument) = environment.get(index) else {
                return false;
            };
            let [decoration, identity] = argument.terms_ref();
            if !self.closed_pair(decoration, identity, pay) {
                return false;
            }
        }
        true
    }

    /// Snapshot only after admission by the SAME checker/Analysis meter used
    /// below. Ctx's encoding borrow ends with this closure, before any later
    /// Analysis call can generate bridge operations through that RefCell.
    pub(super) fn new(
        ctx: &Ctx<'_>,
        functions: &[Function],
        signatures: &HashMap<FnId, SpecSig>,
        pay: &mut impl FnMut(usize) -> bool,
    ) -> Option<Self> {
        if !pay(1) {
            return None;
        }
        ctx.with_template_vocabulary(|encoding, nominal_count| {
            let mut out = Self {
                functions: HashMap::new(),
                generic_heads: HashMap::new(),
                closed_arguments: Vec::new(),
                nominal_count,
            };
            for function in functions.iter().chain(encoding.template_functions()) {
                // Reserve name hashing/copying, signature scans/copies and map
                // growth before lookup, comparison or any owned allocation.
                if !pay(function
                    .name
                    .len()
                    .saturating_add(function.params.len())
                    .saturating_add(1)
                    .saturating_mul(4))
                    || !out.registered_sort(function.ret)
                    || function
                        .params
                        .iter()
                        .any(|sort| !out.registered_sort(*sort))
                {
                    return None;
                }
                if let Some(previous) = out.functions.get(&function.name) {
                    if previous != function {
                        return None;
                    }
                } else {
                    out.functions
                        .insert(function.name.clone(), function.clone());
                }
            }
            for argument in encoding.closed_arguments() {
                if !pay(1) {
                    return None;
                }
                let [decoration, identity] = argument.terms_ref();
                if !charge_term(decoration, pay) || !charge_term(identity, pay) {
                    return None;
                }
                out.closed_arguments.push(argument.clone());
            }
            for (owner, signature) in signatures {
                if !pay(1) || signature.owner != *owner {
                    return None;
                }
                if signature.problem.is_some() {
                    continue;
                }
                let prefix = signature.n_types.checked_mul(2)?;
                for output in &signature.outputs {
                    if !pay(output.name.len().saturating_mul(4).saturating_add(1)) {
                        return None;
                    }
                    let actual = out.functions.get(&output.name)?;
                    if prefix > actual.params.len() || actual.ret != output.leaf.sort() {
                        return None;
                    }
                    for (index, sort) in actual.params[..prefix].iter().enumerate() {
                        if !pay(1)
                            || *sort
                                != (if index % 2 == 0 {
                                    Sort::Decoration
                                } else {
                                    Sort::TypeId
                                })
                        {
                            return None;
                        }
                    }
                    let mut at = prefix;
                    for shape in &signature.params {
                        if !shape_matches(shape, &actual.params, &mut at, pay) {
                            return None;
                        }
                    }
                    if at != actual.params.len() {
                        return None;
                    }
                    if signature.n_types != 0 {
                        if let Some(previous) = out.generic_heads.get(&output.name) {
                            if *previous != signature.n_types {
                                return None;
                            }
                        } else {
                            out.generic_heads
                                .insert(output.name.clone(), signature.n_types);
                        }
                    }
                }
            }
            Some(out)
        })
    }

    fn registered_sort(&self, sort: Sort) -> bool {
        match sort {
            Sort::Nominal(index) => (index as usize) < self.nominal_count,
            _ => true,
        }
    }

    fn signature<'a>(
        &'a self,
        registry: &'a Registry,
        name: &str,
        pay: &mut impl FnMut(usize) -> bool,
    ) -> Option<(&'a [Sort], Sort)> {
        // Both name hashing and the canonical registry-name parse are borrowed.
        if !pay(name.len().saturating_mul(4).saturating_add(1)) {
            return None;
        }
        let stored = self.functions.get(name);
        let generated = registry.signature(name);
        match (stored, generated) {
            (Some(a), Some((params, ret))) => {
                if !pay(params.len()) || a.ret != ret || a.params.as_slice() != params {
                    return None;
                }
                Some((&a.params, a.ret))
            }
            (Some(a), None) => Some((&a.params, a.ret)),
            (None, generated) => generated,
        }
    }

    fn closed_pair(
        &self,
        decoration: &Term,
        identity: &Term,
        pay: &mut impl FnMut(usize) -> bool,
    ) -> bool {
        // Borrow terms rather than construct/clone a TypeArgument for lookup.
        // The bounded linear scan pays both structural comparisons first.
        for argument in &self.closed_arguments {
            if !pay(1) {
                return false;
            }
            let [expected_decoration, expected_identity] = argument.terms_ref();
            if !charge_term(decoration, pay)
                || !charge_term(identity, pay)
                || !charge_term(expected_decoration, pay)
                || !charge_term(expected_identity, pay)
            {
                return false;
            }
            if decoration == expected_decoration && identity == expected_identity {
                return true;
            }
        }
        false
    }

    pub(super) fn call_is_typed(
        &self,
        registry: &Registry,
        name: &str,
        args: &[Term],
        sort: Sort,
        pay: &mut impl FnMut(usize) -> bool,
    ) -> bool {
        let Some((params, ret)) = self.signature(registry, name, pay) else {
            return false;
        };
        if !pay(args.len().saturating_add(name.len()))
            || ret != sort
            || params.len() != args.len()
            || params
                .iter()
                .zip(args)
                .any(|(sort, arg)| *sort != arg.sort())
        {
            return false;
        }
        if let Some(arity) = self.generic_heads.get(name) {
            let Some(prefix) = arity.checked_mul(2).and_then(|n| args.get(..n)) else {
                return false;
            };
            for pair in prefix.chunks_exact(2) {
                if !self.closed_pair(&pair[0], &pair[1], pay) {
                    return false;
                }
            }
        }
        true
    }

    /// Check bodies and triggers together: a repeated variable name cannot
    /// silently acquire another sort. The caller retains all native domain
    /// premises inside the formula; this checker creates no predicates.
    pub(super) fn check(
        &self,
        registry: &Registry,
        roots: &[&Term],
        bound: &[(String, LeafTy)],
        pay: &mut impl FnMut(usize) -> bool,
    ) -> bool {
        let mut variables = HashMap::new();
        for (name, leaf) in bound {
            if !native_sort(leaf.sort())
                || !self.registered_sort(leaf.sort())
                || !pay(name.len().saturating_add(1).saturating_mul(4))
                || variables.insert(name.clone(), leaf.sort()).is_some()
            {
                return false;
            }
        }
        roots
            .iter()
            .all(|term| self.term(registry, term, &mut variables, pay))
    }

    pub(super) fn ground(
        &self,
        registry: &Registry,
        root: &Term,
        pay: &mut impl FnMut(usize) -> bool,
    ) -> bool {
        self.term(registry, root, &mut HashMap::new(), pay)
    }

    fn term(
        &self,
        registry: &Registry,
        term: &Term,
        variables: &mut HashMap<String, Sort>,
        pay: &mut impl FnMut(usize) -> bool,
    ) -> bool {
        if !pay(1) {
            return false;
        }
        match term {
            Term::Bool(_) | Term::Int(_) => true,
            Term::Var { name, sort } => {
                if !native_sort(*sort)
                    || !self.registered_sort(*sort)
                    || !pay(name.len().saturating_mul(4))
                {
                    return false;
                }
                match variables.get(name) {
                    Some(previous) => previous == sort,
                    None => {
                        variables.insert(name.clone(), *sort);
                        true
                    }
                }
            }
            Term::Not(value) => {
                value.sort() == Sort::Bool && self.term(registry, value, variables, pay)
            }
            Term::Neg(value) => {
                value.sort() == Sort::Int && self.term(registry, value, variables, pay)
            }
            Term::And(values) | Term::Or(values) => values.iter().all(|value| {
                value.sort() == Sort::Bool && self.term(registry, value, variables, pay)
            }),
            Term::Implies(a, b) => {
                a.sort() == Sort::Bool
                    && b.sort() == Sort::Bool
                    && self.term(registry, a, variables, pay)
                    && self.term(registry, b, variables, pay)
            }
            Term::Cmp(op, a, b) => {
                a.sort() == b.sort()
                    && (*op == CmpOp::Eq || a.sort() == Sort::Int)
                    && self.term(registry, a, variables, pay)
                    && self.term(registry, b, variables, pay)
            }
            Term::Arith(_, a, b) => {
                a.sort() == Sort::Int
                    && b.sort() == Sort::Int
                    && self.term(registry, a, variables, pay)
                    && self.term(registry, b, variables, pay)
            }
            Term::Ite(c, a, b, sort) => {
                c.sort() == Sort::Bool
                    && a.sort() == *sort
                    && b.sort() == *sort
                    && self.term(registry, c, variables, pay)
                    && self.term(registry, a, variables, pay)
                    && self.term(registry, b, variables, pay)
            }
            Term::Call { name, args, sort } => {
                pay(name.len().saturating_add(args.len()))
                    && self.call_is_typed(registry, name, args, *sort, pay)
                    && args
                        .iter()
                        .all(|arg| self.term(registry, arg, variables, pay))
            }
        }
    }
}

#[cfg(test)]
pub(super) mod tests;
