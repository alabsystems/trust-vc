// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The same typed matcher checks instance unwind contracts before use.
use super::*;
use crate::{LocalId, UnwindSpec};
use std::cell::OnceCell;

pub(crate) fn matches(
    functions: &Functions<'_>,
    original: &FnDecl,
    instance: &FnDecl,
    validated: &OnceCell<HashSet<FnId>>,
) -> bool {
    let Some(origin) = &instance.attrs.instance else {
        return false;
    };
    let matcher = Matcher {
        functions,
        arguments: &origin.type_args,
        checked_initializer: false,
        depth: Cell::new(0),
        parameters: Some((&original.params, &instance.params)),
    };
    // This is the existing instance-correspondence ceiling, never a solver
    // allowance or a refill of a partially consumed match.
    let mut budget = MATCH_WORK;
    let mut dependencies = HashSet::new();
    if !matcher.unwind(
        &original.unwind,
        &instance.unwind,
        &mut budget,
        &mut dependencies,
    ) {
        return false;
    }
    if dependencies.is_empty() {
        return true;
    }
    // The immutable WF index shares this closure across header matches. Its
    // initializer checks Spec instance bodies directly through Matcher, never
    // this header entry point, so it cannot recursively initialize the cell.
    let checked = validated.get_or_init(|| validated_origins(functions));
    dependencies.iter().all(|id| checked.contains(id))
}

impl Matcher<'_, '_> {
    pub(super) fn local(&self, formal: LocalId, actual: LocalId, budget: &mut usize) -> bool {
        let Some((left, right)) = self.parameters else {
            return formal == actual;
        };
        let Some(remaining) = budget.checked_sub(left.len()) else {
            return false;
        };
        *budget = remaining;
        match left.iter().position(|local| *local == formal) {
            Some(index) => right.get(index) == Some(&actual),
            None => formal == actual,
        }
    }

    pub(super) fn unwind(
        &self,
        formal: &Option<UnwindSpec>,
        actual: &Option<UnwindSpec>,
        budget: &mut usize,
        dependencies: &mut HashSet<FnId>,
    ) -> bool {
        match (formal, actual) {
            (None, None)
            | (Some(UnwindSpec::NoUnwind), Some(UnwindSpec::NoUnwind))
            | (Some(UnwindSpec::MayUnwind), Some(UnwindSpec::MayUnwind)) => true,
            (Some(UnwindSpec::NoUnwindWhen(a)), Some(UnwindSpec::NoUnwindWhen(b))) => {
                self.expr(a, b, budget, dependencies)
            }
            _ => false,
        }
    }
}
