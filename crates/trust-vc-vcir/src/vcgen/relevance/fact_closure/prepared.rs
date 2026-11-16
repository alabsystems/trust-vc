//! Exact, prepaid connectivity for one immutable bank of fact rows.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
use super::{reserve_cache, scaled, term_work, tick, MAX_DEPTH, R};
use crate::vcgen::term::{ArithOp, CmpOp, Sort, Term};
use std::collections::HashMap;

#[derive(PartialEq, Eq, Hash)]
enum Key {
    Bool(bool),
    Int(i128),
    Var(String, Sort),
    Call(String, Sort, Vec<usize>),
    Not(usize),
    Neg(usize),
    And(Vec<usize>),
    Or(Vec<usize>),
    Implies(usize, usize),
    Cmp(CmpOp, usize, usize),
    Arith(ArithOp, usize, usize),
    Ite(usize, usize, usize, Sort),
}

impl Key {
    fn work(&self, pay: &mut impl FnMut(usize) -> bool) -> R<()> {
        tick(pay, 8)?;
        match self {
            Self::Var(name, _) | Self::Call(name, _, _) => {
                tick(pay, scaled(name.len(), 4)?)?;
            }
            _ => {}
        }
        match self {
            Self::Call(_, _, args) | Self::And(args) | Self::Or(args) => {
                tick(pay, scaled(args.len(), 4)?)?;
            }
            _ => {}
        }
        Ok(())
    }

    fn new(term: &Term, ids: Vec<usize>, pay: &mut impl FnMut(usize) -> bool) -> R<Self> {
        tick(pay, 8)?;
        if let Term::Var { name, .. } | Term::Call { name, .. } = term {
            tick(pay, scaled(name.len(), 4)?)?;
        }
        Ok(match term {
            Term::Bool(value) => Self::Bool(*value),
            Term::Int(value) => Self::Int(*value),
            Term::Var { name, sort } => Self::Var(name.clone(), *sort),
            Term::Call { name, sort, .. } => Self::Call(name.clone(), *sort, ids),
            Term::Not(_) => Self::Not(ids[0]),
            Term::Neg(_) => Self::Neg(ids[0]),
            Term::And(_) => Self::And(ids),
            Term::Or(_) => Self::Or(ids),
            Term::Implies(..) => Self::Implies(ids[0], ids[1]),
            Term::Cmp(op, ..) => Self::Cmp(*op, ids[0], ids[1]),
            Term::Arith(op, ..) => Self::Arith(*op, ids[0], ids[1]),
            Term::Ite(_, _, _, sort) => Self::Ite(ids[0], ids[1], ids[2], *sort),
        })
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Feature {
    Term(usize),
    Call(usize),
}

fn push<T>(items: &mut Vec<T>, value: T, pay: &mut impl FnMut(usize) -> bool) -> R<()> {
    if items.len() == items.capacity() {
        tick(
            pay,
            scaled(items.capacity().checked_add(1).ok_or(super::TooBig)?, 8)?,
        )?;
        items.reserve(1);
    }
    tick(pay, 1)?;
    items.push(value);
    Ok(())
}

fn child_count(term: &Term) -> usize {
    match term {
        Term::Bool(_) | Term::Int(_) | Term::Var { .. } => 0,
        Term::Not(_) | Term::Neg(_) => 1,
        Term::And(args) | Term::Or(args) | Term::Call { args, .. } => args.len(),
        Term::Implies(..) | Term::Cmp(..) | Term::Arith(..) => 2,
        Term::Ite(..) => 3,
    }
}

/// Structural IDs are backed by complete shallow keys, never a digest alone.
/// Literal IDs participate in parent identity but do not connect fact rows.
pub(crate) struct Prepared {
    terms: HashMap<Key, usize>,
    calls: HashMap<String, usize>,
    term_rows: Vec<Vec<usize>>,
    call_rows: Vec<Vec<usize>>,
    formulas: Vec<usize>,
    row_features: Vec<Vec<Feature>>,
}

impl Prepared {
    pub(crate) fn new(
        list: &[(usize, Term)],
        pay: &mut impl FnMut(usize) -> bool,
        observer: &mut impl FnMut(super::Event),
    ) -> R<Self> {
        tick(pay, scaled(list.len(), 8)?)?;
        let mut out = Self {
            terms: HashMap::new(),
            calls: HashMap::new(),
            term_rows: Vec::new(),
            call_rows: Vec::new(),
            formulas: Vec::with_capacity(list.len()),
            row_features: Vec::with_capacity(list.len()),
        };
        for (row, (formula, fact)) in list.iter().enumerate() {
            tick(pay, 2)?;
            observer(super::Event::InputFact);
            let capacity = term_work(fact, pay)?.checked_mul(2).ok_or(super::TooBig)?;
            tick(pay, scaled(capacity, 4)?)?;
            let mut features = Vec::with_capacity(capacity);
            out.intern(fact, 0, &mut features, pay)?;
            let comparisons = features
                .len()
                .checked_mul(features.len().max(1).ilog2() as usize + 1)
                .ok_or(super::TooBig)?;
            tick(pay, scaled(comparisons, 4)?)?;
            features.sort_unstable();
            features.dedup();
            for feature in &features {
                tick(pay, 1)?;
                let rows = match *feature {
                    Feature::Term(id) => &mut out.term_rows[id],
                    Feature::Call(id) => &mut out.call_rows[id],
                };
                push(rows, row, pay)?;
            }
            out.formulas.push(*formula);
            out.row_features.push(features);
        }
        Ok(out)
    }

    fn intern(
        &mut self,
        term: &Term,
        depth: usize,
        features: &mut Vec<Feature>,
        pay: &mut impl FnMut(usize) -> bool,
    ) -> R<usize> {
        tick(pay, 4)?;
        if depth >= MAX_DEPTH {
            return Err(super::TooBig);
        }
        let count = child_count(term);
        tick(pay, scaled(count, 4)?)?;
        let mut children = Vec::with_capacity(count);
        super::children(term, &mut |child| {
            children.push(self.intern(child, depth + 1, features, pay)?);
            Ok(())
        })?;
        let key = Key::new(term, children, pay)?;
        key.work(pay)?;
        let id = if let Some(id) = self.terms.get(&key) {
            *id
        } else {
            reserve_cache(&mut self.terms, pay, &mut |key, pay| key.work(pay))?;
            key.work(pay)?;
            let id = self.term_rows.len();
            push(&mut self.term_rows, Vec::new(), pay)?;
            self.terms.insert(key, id);
            id
        };
        if !matches!(term, Term::Bool(_) | Term::Int(_)) {
            push(features, Feature::Term(id), pay)?;
        }
        if let Term::Call { name, .. } = term {
            tick(pay, scaled(name.len(), 4)?)?;
            let call = if let Some(id) = self.calls.get(name) {
                *id
            } else {
                reserve_cache(&mut self.calls, pay, &mut |name, pay| {
                    tick(pay, scaled(name.len(), 4)?)
                })?;
                tick(pay, scaled(name.len(), 8)?)?;
                let id = self.call_rows.len();
                push(&mut self.call_rows, Vec::new(), pay)?;
                self.calls.insert(name.clone(), id);
                id
            };
            push(features, Feature::Call(call), pay)?;
        }
        Ok(id)
    }

    fn lookup(
        &self,
        term: &Term,
        depth: usize,
        features: &mut Vec<Feature>,
        pay: &mut impl FnMut(usize) -> bool,
    ) -> R<Option<usize>> {
        tick(pay, 4)?;
        if depth >= MAX_DEPTH {
            return Err(super::TooBig);
        }
        let count = child_count(term);
        tick(pay, scaled(count, 4)?)?;
        let mut children = Vec::with_capacity(count);
        let mut known = true;
        super::children(term, &mut |child| {
            match self.lookup(child, depth + 1, features, pay)? {
                Some(id) => children.push(id),
                None => known = false,
            }
            Ok(())
        })?;
        let id = if known {
            let key = Key::new(term, children, pay)?;
            key.work(pay)?;
            self.terms.get(&key).copied()
        } else {
            None
        };
        if !matches!(term, Term::Bool(_) | Term::Int(_)) {
            if let Some(id) = id {
                push(features, Feature::Term(id), pay)?;
            }
        }
        if let Term::Call { name, .. } = term {
            tick(pay, scaled(name.len(), 4)?)?;
            if let Some(id) = self.calls.get(name) {
                push(features, Feature::Call(*id), pay)?;
            }
        }
        Ok(id)
    }

    pub(crate) fn close(
        &self,
        current: usize,
        node: &Term,
        pay: &mut impl FnMut(usize) -> bool,
        observer: &mut impl FnMut(super::Event),
    ) -> R<Vec<usize>> {
        let capacity = term_work(node, pay)?.checked_mul(2).ok_or(super::TooBig)?;
        tick(pay, scaled(capacity, 4)?)?;
        let mut initial = Vec::with_capacity(capacity);
        self.lookup(node, 0, &mut initial, pay)?;
        let size = self
            .term_rows
            .len()
            .checked_add(self.call_rows.len())
            .ok_or(super::TooBig)?;
        tick(
            pay,
            scaled(
                size.checked_add(self.formulas.len()).ok_or(super::TooBig)?,
                8,
            )?,
        )?;
        let mut terms = vec![false; self.term_rows.len()];
        let mut calls = vec![false; self.call_rows.len()];
        let mut chosen = vec![false; self.formulas.len()];
        let mut queue = Vec::with_capacity(size);
        fn enqueue(
            feature: Feature,
            terms: &mut [bool],
            calls: &mut [bool],
            queue: &mut Vec<Feature>,
            pay: &mut impl FnMut(usize) -> bool,
        ) -> R<()> {
            tick(pay, 2)?;
            let seen = match feature {
                Feature::Term(id) => &mut terms[id],
                Feature::Call(id) => &mut calls[id],
            };
            if !*seen {
                *seen = true;
                push(queue, feature, pay)?;
            }
            Ok(())
        }
        for feature in initial {
            enqueue(feature, &mut terms, &mut calls, &mut queue, pay)?;
        }
        let mut next = 0;
        while next < queue.len() {
            tick(pay, 2)?;
            observer(super::Event::Pass);
            let rows = match queue[next] {
                Feature::Term(id) => &self.term_rows[id],
                Feature::Call(id) => &self.call_rows[id],
            };
            next += 1;
            for &row in rows {
                tick(pay, 2)?;
                observer(super::Event::FactRow);
                if chosen[row] || self.formulas[row] == current {
                    continue;
                }
                chosen[row] = true;
                for &feature in &self.row_features[row] {
                    enqueue(feature, &mut terms, &mut calls, &mut queue, pay)?;
                }
            }
        }
        tick(pay, scaled(chosen.len(), 2)?)?;
        let mut out = Vec::with_capacity(chosen.len());
        for (row, selected) in chosen.into_iter().enumerate() {
            tick(pay, 1)?;
            if selected {
                out.push(row);
            }
        }
        Ok(out)
    }
}
