//! Shared prepaid fact closure for both UF and arithmetic relevance searches.
//! A failure returns no selection; it never substitutes an empty/partial fact
//! list into a witness. Every walk, key operation and allocation uses the
//! caller's remaining Analysis grant.
use super::super::term::Term;
use super::{TooBig, R};
use std::collections::HashMap;
#[cfg(test)]
use std::collections::HashSet;
use std::hash::Hash;

const MAX_DEPTH: usize = 256;

mod prepared;
pub(super) use prepared::Prepared;

fn tick(pay: &mut impl FnMut(usize) -> bool, cost: usize) -> R<()> {
    if pay(cost) {
        Ok(())
    } else {
        Err(TooBig)
    }
}
fn scaled(value: usize, multiplier: usize) -> R<usize> {
    value
        .checked_mul(multiplier)
        .and_then(|n| n.checked_add(1))
        .ok_or(TooBig)
}
fn children<'a>(term: &'a Term, visit: &mut impl FnMut(&'a Term) -> R<()>) -> R<()> {
    match term {
        Term::Bool(_) | Term::Int(_) | Term::Var { .. } => {}
        Term::Not(a) | Term::Neg(a) => visit(a)?,
        Term::And(args) | Term::Or(args) | Term::Call { args, .. } => {
            for arg in args {
                visit(arg)?;
            }
        }
        Term::Implies(a, b) | Term::Cmp(_, a, b) | Term::Arith(_, a, b) => {
            visit(a)?;
            visit(b)?;
        }
        Term::Ite(c, a, b, _) => {
            visit(c)?;
            visit(a)?;
            visit(b)?;
        }
    }
    Ok(())
}

/// Admit the borrowed census and subsequent full-tree clone/hash/equality
/// work, paying each node/name before reading its children/payload. The
/// finite depth limit also precedes any recursive derived Hash/Eq/Clone.
pub(super) fn term_work(term: &Term, pay: &mut impl FnMut(usize) -> bool) -> R<usize> {
    fn walk(term: &Term, pay: &mut impl FnMut(usize) -> bool, depth: usize) -> R<usize> {
        tick(pay, 4)?;
        if depth >= MAX_DEPTH {
            return Err(TooBig);
        }
        if let Term::Var { name, .. } | Term::Call { name, .. } = term {
            tick(pay, scaled(name.len(), 4)?)?;
        }
        let mut nodes = 1usize;
        children(term, &mut |child| {
            nodes = nodes
                .checked_add(walk(child, pay, depth + 1)?)
                .ok_or(TooBig)?;
            Ok(())
        })?;
        Ok(nodes)
    }
    walk(term, pay, 0)
}

/// Reserve potential table growth before it can rehash existing structural
/// keys. Iteration is charged by bucket capacity, not the occupied length.
/// A map which already has a spare slot performs no resize or extra scan.
pub(super) fn reserve_cache<K: Eq + Hash, V, P: FnMut(usize) -> bool>(
    cache: &mut HashMap<K, V>,
    pay: &mut P,
    charge_key: &mut impl FnMut(&K, &mut P) -> R<()>,
) -> R<()> {
    if cache.len() < cache.capacity() {
        return Ok(());
    }
    tick(
        pay,
        scaled(cache.capacity().checked_add(1).ok_or(TooBig)?, 16)?,
    )?;
    for key in cache.keys() {
        charge_key(key, pay)?;
    }
    cache.reserve(1);
    Ok(())
}

#[cfg(test)]
fn subterms<'a>(
    term: &'a Term,
    seen: &mut HashSet<&'a Term>,
    pay: &mut impl FnMut(usize) -> bool,
) -> R<()> {
    tick(pay, 1)?;
    if matches!(term, Term::Bool(_) | Term::Int(_)) {
        return Ok(());
    }
    term_work(term, pay)?; // before recursive Hash/Eq in insert
    if !seen.insert(term) {
        return Ok(());
    }
    children(term, &mut |child| subterms(child, seen, pay))
}
#[cfg(test)]
fn shares(term: &Term, seen: &HashSet<&Term>, pay: &mut impl FnMut(usize) -> bool) -> R<bool> {
    tick(pay, 1)?;
    if matches!(term, Term::Bool(_) | Term::Int(_)) {
        return Ok(false);
    }
    term_work(term, pay)?; // before recursive Hash/Eq in contains
    if seen.contains(term) {
        return Ok(true);
    }
    let mut found = false;
    children(term, &mut |child| {
        tick(pay, 1)?;
        if !found {
            found = shares(child, seen, pay)?;
        }
        Ok(())
    })?;
    Ok(found)
}
#[cfg(test)]
fn calls_any(term: &Term, names: &HashSet<&str>, pay: &mut impl FnMut(usize) -> bool) -> R<bool> {
    tick(pay, 1)?;
    if let Term::Call { name, .. } = term {
        tick(pay, scaled(name.len(), 4)?)?;
        if names.contains(name.as_str()) {
            return Ok(true);
        }
    }
    let mut found = false;
    children(term, &mut |child| {
        tick(pay, 1)?;
        if !found {
            found = calls_any(child, names, pay)?;
        }
        Ok(())
    })?;
    Ok(found)
}

#[derive(Clone, Copy)]
pub(super) enum Event {
    InputFact,
    Pass,
    FactRow,
}

#[cfg(test)]
pub(super) fn close(
    list: &[(usize, Term)],
    current: usize,
    node: &Term,
    pay: &mut impl FnMut(usize) -> bool,
) -> R<Vec<usize>> {
    close_impl(list, current, node, pay, &mut |_| {})
}

#[cfg(test)]
fn close_impl(
    list: &[(usize, Term)],
    current: usize,
    node: &Term,
    pay: &mut impl FnMut(usize) -> bool,
    observer: &mut impl FnMut(Event),
) -> R<Vec<usize>> {
    tick(pay, 1)?;
    // The paid whole-input census gives a true upper bound on distinct
    // borrowed subterms. Reserve once, so subsequent inserts cannot hide a
    // resize/rehash of previously seen structural keys.
    let mut capacity = term_work(node, pay)?;
    for (_, fact) in list {
        tick(pay, 1)?;
        observer(Event::InputFact);
        capacity = capacity.checked_add(term_work(fact, pay)?).ok_or(TooBig)?;
    }
    tick(pay, scaled(capacity, 4)?)?;
    let mut seen = HashSet::with_capacity(capacity);
    subterms(node, &mut seen, pay)?;
    tick(pay, scaled(list.len(), 3)?)?;
    let mut chosen = vec![false; list.len()];
    loop {
        tick(pay, 1)?; // every closure pass, including the final unchanged pass
        observer(Event::Pass);
        tick(pay, seen.capacity().checked_add(1).ok_or(TooBig)?)?;
        tick(pay, scaled(seen.len(), 4)?)?;
        let mut names = HashSet::with_capacity(seen.len());
        for term in &seen {
            tick(pay, 1)?;
            if let Term::Call { name, .. } = term {
                tick(pay, scaled(name.len(), 4)?)?;
                names.insert(name.as_str());
            }
        }
        let mut changed = false;
        for (k, (formula, fact)) in list.iter().enumerate() {
            tick(pay, 1)?; // includes chosen/current rows before their fast skip
            observer(Event::FactRow);
            if chosen[k] || *formula == current {
                continue;
            }
            if !shares(fact, &seen, pay)? && !calls_any(fact, &names, pay)? {
                continue;
            }
            chosen[k] = true;
            changed = true;
            subterms(fact, &mut seen, pay)?;
        }
        if !changed {
            break;
        }
    }
    tick(pay, scaled(list.len(), 2)?)?;
    let mut out = Vec::with_capacity(list.len());
    for (k, selected) in chosen.into_iter().enumerate() {
        tick(pay, 1)?;
        if selected {
            out.push(k);
        }
    }
    Ok(out)
}
