//! Occurrence-local receipts from the actual scalar simplifier.
//!
//! A receipt starts at a complete canonical clip, follows only the same
//! formula's actual rewrite calls, and becomes material only when that
//! clip's own fallback branch is selected. It is never a fallback-name map.
use super::*;
use crate::IntRange;

type Pay<'a> = dyn FnMut(usize) -> bool + 'a;
fn pay(work: &mut Pay<'_>, n: usize) -> R<()> {
    if work(n) {
        Ok(())
    } else {
        Err(TooBig)
    }
}
fn term(work: &mut Pay<'_>, t: &Term) -> R<()> {
    fact_closure::term_work(t, &mut |n| work(n)).map(|_| ())
}
fn equal(work: &mut Pay<'_>, a: &Term, b: &Term) -> R<bool> {
    equality::equal(work, a, b)
}
mod equality;
fn owned(work: &mut Pay<'_>, t: &Term) -> R<Term> {
    term(work, t)?;
    Ok(t.clone())
}

#[derive(Clone)]
enum State {
    Pending { fallback_branch: usize },
    Active,
}
#[derive(Clone)]
struct Origin {
    source: Term,
    source_operand: Term,
    operand_image: Term,
    range: IntRange,
    image: Term,
    path: Vec<usize>,
    state: State,
}
impl Origin {
    fn clone_paid(&self, work: &mut Pay<'_>) -> R<Self> {
        term(work, &self.source)?;
        term(work, &self.source_operand)?;
        term(work, &self.operand_image)?;
        term(work, &self.image)?;
        pay(work, self.path.len().saturating_add(4))?;
        Ok(self.clone())
    }
}

fn cloned_origins(origins: &[Origin], work: &mut Pay<'_>) -> R<Vec<Origin>> {
    pay(work, origins.len().saturating_add(1))?;
    let mut copied = Vec::with_capacity(origins.len());
    for origin in origins {
        copied.push(origin.clone_paid(work)?)
    }
    Ok(copied)
}

fn consistent(origin: &Origin, image: &Term, work: &mut Pay<'_>) -> R<bool> {
    term(work, &origin.source)?;
    if super::super::spec::clip_fallback(&origin.source, origin.range, &mut |n| work(n)).is_none() {
        return Ok(false);
    }
    if !equal(
        work,
        child(&origin.source, 1).ok_or(TooBig)?,
        &origin.source_operand,
    )? {
        return Ok(false);
    }
    let fallback_image = match origin.state {
        State::Active => image,
        State::Pending { fallback_branch } => {
            if !matches!(image, Term::Ite(_, _, _, Sort::Int)) || !matches!(fallback_branch, 1 | 2)
            {
                return Ok(false);
            }
            child(image, fallback_branch).ok_or(TooBig)?
        }
    };
    if !fallback(fallback_image, origin.range, work)? {
        return Ok(false);
    }
    equal(
        work,
        child(fallback_image, 0).ok_or(TooBig)?,
        &origin.operand_image,
    )
}

pub(super) struct Formula<P> {
    pub(super) term: Term,
    pub(super) tag: P,
    origins: Vec<Origin>,
}
impl<P> Formula<P> {
    pub(super) fn plain(term: Term, tag: P) -> Self {
        Self {
            term,
            tag,
            origins: Vec::new(),
        }
    }
    pub(super) fn sites(&self, work: &mut Pay<'_>) -> R<Sites> {
        if self.origins.is_empty() {
            return Ok(Sites::default());
        }
        let mut sites = Sites::default();
        pay(work, self.origins.len().saturating_add(1))?;
        sites.0.reserve_exact(self.origins.len());
        for origin in &self.origins {
            pay(work, 1)?;
            if !matches!(origin.state, State::Active) {
                continue;
            }
            let image = at(&self.term, &origin.path, work)?;
            if !equal(work, image, &origin.image)? || !consistent(origin, image, work)? {
                return Err(TooBig);
            }
            sites
                .0
                .push((image as *const Term as usize, origin.clone_paid(work)?));
        }
        Ok(sites)
    }
}

/// This table exists only for the live formula currently traversed by rel.
/// It is removed around body/instance expansion and cleared on every exit.
#[derive(Default)]
pub(super) struct Sites(Vec<(usize, Origin)>);
impl Sites {
    pub(super) fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

fn at<'t>(mut t: &'t Term, path: &[usize], work: &mut Pay<'_>) -> R<&'t Term> {
    for &index in path {
        pay(work, 1)?;
        t = child(t, index).ok_or(TooBig)?;
    }
    Ok(t)
}
fn child(t: &Term, index: usize) -> Option<&Term> {
    match t {
        Term::Not(a) | Term::Neg(a) => (index == 0).then_some(&**a),
        Term::And(xs) | Term::Or(xs) | Term::Call { args: xs, .. } => xs.get(index),
        Term::Implies(a, b) | Term::Cmp(_, a, b) | Term::Arith(_, a, b) => match index {
            0 => Some(a),
            1 => Some(b),
            _ => None,
        },
        Term::Ite(c, a, b, _) => match index {
            0 => Some(c),
            1 => Some(a),
            2 => Some(b),
            _ => None,
        },
        Term::Bool(_) | Term::Int(_) | Term::Var { .. } => None,
    }
}
fn arity(t: &Term) -> usize {
    match t {
        Term::Not(_) | Term::Neg(_) => 1,
        Term::And(xs) | Term::Or(xs) | Term::Call { args: xs, .. } => xs.len(),
        Term::Implies(..) | Term::Cmp(..) | Term::Arith(..) => 2,
        Term::Ite(..) => 3,
        Term::Bool(_) | Term::Int(_) | Term::Var { .. } => 0,
    }
}
fn rebuilt(t: &Term, kids: Vec<Term>, work: &mut Pay<'_>) -> R<Term> {
    pay(work, kids.len().saturating_add(4))?;
    if kids.len() != arity(t) {
        return Err(TooBig);
    }
    let mut xs = kids.into_iter();
    Ok(match t {
        Term::Bool(_) | Term::Int(_) | Term::Var { .. } => owned(work, t)?,
        Term::Not(_) => Term::Not(Box::new(xs.next().ok_or(TooBig)?)),
        Term::Neg(_) => Term::Neg(Box::new(xs.next().ok_or(TooBig)?)),
        Term::And(_) => Term::And(xs.collect()),
        Term::Or(_) => Term::Or(xs.collect()),
        Term::Implies(..) => Term::Implies(
            Box::new(xs.next().ok_or(TooBig)?),
            Box::new(xs.next().ok_or(TooBig)?),
        ),
        Term::Cmp(op, ..) => Term::Cmp(
            *op,
            Box::new(xs.next().ok_or(TooBig)?),
            Box::new(xs.next().ok_or(TooBig)?),
        ),
        Term::Arith(op, ..) => Term::Arith(
            *op,
            Box::new(xs.next().ok_or(TooBig)?),
            Box::new(xs.next().ok_or(TooBig)?),
        ),
        Term::Ite(_, _, _, sort) => Term::Ite(
            Box::new(xs.next().ok_or(TooBig)?),
            Box::new(xs.next().ok_or(TooBig)?),
            Box::new(xs.next().ok_or(TooBig)?),
            *sort,
        ),
        Term::Call { name, sort, .. } => {
            pay(work, name.len())?;
            Term::Call {
                name: name.clone(),
                args: xs.collect(),
                sort: *sort,
            }
        }
    })
}

/// Only a unique surviving occurrence can transport a receipt. Two equal
/// images are deliberately ambiguous even when one could have survived.
fn unique(t: &Term, image: &Term, work: &mut Pay<'_>) -> R<Option<Vec<usize>>> {
    fn visit(
        t: &Term,
        image: &Term,
        path: &mut Vec<usize>,
        found: &mut Option<Vec<usize>>,
        count: &mut usize,
        work: &mut Pay<'_>,
    ) -> R<()> {
        pay(work, 1)?;
        if *count > 1 {
            return Ok(());
        }
        if equal(work, t, image)? {
            *count += 1;
            if *count == 1 {
                pay(work, path.len().saturating_add(1))?;
                *found = Some(path.clone());
            }
            return Ok(());
        }
        for index in 0..arity(t) {
            pay(work, path.len().saturating_add(2))?;
            path.push(index);
            visit(
                child(t, index).ok_or(TooBig)?,
                image,
                path,
                found,
                count,
                work,
            )?;
            path.pop();
            if *count > 1 {
                break;
            }
        }
        Ok(())
    }
    let mut found = None;
    let mut count = 0;
    visit(t, image, &mut Vec::new(), &mut found, &mut count, work)?;
    Ok(if count == 1 { found } else { None })
}
fn fallback(t: &Term, range: IntRange, work: &mut Pay<'_>) -> R<bool> {
    term(work, t)?;
    let Term::Call { name, args, sort } = t else {
        return Ok(false);
    };
    pay(work, name.len().saturating_add(64))?;
    Ok(*sort == Sort::Int
        && args.len() == 1
        && args[0].sort() == Sort::Int
        && *name == super::super::spec::clip_oob_name(range))
}

struct Traced {
    term: Term,
    origins: Vec<Origin>,
}
struct Frame {
    own: Vec<Origin>,
    children: Vec<Traced>,
}
/// Observer used by the ACTUAL Simp::go traversal, not a second rewriter.
pub(super) struct Trace<'a> {
    ranges: &'a HashSet<IntRange>,
    capture_original: bool,
    incoming: Vec<(usize, Origin)>,
    frames: Vec<Frame>,
    result: Option<Traced>,
}
impl<'a> Trace<'a> {
    fn new(
        t: &Term,
        origins: Vec<Origin>,
        ranges: &'a HashSet<IntRange>,
        capture_original: bool,
        work: &mut Pay<'_>,
    ) -> R<Self> {
        pay(work, origins.len().saturating_add(1))?;
        let mut incoming = Vec::with_capacity(origins.len());
        for origin in origins {
            let image = at(t, &origin.path, work)?;
            if !equal(work, image, &origin.image)? || !consistent(&origin, image, work)? {
                return Err(TooBig);
            }
            incoming.push((image as *const Term as usize, origin));
        }
        Ok(Self {
            ranges,
            capture_original,
            incoming,
            frames: Vec::new(),
            result: None,
        })
    }
    pub(super) fn enter(&mut self, t: &Term, work: &mut Pay<'_>) -> R<()> {
        pay(work, 1)?;
        if self.frames.len() >= 256 {
            return Err(TooBig);
        }
        // Admit the existing recursive rewrite and every later tracking copy.
        term(work, t)?;
        pay(
            work,
            self.incoming
                .len()
                .saturating_add(self.frames.capacity())
                .saturating_add(4),
        )?;
        let mut own = Vec::new();
        let address = t as *const Term as usize;
        let mut index = 0;
        while index < self.incoming.len() {
            pay(work, 2)?;
            if self.incoming[index].0 == address {
                pay(work, own.capacity().saturating_add(2))?;
                own.push(self.incoming.swap_remove(index).1);
            } else {
                index += 1
            }
        }
        // Only the original input traversal can mint an origin. A later
        // simplifier-created canonical shape cannot create source provenance.
        if self.capture_original {
            pay(work, self.ranges.capacity().saturating_add(1))?;
            for &range in self.ranges {
                pay(work, 1)?;
                if super::super::spec::clip_fallback(t, range, &mut |n| work(n)).is_none() {
                    continue;
                }
                let mut duplicate = false;
                for origin in &own {
                    pay(work, 1)?;
                    if origin.range == range && equal(work, &origin.source, t)? {
                        duplicate = true;
                        break;
                    }
                }
                if !duplicate {
                    pay(work, own.capacity().saturating_add(4))?;
                    let operand = child(t, 1).ok_or(TooBig)?;
                    own.push(Origin {
                        source: owned(work, t)?,
                        source_operand: owned(work, operand)?,
                        operand_image: owned(work, operand)?,
                        range,
                        image: owned(work, t)?,
                        path: Vec::new(),
                        state: State::Pending { fallback_branch: 2 },
                    });
                }
            }
        }
        pay(work, arity(t).saturating_add(1))?;
        self.frames.push(Frame {
            own,
            children: Vec::with_capacity(arity(t)),
        });
        Ok(())
    }
    pub(super) fn exit(&mut self, t: &Term, output: &Term, work: &mut Pay<'_>) -> R<()> {
        let frame = self.frames.pop().ok_or(TooBig)?;
        pay(work, frame.children.len().saturating_add(1))?;
        let mut children = Vec::with_capacity(frame.children.len());
        let mut inherited = Vec::new();
        for (index, child) in frame.children.into_iter().enumerate() {
            children.push(child.term);
            for mut origin in child.origins {
                pay(
                    work,
                    origin
                        .path
                        .len()
                        .saturating_add(inherited.capacity())
                        .saturating_add(4),
                )?;
                origin.path.insert(0, index);
                inherited.push(origin);
            }
        }
        let before = rebuilt(t, children, work)?;
        let mut origins = Vec::new();
        for mut origin in inherited {
            let reached = at(&before, &origin.path, work)?;
            if !equal(work, reached, &origin.image)? {
                return Err(TooBig);
            }
            if unique(&before, &origin.image, work)?.is_none() {
                continue;
            }
            let Some(path) = unique(output, &origin.image, work)? else {
                continue;
            };
            if let State::Pending { fallback_branch } = origin.state {
                let call = child(&origin.image, fallback_branch).ok_or(TooBig)?;
                // An interpreted ITE can be rebuilt from other children.
                // Its opaque fallback occurrence must independently retain
                // unique lineage, not merely an equal ITE value.
                if unique(&before, call, work)?.is_none() || unique(output, call, work)?.is_none() {
                    continue;
                }
            }
            pay(work, origins.capacity().saturating_add(1))?;
            origin.path = path;
            origins.push(origin);
        }
        for mut origin in frame.own {
            pay(work, 1)?;
            let state = match origin.state {
                State::Active => {
                    if !fallback(&before, origin.range, work)? || !equal(work, &before, output)? {
                        continue;
                    }
                    origin.operand_image = owned(work, child(output, 0).ok_or(TooBig)?)?;
                    State::Active
                }
                State::Pending { fallback_branch } => {
                    let Term::Ite(condition, _, _, Sort::Int) = &before else {
                        continue;
                    };
                    let chosen = child(&before, fallback_branch).ok_or(TooBig)?;
                    let value_branch = match fallback_branch {
                        1 => 2,
                        2 => 1,
                        _ => return Err(TooBig),
                    };
                    let value = child(&before, value_branch).ok_or(TooBig)?;
                    if !fallback(chosen, origin.range, work)? {
                        continue;
                    }
                    let argument = child(chosen, 0).ok_or(TooBig)?;
                    if !equal(work, argument, value)? {
                        continue;
                    }
                    origin.operand_image = owned(work, value)?;
                    let selected = match condition.as_bool() {
                        Some(true) => Some(1),
                        Some(false) => Some(2),
                        None => None,
                    };
                    if selected == Some(fallback_branch) && equal(work, chosen, output)? {
                        State::Active
                    } else if let Term::Ite(_, _, _, Sort::Int) = output {
                        let Some(path) = unique(output, chosen, work)? else {
                            continue;
                        };
                        if path.len() != 1 || !matches!(path[0], 1 | 2) {
                            continue;
                        }
                        State::Pending {
                            fallback_branch: path[0],
                        }
                    } else {
                        continue;
                    }
                }
            };
            pay(work, origins.capacity().saturating_add(2))?;
            origin.state = state;
            origin.image = owned(work, output)?;
            origin.path.clear();
            origins.push(origin);
        }
        let result = Traced {
            term: owned(work, output)?,
            origins,
        };
        if let Some(parent) = self.frames.last_mut() {
            pay(work, parent.children.capacity().saturating_add(1))?;
            parent.children.push(result);
        } else {
            self.result = Some(result)
        }
        Ok(())
    }
    fn finish(self) -> R<Traced> {
        if !self.frames.is_empty() || !self.incoming.is_empty() {
            return Err(TooBig);
        }
        self.result.ok_or(TooBig)
    }
}

fn rewrite(
    t: &Term,
    origins: Vec<Origin>,
    ranges: &HashSet<IntRange>,
    capture_original: bool,
    simp: &mut Simp<'_>,
    work: &mut Pay<'_>,
) -> R<Traced> {
    let mut trace = Trace::new(t, origins, ranges, capture_original, work)?;
    let output = simp.go_observed(t, Some(&mut trace), work)?;
    let traced = trace.finish()?;
    if !equal(work, &output, &traced.term)? {
        return Err(TooBig);
    }
    Ok(traced)
}
fn part<P: Copy>(f: Formula<P>, index: usize, term: Term, work: &mut Pay<'_>) -> R<Formula<P>> {
    let mut origins = Vec::new();
    for mut origin in f.origins {
        pay(
            work,
            origin
                .path
                .len()
                .saturating_add(origins.capacity())
                .saturating_add(2),
        )?;
        if origin.path.first() == Some(&index) {
            origin.path.remove(0);
            let reached = at(&term, &origin.path, work)?;
            if !equal(work, reached, &origin.image)? {
                return Err(TooBig);
            }
            origins.push(origin);
        }
    }
    Ok(Formula {
        term,
        tag: f.tag,
        origins,
    })
}
fn split_traced<P: Copy>(
    f: Formula<P>,
    ranges: &HashSet<IntRange>,
    work: &mut Pay<'_>,
    out: &mut Vec<Formula<P>>,
) -> R<()> {
    pay(work, 1)?;
    match &f.term {
        Term::Bool(true) => Ok(()),
        Term::And(children) => {
            // The original is borrowed only to pre-admit and then own each
            // selected child. No origin is shared between sibling formulas.
            pay(work, children.len().saturating_add(1))?;
            for (index, child) in children.iter().enumerate() {
                let child = owned(work, child)?;
                let copy = Formula {
                    term: owned(work, &f.term)?,
                    tag: f.tag,
                    origins: cloned_origins(&f.origins, work)?,
                };
                split_traced(part(copy, index, child, work)?, ranges, work, out)?;
            }
            Ok(())
        }
        Term::Not(inner) if matches!(&**inner, Term::Or(_) | Term::Implies(..)) => {
            let inner_copy = owned(work, inner)?;
            let inner_f = part(f, 0, inner_copy, work)?;
            let count = arity(&inner_f.term);
            for index in 0..count {
                let child = owned(work, child(&inner_f.term, index).ok_or(TooBig)?)?;
                let copy = Formula {
                    term: owned(work, &inner_f.term)?,
                    tag: inner_f.tag,
                    origins: cloned_origins(&inner_f.origins, work)?,
                };
                let mut selected = part(copy, index, child, work)?;
                let negate = matches!(&inner_f.term, Term::Or(_)) || index == 1;
                if negate {
                    for origin in &mut selected.origins {
                        pay(work, origin.path.len().saturating_add(2))?;
                        origin.path.insert(0, 0);
                    }
                    pay(work, 1)?;
                    selected.term = Term::Not(Box::new(selected.term));
                    let traced = rewrite(
                        &selected.term,
                        selected.origins,
                        ranges,
                        false,
                        &mut Simp::local(),
                        work,
                    )?;
                    selected = Formula {
                        term: traced.term,
                        tag: selected.tag,
                        origins: traced.origins,
                    };
                }
                split_traced(selected, ranges, work, out)?;
            }
            Ok(())
        }
        _ => {
            pay(work, out.capacity().saturating_add(1))?;
            out.push(f);
            Ok(())
        }
    }
}

/// The same local rewrite, splitting, forward/backward fact windows and
/// eight-pass stopping rule as propagate; receipts travel only with their
/// actual current formula through every one of these operations.
pub(super) fn prepare<'t>(
    inputs: impl Iterator<Item = (usize, &'t Term)>,
    ranges: &HashSet<IntRange>,
    work: &mut Pay<'_>,
) -> R<Option<Vec<Formula<usize>>>> {
    let mut formulas = Vec::new();
    for (tag, input) in inputs {
        pay(work, 1)?;
        let t = rewrite(input, Vec::new(), ranges, true, &mut Simp::local(), work)?;
        split_traced(
            Formula {
                term: t.term,
                tag,
                origins: t.origins,
            },
            ranges,
            work,
            &mut formulas,
        )?;
    }
    for _ in 0..8 {
        let mut changed = false;
        for backward in [false, true] {
            let mut graph = EGraph::default();
            pay(work, formulas.len().saturating_add(1))?;
            let order: Vec<usize> = if backward {
                (0..formulas.len()).rev().collect()
            } else {
                (0..formulas.len()).collect()
            };
            for index in order {
                pay(work, 1)?;
                let origins = std::mem::take(&mut formulas[index].origins);
                let t = rewrite(
                    &formulas[index].term,
                    origins,
                    ranges,
                    false,
                    &mut Simp::with(&mut graph),
                    work,
                )?;
                if !equal(work, &t.term, &formulas[index].term)? {
                    changed = true
                }
                formulas[index].term = t.term;
                formulas[index].origins = t.origins;
                // Pre-admit extra graph registration in this new tracked lane.
                term(work, &formulas[index].term)?;
                graph.assert(&formulas[index].term);
                if graph.inconsistent {
                    return Ok(None);
                }
            }
        }
        let mut again = Vec::new();
        for f in formulas {
            split_traced(f, ranges, work, &mut again)?
        }
        formulas = again;
        if !changed {
            break;
        }
    }
    Ok(Some(formulas))
}

/// Called INSIDE one actual fallback occurrence, before its local Conds is
/// merged into parents. Parent rel/ite/one_of/filter supplies that origin's
/// own conditions, never a same-valued bare occurrence's OR-merged facts.
pub(super) fn mint(sites: &Sites, image: &Term, out: &mut Conds, work: &mut Pay<'_>) -> R<()> {
    pay(work, sites.0.len().saturating_add(1))?;
    for (address, origin) in &sites.0 {
        pay(work, 1)?;
        if *address != image as *const Term as usize {
            continue;
        }
        if !matches!(origin.state, State::Active)
            || !equal(work, image, &origin.image)?
            || !fallback(image, origin.range, work)?
        {
            return Err(TooBig);
        }
        if super::super::spec::clip_fallback(&origin.source, origin.range, &mut |n| work(n))
            .is_none()
        {
            return Err(TooBig);
        }
        let original_operand = child(&origin.source, 1).ok_or(TooBig)?;
        let current_operand = child(image, 0).ok_or(TooBig)?;
        if !equal(work, original_operand, &origin.source_operand)?
            || !equal(work, current_operand, &origin.operand_image)?
        {
            return Err(TooBig);
        }
        // Reserve worst-case local hashes/Eq probes, vector growth and all
        // owned payload copies BEFORE Conds::get/add can perform them.
        pay(
            work,
            out.index
                .capacity()
                .saturating_add(out.items.capacity())
                .saturating_add(8),
        )?;
        for _ in 0..out.items.len().saturating_mul(3).saturating_add(8) {
            term(work, image)?;
            term(work, &origin.source)?;
        }
        for item in &out.items {
            term(work, &item.call)?;
            term(work, &item.cond)?;
            pay(work, item.carriers.len().saturating_add(1))?;
            for carrier in &item.carriers {
                term(work, carrier)?
            }
        }
        let Some(item) = out.get(image) else { continue };
        let Term::Ite(condition, _, _, Sort::Int) = &origin.source else {
            return Err(TooBig);
        };
        // Raw conjunction retains both premises without an extra uncharged
        // flatten/dedup pass. It is an ordinary well-sorted query term.
        pay(work, 3)?;
        let gate = Term::And(vec![
            owned(work, &item.cond)?,
            owned(work, condition)?.not(),
        ]);
        let carrier = owned(work, image)?;
        let candidate = owned(work, &origin.source)?;
        // Duplicate original candidates may be conservatively omitted; never
        // borrow a premerged condition from another local source occurrence.
        if out.index.contains_key(&candidate) {
            continue;
        }
        // Existing keys were admitted above before reserve can rehash them.
        out.index.reserve(1);
        out.items.reserve(1);
        out.add(candidate, &[carrier], gate);
    }
    Ok(())
}

#[cfg(test)]
mod tests;
