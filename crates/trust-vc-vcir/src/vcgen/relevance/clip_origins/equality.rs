//! Borrowed structural equality, charged for the fields actually compared.
//!
//! A different constructor can reject a candidate without walking either
//! subtree. Receipt identity still includes every field of `Term`'s Eq.
use super::*;

fn text(work: &mut Pay<'_>, a: &str, b: &str) -> R<bool> {
    pay(work, 2)?;
    if a.len() != b.len() {
        return Ok(false);
    }
    pay(work, a.len().saturating_mul(2))?;
    Ok(a == b)
}

fn push<'t>(
    work: &mut Pay<'_>,
    pending: &mut Vec<(&'t Term, &'t Term)>,
    pair: (&'t Term, &'t Term),
) -> R<()> {
    // Pay for both storing this pair and eventually popping it. Pay before
    // allocation for the new slots and moving the existing borrowed pairs.
    pay(work, 2)?;
    if pending.len() == pending.capacity() {
        let capacity = pending.capacity().saturating_mul(2).max(4);
        pay(work, pending.len().saturating_add(capacity))?;
        pending.reserve_exact(capacity.saturating_sub(pending.len()));
    }
    pending.push(pair);
    Ok(())
}

fn children<'t>(
    work: &mut Pay<'_>,
    pending: &mut Vec<(&'t Term, &'t Term)>,
    a: &'t [Term],
    b: &'t [Term],
) -> R<bool> {
    pay(work, 2)?;
    if a.len() != b.len() {
        return Ok(false);
    }
    // Reverse insertion preserves the source order when the pairs are popped.
    for pair in a.iter().zip(b).rev() {
        pay(work, 1)?;
        push(work, pending, pair)?;
    }
    Ok(true)
}

pub(super) fn equal(work: &mut Pay<'_>, a: &Term, b: &Term) -> R<bool> {
    let mut pending = Vec::new();
    let mut pair = (a, b);
    loop {
        // Constructor inspection and every scalar field comparison are paid
        // before reading them. A refused payment never becomes inequality.
        pay(work, 2)?;
        let (a, b) = pair;
        let same = match a {
            Term::Bool(a) => match b {
                Term::Bool(b) => {
                    pay(work, 2)?;
                    a == b
                }
                _ => false,
            },
            Term::Int(a) => match b {
                Term::Int(b) => {
                    pay(work, 2)?;
                    a == b
                }
                _ => false,
            },
            Term::Var { name: a, sort: sa } => match b {
                Term::Var { name: b, sort: sb } => {
                    if !text(work, a, b)? {
                        return Ok(false);
                    }
                    pay(work, 2)?;
                    sa == sb
                }
                _ => false,
            },
            Term::Not(a) => match b {
                Term::Not(b) => {
                    push(work, &mut pending, (a, b))?;
                    true
                }
                _ => false,
            },
            Term::And(a) => match b {
                Term::And(b) => children(work, &mut pending, a, b)?,
                _ => false,
            },
            Term::Or(a) => match b {
                Term::Or(b) => children(work, &mut pending, a, b)?,
                _ => false,
            },
            Term::Implies(a0, a1) => match b {
                Term::Implies(b0, b1) => {
                    push(work, &mut pending, (a1, b1))?;
                    push(work, &mut pending, (a0, b0))?;
                    true
                }
                _ => false,
            },
            Term::Cmp(oa, a0, a1) => match b {
                Term::Cmp(ob, b0, b1) => {
                    pay(work, 2)?;
                    if oa != ob {
                        return Ok(false);
                    }
                    push(work, &mut pending, (a1, b1))?;
                    push(work, &mut pending, (a0, b0))?;
                    true
                }
                _ => false,
            },
            Term::Arith(oa, a0, a1) => match b {
                Term::Arith(ob, b0, b1) => {
                    pay(work, 2)?;
                    if oa != ob {
                        return Ok(false);
                    }
                    push(work, &mut pending, (a1, b1))?;
                    push(work, &mut pending, (a0, b0))?;
                    true
                }
                _ => false,
            },
            Term::Neg(a) => match b {
                Term::Neg(b) => {
                    push(work, &mut pending, (a, b))?;
                    true
                }
                _ => false,
            },
            Term::Ite(a0, a1, a2, sa) => match b {
                Term::Ite(b0, b1, b2, sb) => {
                    pay(work, 2)?;
                    if sa != sb {
                        return Ok(false);
                    }
                    push(work, &mut pending, (a2, b2))?;
                    push(work, &mut pending, (a1, b1))?;
                    push(work, &mut pending, (a0, b0))?;
                    true
                }
                _ => false,
            },
            Term::Call {
                name: a,
                args: aa,
                sort: sa,
            } => match b {
                Term::Call {
                    name: b,
                    args: ab,
                    sort: sb,
                } => {
                    if !text(work, a, b)? {
                        return Ok(false);
                    }
                    pay(work, 2)?;
                    sa == sb && children(work, &mut pending, aa, ab)?
                }
                _ => false,
            },
        };
        if !same {
            return Ok(false);
        }
        match pending.pop() {
            Some(next) => pair = next,
            None => return Ok(true),
        }
    }
}

#[cfg(test)]
mod tests;
