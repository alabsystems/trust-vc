//! Expanded substitution paid by the actual query/analysis caller.
//!
//! Arguments are borrowed and substituted once. There is no independent work
//! grant and no output, partial fact or term clone on a failed preflight.

use super::term::{CmpOp, Sort, Term};
use std::collections::HashMap;

fn charge(work: &mut usize, amount: usize) -> Option<()> {
    match work.checked_sub(amount) {
        Some(left) => { *work = left; Some(()) }
        None => { *work = 0; None }
    }
}

pub(super) fn bindings<'a>(
    parameters: &'a [(String, Sort)],
    arguments: &'a [Term],
    work: &mut usize,
) -> Option<HashMap<&'a str, &'a Term>> {
    if parameters.len() != arguments.len()
        || parameters.iter().zip(arguments).any(|((_, sort), value)| *sort != value.sort())
    { return None; }
    charge(work, parameters.len())?;
    Some(parameters.iter().map(|(name, _)| name.as_str()).zip(arguments).collect())
}

/// Price the entire expanded result before allocating it. Variables inside
/// an actual argument retain their caller scope and are never substituted.
pub(super) fn price(
    source: &Term,
    bindings: &HashMap<&str, &Term>,
    work: &mut usize,
) -> Option<()> {
    charge(work, 1)?;
    let mut pending = vec![(source, true, 0usize)];
    while let Some((node, substitute, depth)) = pending.pop() {
        if depth >= 256 { *work = 0; return None; }
        let name_bytes = match node {
            Term::Var { name, .. } | Term::Call { name, .. } => name.len(),
            _ => 0,
        };
        charge(work, name_bytes.checked_add(1)?)?;
        if substitute {
            if let Term::Var { name, .. } = node {
                if let Some(argument) = bindings.get(name.as_str()) {
                    charge(work, 1)?;
                    pending.push((argument, false, depth));
                    continue;
                }
            }
        }
        let next = depth + 1;
        match node {
            Term::Not(inner) | Term::Neg(inner) => {
                charge(work, 1)?; pending.push((inner, substitute, next));
            }
            Term::And(children) | Term::Or(children) | Term::Call { args: children, .. } => {
                charge(work, children.len())?;
                pending.extend(children.iter().map(|child| (child, substitute, next)));
            }
            Term::Implies(a, b) | Term::Cmp(_, a, b) | Term::Arith(_, a, b) => {
                charge(work, 2)?;
                pending.push((a, substitute, next)); pending.push((b, substitute, next));
            }
            Term::Ite(a, b, c, _) => {
                charge(work, 3)?;
                pending.push((a, substitute, next)); pending.push((b, substitute, next));
                pending.push((c, substitute, next));
            }
            Term::Bool(_) | Term::Int(_) | Term::Var { .. } => {}
        }
    }
    Some(())
}

pub(super) fn apply(source: &Term, bindings: &HashMap<&str, &Term>, work: &mut usize) -> Option<Term> {
    price(source, bindings, work)?;
    fn rebuild(source: &Term, bindings: &HashMap<&str, &Term>) -> Term {
        match source {
            Term::Var { name, .. } => bindings.get(name.as_str())
                .map_or_else(|| source.clone(), |argument| (*argument).clone()),
            Term::Bool(_) | Term::Int(_) => source.clone(),
            Term::Not(inner) => !rebuild(inner, bindings),
            Term::Neg(inner) => -rebuild(inner, bindings),
            Term::And(children) => Term::and(children.iter().map(|child| rebuild(child, bindings))),
            Term::Or(children) => Term::or(children.iter().map(|child| rebuild(child, bindings))),
            Term::Implies(a, b) => Term::implies(rebuild(a, bindings), rebuild(b, bindings)),
            Term::Cmp(op, a, b) => match op {
                CmpOp::Eq => Term::eq(rebuild(a, bindings), rebuild(b, bindings)),
                CmpOp::Lt => Term::lt(rebuild(a, bindings), rebuild(b, bindings)),
                CmpOp::Le => Term::le(rebuild(a, bindings), rebuild(b, bindings)),
            },
            Term::Arith(op, a, b) => Term::arith(*op, rebuild(a, bindings), rebuild(b, bindings)),
            Term::Ite(a, b, c, _) => Term::ite(rebuild(a, bindings), rebuild(b, bindings), rebuild(c, bindings)),
            Term::Call { name, args, sort } => Term::Call {
                name: name.clone(), args: args.iter().map(|arg| rebuild(arg, bindings)).collect(), sort: *sort,
            },
        }
    }
    Some(rebuild(source, bindings))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn substitution_preserves_caller_variables_and_prices_every_repetition() {
        let source = Term::call("pair", vec![Term::var("a", Sort::TypeId); 4], Sort::TypeId);
        let actual = Term::call("type", vec![Term::var("a", Sort::TypeId)], Sort::TypeId);
        let map = HashMap::from([("a", &actual)]);
        let mut work = 10_000;
        let result = apply(&source, &map, &mut work).unwrap();
        assert_eq!(result, Term::call("pair", vec![actual.clone(); 4], Sort::TypeId));
        let cost = 10_000 - work;
        let mut one_short = cost - 1;
        assert!(apply(&source, &map, &mut one_short).is_none());
        assert_eq!(one_short, 0);
        assert!(apply(&source, &map, &mut one_short).is_none());
    }

    #[test]
    fn borrowed_bindings_check_sorts_and_share_one_original_allowance() {
        let parameters = vec![("a".into(), Sort::TypeId)];
        let arguments = vec![Term::var("caller", Sort::TypeId)];
        let mut work = 2;
        let map = bindings(&parameters, &arguments, &mut work).unwrap();
        assert_eq!(work, 1);
        assert!(apply(&Term::var("a", Sort::TypeId), &map, &mut work).is_none());
        assert_eq!(work, 0);
        assert!(bindings(&parameters, &[Term::Bool(true)], &mut work).is_none());
    }
}
