//! Executable instance contract correspondence only. Never a checked Spec
//! origin, UF alias, definition equation, body proof or native-owner token.

use super::*;
use crate::{AdtDecl, AdtId, LocalKind};

fn take(work: &mut usize, amount: usize) -> bool {
    match work.checked_sub(amount) {
        Some(left) => {
            *work = left;
            true
        }
        None => {
            *work = 0;
            false
        }
    }
}

// Preprice the clone/equality in the existing attrs matcher. Pure expression
// recursion is capped before invoking clone; unsupported proof blocks fail
// closed here rather than acquiring an unmetered recursive walk.
fn matcher_work(decl: &FnDecl, budget: &mut usize) -> bool {
    let mut pending = Vec::new();
    if let Some(groups) = &decl.attrs.broadcast_triggers {
        if !take(budget, groups.len()) {
            return false;
        }
        for group in groups {
            if !take(budget, group.len()) {
                return false;
            }
            pending.extend(group.iter().map(|expr| (expr, 0usize)));
        }
    }
    for clause in decl
        .requires
        .iter()
        .chain(&decl.ensures)
        .chain(&decl.recommends)
    {
        if !take(budget, 1) {
            return false;
        }
        pending.push((&clause.expr, 0));
    }
    for expr in decl
        .decreases
        .iter()
        .chain(&decl.decreases_when)
        .chain(decl.unwind_spec().condition())
    {
        if !take(budget, 1) {
            return false;
        }
        pending.push((expr, 0));
    }
    if let Body::Spec(expr) | Body::Constant(expr) = &decl.body {
        if !take(budget, 1) {
            return false;
        }
        pending.push((expr, 0));
    }
    while let Some((expr, depth)) = pending.pop() {
        if depth >= 64 || !take(budget, 1) || !type_work(&expr.ty, budget, 0) {
            return false;
        }
        if matches!(
            expr.kind,
            ExprKind::ProofInSpec(_) | ExprKind::ProofInSpecTail { .. }
        ) {
            return false;
        }
        match &expr.kind {
            ExprKind::Read(place) | ExprKind::Old(place) => {
                if !take(budget, place.projections.len()) {
                    return false;
                }
            }
            ExprKind::Call { type_args, .. } => {
                for ty in type_args {
                    if !type_work(ty, budget, 0) {
                        return false;
                    }
                }
            }
            ExprKind::Quant { vars, .. }
            | ExprKind::Choose { vars, .. }
            | ExprKind::UntriggeredQuant { vars, .. }
            | ExprKind::UntriggeredChoose { vars, .. } => {
                for (_, ty) in vars {
                    if !type_work(ty, budget, 0) {
                        return false;
                    }
                }
            }
            _ => {}
        }
        if crate::static_values::child_work(
            expr,
            |n| if take(budget, n) { Ok(()) } else { Err(()) },
        )
        .is_err()
        {
            return false;
        }
        expr.for_each_child(&mut |child| pending.push((child, depth + 1)));
    }
    for clause in decl
        .requires
        .iter()
        .chain(&decl.ensures)
        .chain(&decl.recommends)
    {
        for text in clause
            .attrs
            .proof_notes
            .iter()
            .chain(&clause.attrs.custom_errs)
        {
            if !take(budget, 1) || !take(budget, text.len()) {
                return false;
            }
        }
    }
    true
}

fn checked(
    functions: &Functions<'_>,
    adts: &HashMap<AdtId, &AdtDecl>,
    instance: &FnDecl,
    budget: &mut usize,
) -> bool {
    if !take(budget, 1) {
        return false;
    }
    let Some(origin) = &instance.attrs.instance else {
        return false;
    };
    let Some(original) = functions.get(&origin.declaration).copied() else {
        return false;
    };
    if instance.role != FnRole::Instance
        || matches!(original.role, FnRole::Instance | FnRole::Imported)
        || original.attrs.instance.is_some()
        || !matches!(original.mode, Mode::Exec | Mode::Proof)
        || instance.mode != original.mode
        || instance.kind != original.kind
        || original.kind == crate::FnKind::Static
        || !instance.type_params.is_empty()
        || origin.type_args.len() != original.type_params.len()
        || origin.type_args.len() > 64
        || !matches!(instance.body, Body::None | Body::Stmts(_))
        || !(matches!(original.body, Body::Stmts(_))
            || original.body == Body::None && original.attrs.external_body)
    {
        return false;
    }
    for ty in &origin.type_args {
        // Bound depth before has_param's recursive walk. No substitution copy.
        if !type_work(ty, budget, 0)
            || ty.has_param()
            || crate::copy_context::wellformed_with(adts, &|_| None, ty, 0, |n| {
                if take(budget, n) {
                    Ok(())
                } else {
                    Err(())
                }
            }) != Ok(true)
        {
            return false;
        }
    }
    if !matcher_work(original, budget)
        || !matcher_work(instance, budget)
        || instance.attrs.without_instance() != original.attrs
        || original.params.len() != instance.params.len()
        || !take(
            budget,
            original.params.len().saturating_add(1).saturating_mul(2),
        )
    {
        return false;
    }
    // Contract reads map actual ordered parameter slots and the result, not
    // whole local tables or source names. Enforce an injective result binding.
    let mut left = original.params.clone();
    left.push(original.ret);
    let mut right = instance.params.clone();
    right.push(instance.ret);
    let mut seen_left = HashSet::new();
    let mut seen_right = HashSet::new();
    for (formal, actual) in left.iter().zip(&right) {
        if !take(budget, 1) || !seen_left.insert(*formal) || !seen_right.insert(*actual) {
            return false;
        }
    }
    let matcher = Matcher {
        functions,
        definitions: None,
        arguments: &origin.type_args,
        checked_initializer: false,
        depth: Cell::new(0),
        parameters: Some((&left, &right)),
    };
    for (index, (formal, actual)) in left.iter().zip(&right).enumerate() {
        let (Some(formal), Some(actual)) = (original.local(*formal), instance.local(*actual))
        else {
            return false;
        };
        let kind = if index == original.params.len() {
            LocalKind::Return
        } else {
            LocalKind::Param
        };
        if formal.kind != kind
            || actual.kind != kind
            || formal.mode != actual.mode
            || formal.mutable != actual.mutable
            || formal.prophecy != actual.prophecy
            || !matcher.ty(&formal.ty, &actual.ty, budget)
        {
            return false;
        }
    }
    if original.copy_premises.len() != instance.copy_premises.len() {
        return false;
    }
    for (formal, actual) in original.copy_premises.iter().zip(&instance.copy_premises) {
        if !matcher.ty(formal, actual, budget)
            || crate::copy_context::is_copy_with(adts, &[], formal, Some(&origin.type_args), |n| {
                if take(budget, n) {
                    Ok(())
                } else {
                    Err(())
                }
            }) != Ok(true)
        {
            return false;
        }
    }
    let mut dependencies = HashSet::new();
    for (formal, actual) in [
        (&original.requires, &instance.requires),
        (&original.ensures, &instance.ensures),
        (&original.recommends, &instance.recommends),
    ] {
        if !matcher.clauses(formal, actual, budget, &mut dependencies) {
            return false;
        }
    }
    if !matcher.exprs(
        &original.decreases,
        &instance.decreases,
        budget,
        &mut dependencies,
    ) || original.decreases_by != instance.decreases_by
        || !matcher.unwind(
            &original.unwind,
            &instance.unwind,
            budget,
            &mut dependencies,
        )
    {
        return false;
    }
    match (&original.decreases_when, &instance.decreases_when) {
        (None, None) => {}
        (Some(a), Some(b)) if matcher.expr(a, b, budget, &mut dependencies) => {}
        _ => return false,
    }
    // Use the same core Spec-body matcher for every canonicalized contract
    // dependency, with this actual remaining allowance. No fresh MATCH_WORK.
    let mut pending = dependencies.into_iter().collect::<Vec<_>>();
    let mut seen = HashSet::new();
    while let Some(id) = pending.pop() {
        if !take(budget, 1) {
            return false;
        }
        if !seen.insert(id) {
            continue;
        }
        let Some(decl) = functions.get(&id).copied() else {
            return false;
        };
        if !matcher_work(decl, budget) {
            return false;
        }
        let Some(origin) = &decl.attrs.instance else {
            return false;
        };
        for ty in &origin.type_args {
            if !type_work(ty, budget, 0) {
                return false;
            }
        }
        let Some(next) = candidate_budgeted(functions, decl, budget) else {
            return false;
        };
        if !take(budget, next.len()) {
            return false;
        }
        pending.extend(next);
    }
    true
}

pub(crate) fn matches(
    functions: &Functions<'_>,
    adts: &HashMap<AdtId, &AdtDecl>,
    instance: &FnDecl,
    work: &Cell<usize>,
) -> bool {
    let mut remaining = work.get();
    let okay = checked(functions, adts, instance, &mut remaining);
    // Every failure keeps work spent; neither fallback nor another read gets
    // the original grant again.
    work.set(remaining);
    okay
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{DefHash, FnAttrs, FnKind, LocalDecl, LocalId, SpanId};

    fn base(id: u64, mode: Mode, ret: Ty) -> FnDecl {
        FnDecl {
            id: FnId(DefHash::new(0, id)),
            name: "contract".into(),
            span: SpanId(0),
            mode,
            role: FnRole::Item,
            kind: FnKind::Function,
            type_params: vec!["T".into()],
            copy_premises: vec![],
            locals: vec![LocalDecl {
                name: "ret".into(),
                ty: ret,
                mode,
                prophecy: Default::default(),
                mutable: false,
                kind: LocalKind::Return,
                span: SpanId(0),
            }],
            params: vec![],
            ret: LocalId(0),
            requires: vec![],
            ensures: vec![],
            recommends: vec![],
            decreases: vec![],
            decreases_when: None,
            decreases_by: None,
            unwind: None,
            attrs: FnAttrs::default(),
            body: Body::None,
        }
    }

    #[test]
    fn contract_and_spec_dependency_matching_share_the_original_allowance() {
        let mut spec = base(7, Mode::Spec, Ty::Bool);
        spec.attrs.inline = true;
        spec.body = Body::Spec(Expr::bool_lit(true, SpanId(0)));
        let mut spec_instance = spec.clone();
        spec_instance.id = FnId(DefHash::new(0, 6));
        spec_instance.role = FnRole::Instance;
        spec_instance.type_params.clear();
        spec_instance.attrs.instance = Some(crate::GenericInstance {
            declaration: spec.id,
            type_args: vec![Ty::uint(8)],
        });
        let mut original = base(4, Mode::Exec, Ty::uint(8));
        original.attrs.external_body = true;
        original.copy_premises = vec![Ty::Param(0)];
        original.ensures.push(Clause {
            expr: Expr::new(
                Ty::Bool,
                SpanId(0),
                ExprKind::Call {
                    callee: spec.id,
                    type_args: vec![Ty::Param(0)],
                    args: vec![],
                },
            ),
            span: SpanId(0),
            attrs: Default::default(),
        });
        let mut instance = original.clone();
        instance.id = FnId(DefHash::new(0, 5));
        instance.role = FnRole::Instance;
        instance.type_params.clear();
        instance.copy_premises = vec![Ty::uint(8)];
        instance.attrs.instance = Some(crate::GenericInstance {
            declaration: original.id,
            type_args: vec![Ty::uint(8)],
        });
        instance.ensures[0].expr = Expr::new(
            Ty::Bool,
            SpanId(0),
            ExprKind::Call {
                callee: spec_instance.id,
                type_args: vec![],
                args: vec![],
            },
        );
        let functions = [&original, &instance, &spec, &spec_instance]
            .into_iter()
            .map(|decl| (decl.id, decl))
            .collect();
        let adts = HashMap::new();
        let measure = Cell::new(100_000);
        assert!(matches(&functions, &adts, &instance, &measure));
        let spent = 100_000 - measure.get();
        assert!(spent > 1);
        // Successful Exec correspondence never joins Spec's UF/body set.
        assert!(!validated_origins(&functions).contains(&instance.id));
        let zero = Cell::new(0);
        assert!(!matches(&functions, &adts, &instance, &zero));
        assert_eq!(zero.get(), 0);
        let exact = Cell::new(spent);
        assert!(matches(&functions, &adts, &instance, &exact));
        assert_eq!(exact.get(), 0);
        assert!(!matches(&functions, &adts, &instance, &exact));
        assert_eq!(exact.get(), 0);
        let short = Cell::new(spent - 1);
        assert!(!matches(&functions, &adts, &instance, &short));
        let remaining = short.get();
        assert!(remaining < spent - 1);
        assert!(!matches(&functions, &adts, &instance, &short));
        assert!(short.get() <= remaining);
    }
}
