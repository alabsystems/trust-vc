//! Finite stable storage that cannot supply an owned abstract/reference ABI.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
use crate::{AdtDecl, AdtId, AdtKind, Ty};
use std::collections::{HashMap, HashSet};

pub(crate) fn storage_type_budgeted(
    ty: &Ty,
    adts: &HashMap<AdtId, &AdtDecl>,
    work: &std::cell::Cell<usize>,
) -> bool {
    // Charge the substituted result before cloning it. A field type may repeat
    // a large actual argument; bounding source nodes alone would miss that.
    fn substitution(ty: &Ty, args: &[Ty], remaining: &mut usize, depth: usize) -> bool {
        if depth > 64 {
            return false;
        }
        let Some(next) = remaining.checked_sub(1) else {
            return false;
        };
        *remaining = next;
        match ty {
            Ty::Param(index) => args
                .get(*index as usize)
                .is_some_and(|arg| substitution(arg, &[], remaining, depth + 1)),
            Ty::Tuple(parts) | Ty::Adt(_, parts) | Ty::Projection(_, parts) => parts
                .iter()
                .all(|part| substitution(part, args, remaining, depth + 1)),
            Ty::Ref { inner, .. } | Ty::MutRef(inner) => {
                substitution(inner, args, remaining, depth + 1)
            }
            _ => true,
        }
    }
    fn check(
        ty: &Ty,
        adts: &HashMap<AdtId, &AdtDecl>,
        active: &mut HashSet<AdtId>,
        remaining: &mut usize,
        depth: usize,
    ) -> bool {
        if depth > 64 {
            return false;
        }
        let Some(next) = remaining.checked_sub(1) else {
            return false;
        };
        *remaining = next;
        match ty {
            Ty::Bool | Ty::Int(_) | Ty::Unit => true,
            Ty::Tuple(fields) => fields
                .iter()
                .all(|field| check(field, adts, active, remaining, depth + 1)),
            Ty::Ref {
                mutable: false,
                inner,
            } => check(inner, adts, active, remaining, depth + 1),
            Ty::Adt(id, args) => {
                let Some(decl) = adts.get(id) else {
                    return false;
                };
                if decl.kind == AdtKind::Opaque
                    || decl.type_params.len() != args.len()
                    || !active.insert(*id)
                {
                    return false;
                }
                let result = args
                    .iter()
                    .all(|arg| check(arg, adts, active, remaining, depth + 1))
                    && decl.variants.iter().all(|variant| {
                        variant.fields.iter().all(|field| {
                            substitution(&field.ty, args, remaining, depth + 1)
                                && check(&field.ty.subst(args), adts, active, remaining, depth + 1)
                        })
                    });
                active.remove(id);
                result
            }
            // Shared global storage is not a source of owned generic values,
            // mutable reference identities, or opaque representation facts.
            Ty::Param(_) | Ty::Projection(..) | Ty::MutRef(_) | Ty::Ref { mutable: true, .. } => false,
        }
    }
    let original = work.get();
    let admitted = original.min(100_000);
    let mut remaining = admitted;
    let result = check(ty, adts, &mut HashSet::new(), &mut remaining, 0);
    work.set(original - (admitted - remaining));
    result
}

pub(crate) mod dependencies;

/// Prepay direct-child iteration before for_each_child can visit an arbitrarily
/// large vector. A failed callback must not keep scanning unpaid siblings.
pub(crate) fn child_work<E>(
    expr: &crate::Expr,
    mut charge: impl FnMut(usize) -> Result<(), E>,
) -> Result<(), E> {
    use crate::ExprKind as K;
    match &expr.kind {
        K::Lit(_) | K::IntegerConstant(_) | K::Read(_) | K::Old(_) | K::ProofInSpec(_) => {}
        K::Unary { .. }
        | K::Cast { .. }
        | K::Field { .. }
        | K::IsVariant { .. }
        | K::TupleField { .. }
        | K::Borrow(_)
        | K::MutRefCurrent(_)
        | K::MutRefFuture(_)
        | K::HasResolved(_)
        | K::ProofInSpecTail { .. } => charge(1)?,
        K::Binary { .. } | K::Let { .. } | K::MutRefUpdate { .. } => charge(2)?,
        K::If { .. } => charge(3)?,
        K::Call { args, .. } | K::Ctor { fields: args, .. } | K::Tuple(args) => charge(args.len())?,
        K::Quant { triggers, .. } | K::Choose { triggers, .. } => {
            charge(triggers.len())?;
            for group in triggers {
                charge(group.len())?;
            }
            charge(if matches!(expr.kind, K::Quant { .. }) {
                1
            } else {
                2
            })?;
        }
        K::UntriggeredQuant {
            trigger_candidates, ..
        } => {
            charge(trigger_candidates.len())?;
            charge(1)?;
        }
        K::UntriggeredChoose {
            trigger_candidates, ..
        } => {
            charge(trigger_candidates.len())?;
            charge(2)?;
        }
    }
    Ok(())
}

/// Occurrence-aware eligibility using the original WF/read allowance. No
/// eager whole-source scan and no fresh per-call grant.
pub(crate) fn dependency_problem(
    source: &crate::VcCrate,
    functions: &HashMap<crate::FnId, &crate::FnDecl>,
    adts: &HashMap<AdtId, &AdtDecl>,
    root: crate::FnId,
    work: &std::cell::Cell<usize>,
) -> Result<(), &'static str> {
    dependencies::check(source, functions, adts, root, work)
}
