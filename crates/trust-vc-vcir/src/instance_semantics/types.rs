// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Bounded instance type matching borrows the actual substituted type tree.
use super::*;

pub(super) fn type_work(ty: &Ty, budget: &mut usize, depth: u32) -> bool {
    if depth >= 64 {
        return false;
    }
    let Some(left) = budget.checked_sub(1) else {
        return false;
    };
    *budget = left;
    match ty {
        Ty::Ref { inner, .. } | Ty::MutRef(inner) => type_work(inner, budget, depth + 1),
        Ty::Adt(_, args) | Ty::Tuple(args) => {
            args.len() <= *budget && args.iter().all(|ty| type_work(ty, budget, depth + 1))
        }
        _ => true,
    }
}

pub(super) fn substituted(formal: &Ty, arguments: &[Ty], actual: &Ty) -> bool {
    match (formal, actual) {
        // Substitution is single-level: a caller's parameter is not another
        // index into this callee's argument list.
        (Ty::Param(index), _) => arguments.get(*index as usize) == Some(actual),
        (Ty::Tuple(a), Ty::Tuple(b)) => group(a, arguments, b),
        (Ty::Adt(a, x), Ty::Adt(b, y)) => a == b && group(x, arguments, y),
        (
            Ty::Ref {
                mutable: a,
                inner: x,
            },
            Ty::Ref {
                mutable: b,
                inner: y,
            },
        ) => a == b && substituted(x, arguments, y),
        (Ty::MutRef(a), Ty::MutRef(b)) => substituted(a, arguments, b),
        (Ty::Bool | Ty::Int(_) | Ty::Unit, _) => formal == actual,
        _ => false,
    }
}

fn group(formal: &[Ty], arguments: &[Ty], actual: &[Ty]) -> bool {
    formal.len() == actual.len()
        && formal
            .iter()
            .zip(actual)
            .all(|(a, b)| substituted(a, arguments, b))
}

pub(super) fn canonical_call<'a>(
    functions: &'a Functions<'_>,
    callee: FnId,
    arguments: &'a [Ty],
) -> Option<(FnId, &'a [Ty], Option<FnId>)> {
    let function = functions.get(&callee)?;
    let Some(origin) = &function.attrs.instance else {
        return Some((callee, arguments, None));
    };
    let original = functions.get(&origin.declaration)?;
    if function.role != FnRole::Instance
        || !arguments.is_empty()
        || original.role != FnRole::Item
        || original.attrs.instance.is_some()
        || original.attrs.is_trait_method_impl
    {
        return None;
    }
    Some((origin.declaration, &origin.type_args, Some(callee)))
}
