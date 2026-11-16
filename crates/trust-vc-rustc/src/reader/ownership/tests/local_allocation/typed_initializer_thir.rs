// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Preserve the registered initializer's exact type, wrappers and root.
use super::*;
use rustc_errors::ErrorGuaranteed;
use rustc_middle::thir::{self, ExprId, Thir};
use rustc_middle::ty::{self, Ty};

fn seed<'tcx>(
    tcx: TyCtxt<'tcx>,
    thir: &Thir<'tcx>,
    registration: hooks::Seed,
) -> Result<ExprId, ErrorGuaranteed> {
    let mut initializers = thir.stmts.iter().filter_map(|statement| {
        let thir::StmtKind::Let {
            hir_id,
            pattern,
            initializer: Some(initializer),
            ..
        } = &statement.kind
        else {
            return None;
        };
        let thir::PatKind::Binding { var, ty, .. } = &pattern.kind else {
            return None;
        };
        (*hir_id == registration.local && var.0 == registration.binding).then_some((
            *initializer,
            *ty,
            pattern.ty,
        ))
    });
    let Some((initializer, binding_type, pattern_type)) = initializers.next() else {
        return Err(hooks::refuse(
            tcx,
            registration.owner,
            "typed-initializer-missing-seed",
        ));
    };
    if initializers.next().is_some() {
        return Err(hooks::refuse(
            tcx,
            registration.owner,
            "typed-initializer-duplicate-seed",
        ));
    }
    let typeck = tcx.typeck(registration.owner);
    let hir::Node::Expr(hir_initializer) = tcx.hir_node(registration.initializer) else {
        panic!("published initializer");
    };
    if !typeck.expr_adjustments(hir_initializer).is_empty() {
        return Err(hooks::refuse(
            tcx,
            registration.owner,
            "typed-initializer-coercion",
        ));
    }
    let expected = typeck.node_type(registration.binding);
    let mut current = initializer;
    let mut seen_hir = false;
    let mut visited = std::collections::HashSet::new();
    loop {
        if !visited.insert(current) {
            return Err(hooks::refuse(
                tcx,
                registration.owner,
                "typed-initializer-scope-cycle",
            ));
        }
        if thir[current].ty != expected
            || binding_type != expected
            || pattern_type != expected
            || typeck.expr_ty(hir_initializer) != expected
        {
            return Err(hooks::refuse(
                tcx,
                registration.owner,
                "typed-initializer-seed-type",
            ));
        }
        match thir[current].kind {
            thir::ExprKind::Scope { hir_id, value, .. } => {
                seen_hir |= hir_id == registration.initializer;
                current = value;
            }
            _ => break,
        }
    }
    if !seen_hir {
        return Err(hooks::refuse(
            tcx,
            registration.owner,
            "typed-initializer-scope",
        ));
    }
    Ok(current)
}

fn function_type<'tcx>(tcx: TyCtxt<'tcx>, helper: DefId, result: Ty<'tcx>) -> Ty<'tcx> {
    let generics = tcx.generics_of(helper);
    assert!(generics.parent.is_none() && generics.own_params.len() == 1);
    assert!(matches!(
        generics.own_params[0].kind,
        ty::GenericParamDefKind::Type { .. }
    ));
    let argument: ty::GenericArg<'tcx> = result.into();
    Ty::new_fn_def(tcx, helper, ty::Binder::dummy([argument]))
}

pub(super) fn replace<'tcx>(
    tcx: TyCtxt<'tcx>,
    thir: &mut Thir<'tcx>,
    root: ExprId,
    registration: hooks::Seed,
    case: Case,
) -> Result<(), ErrorGuaranteed> {
    let inner = seed(tcx, thir, registration)?;
    let before = thir[inner].clone();
    let root_metadata = (thir[root].ty, thir[root].span, thir[root].temp_scope_id);
    let argument = if case == Case::WrongType {
        tcx.types.unit
    } else {
        before.ty
    };
    let function = function_type(tcx, registration.helper, argument);
    let signature = function
        .fn_sig(tcx)
        .no_bound_vars()
        .expect("the ordinary helper has no bound signature variables");
    if !signature.inputs().is_empty()
        || signature.output() != before.ty
        || !signature.is_fn_trait_compatible()
    {
        return Err(hooks::refuse(
            tcx,
            registration.owner,
            "typed-initializer-result-type",
        ));
    }
    let fun = thir.exprs.push(thir::Expr {
        kind: thir::ExprKind::ZstLiteral { user_ty: None },
        ty: function,
        temp_scope_id: before.temp_scope_id,
        span: before.span,
    });
    thir.exprs[inner].kind = thir::ExprKind::Call {
        ty: function,
        fun,
        args: Box::new([]),
        from_hir_call: false,
        fn_span: before.span,
    };
    assert_eq!(
        (thir[inner].ty, thir[inner].span, thir[inner].temp_scope_id),
        (before.ty, before.span, before.temp_scope_id)
    );
    assert_eq!(
        (thir[root].ty, thir[root].span, thir[root].temp_scope_id),
        root_metadata
    );
    Ok(())
}

pub(super) fn inspect_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    helper: DefId,
    thir: &Thir<'tcx>,
    root: ExprId,
) {
    let body = tcx.hir_body_owned_by(owner);
    assert_eq!(thir[root].ty, tcx.types.unit);
    assert!(
        matches!(thir[root].kind, thir::ExprKind::Scope { hir_id, .. } if hir_id == body.value.hir_id)
    );
    let calls = thir
        .exprs
        .iter()
        .filter_map(|expression| {
            let thir::ExprKind::Call {
                ty: function,
                args,
                fun,
                ..
            } = &expression.kind
            else {
                return None;
            };
            let ty::FnDef(definition, parameters) = function.kind() else {
                return None;
            };
            (*definition == helper).then_some((expression, parameters, args, *fun))
        })
        .collect::<Vec<_>>();
    assert_eq!(calls.len(), 1);
    let (call, parameters, args, fun) = calls[0];
    let parameters = parameters.no_bound_vars().unwrap();
    assert_eq!(parameters.len(), 1);
    assert_eq!(parameters[0].as_type(), Some(call.ty));
    assert!(args.is_empty());
    assert!(matches!(
        thir[fun].kind,
        thir::ExprKind::ZstLiteral { user_ty: None }
    ));
}
