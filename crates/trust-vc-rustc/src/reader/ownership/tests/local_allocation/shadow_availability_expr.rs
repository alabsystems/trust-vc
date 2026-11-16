// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Ordinary typed calls preserve the real helper signatures and tie binder.
use super::*;
use rustc_middle::mir::{BorrowKind, MutBorrowKind};
use thir::{Expr, ExprId, ExprKind, Thir};

pub(super) fn push<'tcx>(
    body: &mut Thir<'tcx>,
    meta: &Expr<'tcx>,
    ty: ty::Ty<'tcx>,
    kind: ExprKind<'tcx>,
) -> ExprId {
    body.exprs.push(Expr {
        kind,
        ty,
        temp_scope_id: meta.temp_scope_id,
        span: meta.span,
    })
}
pub(super) fn tuple<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Thir<'tcx>,
    meta: &Expr<'tcx>,
    fields: Vec<ExprId>,
) -> ExprId {
    let types = fields
        .iter()
        .map(|field| body[*field].ty)
        .collect::<Vec<_>>();
    let ty = if fields.is_empty() {
        tcx.types.unit
    } else {
        ty::Ty::new_tup(tcx, &types)
    };
    push(
        body,
        meta,
        ty,
        ExprKind::Tuple {
            fields: fields.into_boxed_slice(),
        },
    )
}
pub(super) fn borrow<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Thir<'tcx>,
    meta: &Expr<'tcx>,
    place: ExprId,
    mutable: bool,
) -> ExprId {
    let inner = body[place].ty;
    let (ty, borrow_kind) = if mutable {
        (
            ty::Ty::new_mut_ref(tcx, tcx.lifetimes.re_erased, inner),
            BorrowKind::Mut {
                kind: MutBorrowKind::Default,
            },
        )
    } else {
        (
            ty::Ty::new_imm_ref(tcx, tcx.lifetimes.re_erased, inner),
            BorrowKind::Shared,
        )
    };
    push(
        body,
        meta,
        ty,
        ExprKind::Borrow {
            borrow_kind,
            arg: place,
        },
    )
}
pub(super) fn call_kind<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Thir<'tcx>,
    meta: &Expr<'tcx>,
    helper: DefId,
    types: [ty::Ty<'tcx>; 2],
    arguments: Vec<ExprId>,
    tie: bool,
) -> ExprKind<'tcx> {
    let generics = tcx.generics_of(helper);
    assert!(generics.parent.is_none() && generics.own_params.len() == 2);
    assert!(generics
        .own_params
        .iter()
        .all(|parameter| matches!(parameter.kind, ty::GenericParamDefKind::Type { .. })));
    let parameters: [ty::GenericArg<'tcx>; 2] = [types[0].into(), types[1].into()];
    let function = ty::Ty::new_fn_def(tcx, helper, ty::Binder::dummy(parameters));
    let signature = function.fn_sig(tcx);
    if tie {
        assert_eq!(signature.bound_vars().len(), 1);
        assert!(matches!(
            signature.bound_vars()[0],
            ty::BoundVariableKind::Region(_)
        ));
        let signature = signature.skip_binder();
        assert!(signature.is_fn_trait_compatible() && signature.inputs().len() == 2);
        let ty::Ref(first, first_ty, ast::Mutability::Mut) = signature.inputs()[0].kind() else {
            panic!("first tie reference");
        };
        let ty::Ref(second, second_ty, ast::Mutability::Mut) = signature.inputs()[1].kind() else {
            panic!("second tie reference");
        };
        let ty::Ref(output, output_ty, ast::Mutability::Mut) = signature.output().kind() else {
            panic!("tie output reference");
        };
        assert_eq!(
            (*first_ty, *second_ty, *output_ty),
            (types[0], types[1], types[0])
        );
        assert_eq!((first, second), (output, output));
        assert!(
            matches!(first.kind(),ty::RegionKind::ReBound(ty::BoundVarIndexKind::Bound(ty::INNERMOST),region) if region.var.as_u32()==0)
        );
        assert_eq!(arguments.len(), 2);
    } else {
        let signature = signature.no_bound_vars().unwrap();
        assert!(signature.is_fn_trait_compatible());
        assert_eq!(signature.inputs(), &[types[0]]);
        assert_eq!(signature.output(), types[1]);
        assert_eq!(arguments.len(), 1);
    }
    let fun = push(body, meta, function, ExprKind::ZstLiteral { user_ty: None });
    ExprKind::Call {
        ty: function,
        fun,
        args: arguments.into_boxed_slice(),
        from_hir_call: false,
        fn_span: meta.span,
    }
}
pub(super) fn erased<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Thir<'tcx>,
    meta: &Expr<'tcx>,
    helper: DefId,
    result: ty::Ty<'tcx>,
) -> ExprId {
    let unit = tuple(tcx, body, meta, Vec::new());
    let kind = call_kind(
        tcx,
        body,
        meta,
        helper,
        [tcx.types.unit, result],
        vec![unit],
        false,
    );
    push(body, meta, result, kind)
}
pub(super) fn pure_place(body: &Thir<'_>, place: ExprId) -> bool {
    match body[place].kind {
        ExprKind::Scope { value, .. } => pure_place(body, value),
        ExprKind::VarRef { .. } => true,
        ExprKind::Field { lhs, .. } => pure_place(body, lhs),
        ExprKind::Deref { arg } => {
            matches!(body[arg].ty.kind(), ty::Ref(..)) && pure_place(body, arg)
        }
        _ => false,
    }
}
pub(super) fn mirror<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    body: &mut Thir<'tcx>,
    place: ExprId,
    map: &HashMap<hir::HirId, hooks::Shadow>,
) -> ExprId {
    let meta = body[place].clone();
    let kind = match meta.kind.clone() {
        ExprKind::Scope {
            region_scope,
            hir_id,
            value,
        } => ExprKind::Scope {
            region_scope,
            hir_id,
            value: mirror(tcx, owner, body, value, map),
        },
        ExprKind::VarRef { id } => {
            let shadow = map
                .get(&id.0)
                .unwrap_or_else(|| tcx.dcx().fatal("a shadow place has no published binding"));
            assert_eq!(tcx.typeck(owner).node_type(shadow.binding), meta.ty);
            ExprKind::VarRef {
                id: thir::LocalVarId(shadow.binding),
            }
        }
        ExprKind::Deref { arg } => {
            if !matches!(body[arg].ty.kind(), ty::Ref(_, _, ast::Mutability::Mut)) {
                tcx.dcx()
                    .fatal("this shadow component does not mirror shared or raw dereferences");
            }
            ExprKind::Deref {
                arg: mirror(tcx, owner, body, arg, map),
            }
        }
        ExprKind::Field {
            lhs,
            variant_index,
            name,
        } => ExprKind::Field {
            lhs: mirror(tcx, owner, body, lhs, map),
            variant_index,
            name,
        },
        _ => tcx.dcx().fatal("unsupported shadow place projection"),
    };
    push(body, &meta, meta.ty, kind)
}
