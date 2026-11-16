// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Inspect only identities, types and scopes published by normal lowering.
use super::*;
use rustc_hir::{self as hir, def::Res};
use rustc_middle::ty;

pub(super) fn published_local(tcx: TyCtxt<'_>, plan: Plan) -> LocalDefId {
    let target = tcx
        .sess
        .with_trust_compiler_state::<Transaction, _>(|state| {
            assert_eq!((state.installs, state.expansions), (1, 1));
            assert_eq!(state.plan, Some(plan));
            let expected = if plan == Plan::Move { 8 } else { 10 };
            assert_eq!(state.allocated.len(), expected);
            let initial = state.initial_next.unwrap().as_u32();
            let final_id = state.final_next.unwrap().as_u32();
            assert_eq!(final_id - initial, expected as u32);
            for (index, id) in state.allocated.iter().enumerate() {
                assert_eq!(id.as_u32(), initial + index as u32);
                assert_ne!(*id, ast::DUMMY_NODE_ID);
            }
            state.target.unwrap()
        });
    assert_eq!(tcx.item_name(target.to_def_id()).as_str(), "target");
    assert!(tcx.def_span(target).from_expansion());
    let body = tcx.hir_body_owned_by(target);
    assert_eq!(body.value.hir_id.owner.def_id, target);
    let hir::PatKind::Binding(_, original, name, None) = body.params[0].pat.kind else {
        panic!("the actual original parameter must be a plain binding");
    };
    assert_eq!(name.name.as_str(), "original");
    let hir::ExprKind::Block(block, None) = body.value.kind else {
        panic!("the actual function must lower to a block");
    };
    let mut shadows = block.stmts.iter().filter_map(|statement| {
        let hir::StmtKind::Let(local) = statement.kind else {
            return None;
        };
        let hir::PatKind::Binding(_, binding, ident, None) = local.pat.kind else {
            return None;
        };
        (ident.name.as_str() == provider::SHADOW).then_some((local, binding))
    });
    let (shadow, binding) = shadows
        .next()
        .expect("the compiler must publish the injected local");
    assert!(shadows.next().is_none());
    assert_ne!(binding, original);
    assert_eq!(binding.owner.def_id, target);
    assert_eq!(shadow.pat.hir_id, binding);
    assert_eq!(tcx.hir_name(binding).as_str(), provider::SHADOW);
    assert!(
        matches!(tcx.hir_node(binding), hir::Node::Pat(pattern) if std::ptr::eq(pattern, shadow.pat))
    );
    let scopes = tcx.region_scope_tree(target);
    let scope = scopes
        .var_scope(binding.local_id)
        .expect("a real local needs a registered lexical scope");
    assert_eq!(scope.hir_id(scopes).unwrap().owner.def_id, target);
    let typeck = tcx.typeck(target);
    let original_type = typeck.pat_ty(body.params[0].pat);
    let shadow_type = typeck.pat_ty(shadow.pat);
    let initializer = shadow
        .init
        .expect("the real synthetic local must have an initializer");
    assert_eq!(typeck.expr_ty(initializer), shadow_type);
    let seed = match plan {
        Plan::Move => {
            assert!(
                matches!(original_type.kind(), ty::Param(_)),
                "{original_type:?}"
            );
            assert_eq!(shadow_type, original_type);
            initializer
        }
        Plan::BorrowEarly | Plan::BorrowLate => {
            assert_eq!(original_type, tcx.types.u64);
            assert!(
                matches!(shadow_type.kind(), ty::Ref(_, inner, rustc_ast::Mutability::Mut) if *inner == original_type)
            );
            let hir::ExprKind::AddrOf(_, rustc_ast::Mutability::Mut, seed) = initializer.kind
            else {
                panic!("the shadow must be a real mutable borrow, not a type rewrite");
            };
            seed
        }
    };
    let hir::ExprKind::Path(ref path) = seed.kind else {
        panic!("the seed must name the original binding");
    };
    assert_eq!(typeck.qpath_res(path, seed.hir_id), Res::Local(original));
    let hir::StmtKind::Semi(last) = block.stmts.last().unwrap().kind else {
        panic!("the real shadow use must survive lowering");
    };
    let last_path = match plan {
        Plan::Move => {
            assert_eq!(typeck.expr_ty(last), shadow_type);
            last
        }
        Plan::BorrowEarly | Plan::BorrowLate => {
            let hir::ExprKind::Unary(hir::UnOp::Deref, path) = last.kind else {
                panic!("the shadow borrow must have an actual later dereference");
            };
            assert_eq!(typeck.expr_ty(last), original_type);
            path
        }
    };
    let hir::ExprKind::Path(ref path) = last_path.kind else {
        panic!("the synthetic use must name its binding");
    };
    assert_eq!(
        typeck.qpath_res(path, last_path.hir_id),
        Res::Local(binding)
    );
    assert_eq!(typeck.expr_ty(last_path), shadow_type);
    target
}
