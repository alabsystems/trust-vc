// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Expanded AST IDs become HIR locals only through the canonical lowerer.
use super::rustc_data_structures::steal::Steal;
use super::*;
use rustc_hir::def::Res;
use rustc_middle::middle::resolve::{PartialRes, ResolverAstLowering, ResolverGlobalCtxt};
use rustc_middle::util::Providers;
use rustc_session::Session;
use rustc_span::{Ident, Symbol};

pub(super) const SHADOW: &str = "__trust_vc_allocated_shadow";
pub(super) type ResolverProvider = for<'tcx> fn(
    TyCtxt<'tcx>,
    (),
) -> (
    &'tcx Steal<ResolverAstLowering<'tcx>>,
    &'tcx Steal<ast::Crate>,
    &'tcx ResolverGlobalCtxt,
);

pub(super) fn install(session: &Session, providers: &mut Providers) {
    if session.trust_verification_enabled()
        || session.trust_ir_lower_enabled()
        || session.opts.unstable_opts.trust_targo_test_monitor
        || session.opts.unstable_opts.trust_certified_test_monitors
    {
        session
            .dcx()
            .fatal("local allocation controls require unverified compiler semantics");
    }
    session.with_trust_compiler_state::<Transaction, _>(|state| {
        assert!(state.plan.is_some());
        assert!(state
            .original
            .replace(providers.queries.resolver_for_lowering_raw)
            .is_none());
        state.installs += 1;
    });
    providers.queries.resolver_for_lowering_raw = expanded;
}

fn expanded<'tcx>(
    tcx: TyCtxt<'tcx>,
    (): (),
) -> (
    &'tcx Steal<ResolverAstLowering<'tcx>>,
    &'tcx Steal<ast::Crate>,
    &'tcx ResolverGlobalCtxt,
) {
    let (original, plan) = tcx
        .sess
        .with_trust_compiler_state::<Transaction, _>(|state| {
            (state.original.unwrap(), state.plan.unwrap())
        });
    // No compiler query runs under the Session-state lock.
    let (resolver, krate, global) = original(tcx, ());
    let mut resolver = resolver.steal();
    let mut krate = krate.steal();
    let mut targets = krate
        .items
        .iter_mut()
        .filter_map(|item| match &mut item.kind {
            ast::ItemKind::Fn(function) if function.ident.name.as_str() == "target" => {
                Some((item.id, function.as_mut()))
            }
            _ => None,
        });
    let (owner_id, function) = targets
        .next()
        .expect("the canonical provider must expand the target macro");
    assert!(targets.next().is_none());
    assert!(function.ident.span.from_expansion());
    assert_eq!(function.sig.decl.inputs.len(), 1);
    let original_pattern = &function.sig.decl.inputs[0].pat;
    let ast::PatKind::Ident(_, original_name, None) = original_pattern.kind else {
        panic!("only one plain original parameter is represented");
    };
    assert_eq!(original_name.name.as_str(), "original");
    assert_eq!(
        resolver.partial_res_map[&original_pattern.id].full_res(),
        Some(Res::Local(original_pattern.id))
    );
    let owner = resolver
        .owners
        .get(&owner_id)
        .expect("the actual existing function owner must be published")
        .def_id;
    let span = original_pattern.span;
    let body = function
        .body
        .as_mut()
        .expect("the expanded target must have a body");
    let initial_next = resolver.next_node_id;
    let mut allocated = Vec::new();
    let statement = fresh(&mut resolver, &mut allocated);
    let local = fresh(&mut resolver, &mut allocated);
    let pattern = fresh(&mut resolver, &mut allocated);
    assert!(resolver
        .partial_res_map
        .insert(pattern, PartialRes::new(Res::Local(pattern)))
        .is_none());
    let seed = path(
        &mut resolver,
        &mut allocated,
        original_name,
        original_pattern.id,
    );
    let initializer = match plan {
        Plan::Move => seed,
        Plan::BorrowEarly | Plan::BorrowLate => Box::new(ast::Expr {
            id: fresh(&mut resolver, &mut allocated),
            span,
            attrs: Default::default(),
            tokens: None,
            kind: ast::ExprKind::AddrOf(ast::BorrowKind::Ref, ast::Mutability::Mut, seed),
        }),
    };
    let binding = Box::new(ast::Pat {
        id: pattern,
        span,
        kind: ast::PatKind::Ident(
            ast::BindingMode::MUT,
            Ident::new(Symbol::intern(SHADOW), span),
            None,
        ),
    });
    let declaration = ast::Stmt {
        id: statement,
        span,
        kind: ast::StmtKind::Let(Box::new(ast::Local {
            id: local,
            super_: None,
            pat: binding,
            ty: None,
            kind: ast::LocalKind::Init(initializer),
            span,
            colon_sp: None,
            attrs: Default::default(),
            tokens: None,
        })),
    };
    let insertion = if plan == Plan::BorrowLate {
        body.stmts.len()
    } else {
        0
    };
    body.stmts.insert(insertion, declaration);
    let use_id = fresh(&mut resolver, &mut allocated);
    let use_value = path(
        &mut resolver,
        &mut allocated,
        Ident::new(Symbol::intern(SHADOW), span),
        pattern,
    );
    let use_value = match plan {
        Plan::Move => use_value,
        Plan::BorrowEarly | Plan::BorrowLate => Box::new(ast::Expr {
            id: fresh(&mut resolver, &mut allocated),
            span,
            attrs: Default::default(),
            tokens: None,
            kind: ast::ExprKind::Unary(ast::UnOp::Deref, use_value),
        }),
    };
    body.stmts.push(ast::Stmt {
        id: use_id,
        span,
        kind: ast::StmtKind::Semi(use_value),
    });
    let final_next = resolver.next_node_id;
    tcx.sess
        .with_trust_compiler_state::<Transaction, _>(|state| {
            state.expansions += 1;
            assert!(state.target.replace(owner).is_none());
            assert!(state.allocated.is_empty());
            state.allocated = allocated;
            state.initial_next = Some(initial_next);
            state.final_next = Some(final_next);
        });
    (
        tcx.arena.alloc(Steal::new(resolver)),
        tcx.arena.alloc(Steal::new(krate)),
        global,
    )
}

fn fresh(resolver: &mut ResolverAstLowering<'_>, allocated: &mut Vec<ast::NodeId>) -> ast::NodeId {
    let id = resolver.next_node_id;
    let next = id
        .as_u32()
        .checked_add(1)
        .expect("compiler AST ID space exhausted");
    assert!(next < ast::DUMMY_NODE_ID.as_u32());
    assert!(!resolver.partial_res_map.contains_key(&id) && !resolver.owners.contains_key(&id));
    assert!(!allocated.contains(&id));
    resolver.next_node_id = ast::NodeId::from_u32(next);
    allocated.push(id);
    id
}

fn path(
    resolver: &mut ResolverAstLowering<'_>,
    allocated: &mut Vec<ast::NodeId>,
    ident: Ident,
    binding: ast::NodeId,
) -> Box<ast::Expr> {
    let expression = fresh(resolver, allocated);
    let segment = fresh(resolver, allocated);
    for id in [expression, segment] {
        assert!(resolver
            .partial_res_map
            .insert(id, PartialRes::new(Res::Local(binding)))
            .is_none());
    }
    Box::new(ast::Expr {
        id: expression,
        span: ident.span,
        attrs: Default::default(),
        tokens: None,
        kind: ast::ExprKind::Path(
            None,
            ast::Path {
                span: ident.span,
                segments: vec![ast::PathSegment {
                    ident,
                    id: segment,
                    args: None,
                }]
                .into(),
            },
        ),
    })
}
