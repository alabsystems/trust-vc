// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A fresh Session owns a one-root typed THIR transaction.
use super::*;
use crate::reader::ownership::local_allocation::rustc_data_structures::steal::Steal;
use rustc_errors::ErrorGuaranteed;
use rustc_middle::thir::{ExprId, Thir};
use rustc_middle::util::Providers;
use rustc_session::Session;

type ThirProvider = for<'tcx> fn(
    TyCtxt<'tcx>,
    LocalDefId,
) -> Result<(&'tcx Steal<Thir<'tcx>>, ExprId), ErrorGuaranteed>;

#[derive(Clone, Copy)]
pub(super) struct Seed {
    pub owner: LocalDefId,
    pub body: hir::HirId,
    pub local: hir::HirId,
    pub binding: hir::HirId,
    pub initializer: hir::HirId,
    pub helper: DefId,
}

#[derive(Default)]
pub(super) struct State {
    pub case: Option<Case>,
    original: Option<ThirProvider>,
    seed: Option<Seed>,
    installs: usize,
    requests: usize,
    transforms: usize,
    refused: bool,
}

pub(super) fn install(session: &Session, providers: &mut Providers) {
    provider::install(session, providers);
    session.with_trust_compiler_state::<State, _>(|state| {
        assert!(state.case.is_some());
        assert!(state
            .original
            .replace(providers.queries.thir_body)
            .is_none());
        state.installs += 1;
    });
    providers.queries.thir_body = typed_body;
}

pub(super) fn arm(tcx: TyCtxt<'_>, owner: LocalDefId, helper: DefId, case: Case) {
    let body = tcx.hir_body_owned_by(owner);
    let hir::ExprKind::Block(block, None) = body.value.kind else {
        panic!("target block");
    };
    let local = block
        .stmts
        .iter()
        .find_map(|statement| {
            let hir::StmtKind::Let(local) = statement.kind else {
                return None;
            };
            let hir::PatKind::Binding(_, _, ident, None) = local.pat.kind else {
                return None;
            };
            (ident.name.as_str() == provider::SHADOW).then_some(local)
        })
        .unwrap();
    let hir::PatKind::Binding(_, mut binding, _, None) = local.pat.kind else {
        panic!("real shadow binding");
    };
    if case == Case::MissingSeed {
        // A genuine published parameter has the wrong role: it cannot match
        // the registered local's actual THIR Let binding.
        let hir::PatKind::Binding(_, original, _, None) = body.params[0].pat.kind else {
            panic!("parameter");
        };
        binding = original;
    }
    let seed = Seed {
        owner,
        body: body.value.hir_id,
        local: local.hir_id,
        binding,
        initializer: local.init.unwrap().hir_id,
        helper,
    };
    tcx.sess.with_trust_compiler_state::<State, _>(|state| {
        assert!(!state.refused && state.requests == 0 && state.seed.replace(seed).is_none());
    });
}

fn typed_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
) -> Result<(&'tcx Steal<Thir<'tcx>>, ExprId), ErrorGuaranteed> {
    let target = tcx
        .sess
        .with_trust_compiler_state::<Transaction, _>(|state| state.target);
    let (original, seed, case) = tcx.sess.with_trust_compiler_state::<State, _>(|state| {
        if target == Some(owner) {
            state.requests += 1;
        }
        (state.original.unwrap(), state.seed, state.case.unwrap())
    });
    if target != Some(owner) {
        return original(tcx, owner);
    }
    let Some(seed) = seed else {
        return Err(refuse(tcx, owner, "typed-initializer-unarmed"));
    };
    if seed.owner != owner || tcx.hir_body_owned_by(owner).value.hir_id != seed.body {
        return Err(refuse(tcx, owner, "typed-initializer-owner"));
    }
    let (canonical, root) = original(tcx, owner)?;
    if canonical.is_stolen() {
        return Err(refuse(tcx, owner, "typed-initializer-stolen"));
    }
    let mut cloned = canonical.borrow().clone();
    transform::replace(tcx, &mut cloned, root, seed, case)?;
    tcx.sess
        .with_trust_compiler_state::<State, _>(|state| state.transforms += 1);
    Ok((tcx.alloc_steal_thir(cloned), root))
}

pub(super) fn refuse(tcx: TyCtxt<'_>, owner: LocalDefId, tag: &'static str) -> ErrorGuaranteed {
    tcx.sess
        .with_trust_compiler_state::<State, _>(|state| state.refused = true);
    tcx.dcx().span_err(tcx.def_span(owner), tag)
}

pub(super) fn check(tcx: TyCtxt<'_>, case: Case) {
    tcx.sess.with_trust_compiler_state::<State, _>(|state| {
        assert_eq!((state.installs, state.requests), (1, 1));
        assert_eq!(state.transforms, usize::from(case.refusal().is_none()));
        assert_eq!(state.refused, case.refusal().is_some());
    });
}
