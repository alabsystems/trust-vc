// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! One unverified compiler transaction owns its published binding map.
use super::super::rustc_data_structures::steal::Steal;
use super::*;
use rustc_errors::ErrorGuaranteed;
use rustc_hir::intravisit::{self, Visitor};
use rustc_middle::util::Providers;
use rustc_session::Session;

type ThirProvider =
    for<'tcx> fn(
        TyCtxt<'tcx>,
        LocalDefId,
    ) -> Result<(&'tcx Steal<thir::Thir<'tcx>>, thir::ExprId), ErrorGuaranteed>;
#[derive(Clone, Copy)]
pub(super) struct Shadow {
    pub binding: hir::HirId,
    pub local: hir::HirId,
    pub initializer: hir::HirId,
}
#[derive(Default)]
pub(super) struct State {
    pub case: Option<Case>,
    pub raw: Option<provider::ResolverProvider>,
    thir: Option<ThirProvider>,
    pub owner: Option<LocalDefId>,
    pub shadow_names: Vec<Symbol>,
    pub expansions: usize,
    map: Option<HashMap<hir::HirId, Shadow>>,
    helpers: Option<Helpers>,
    counts: Counts,
    requests: usize,
}
pub(super) fn install(session: &Session, providers: &mut Providers) {
    if session.trust_verification_enabled()
        || session.trust_ir_lower_enabled()
        || session.opts.unstable_opts.trust_targo_test_monitor
        || session.opts.unstable_opts.trust_certified_test_monitors
    {
        session
            .dcx()
            .fatal("shadow component requires unverified compiler semantics");
    }
    session.with_trust_compiler_state::<State, _>(|state| {
        assert!(state.case.is_some() && state.raw.is_none() && state.thir.is_none());
        state.raw = Some(providers.queries.resolver_for_lowering_raw);
        state.thir = Some(providers.queries.thir_body);
    });
    providers.queries.resolver_for_lowering_raw = allocation::expanded;
    providers.queries.thir_body = body;
}
struct Published<'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    names: HashSet<Symbol>,
    map: HashMap<hir::HirId, Shadow>,
}
impl<'tcx> Visitor<'tcx> for Published<'tcx> {
    fn visit_local(&mut self, local: &'tcx hir::LetStmt<'tcx>) {
        if let hir::PatKind::Binding(_, binding, ident, None) = local.pat.kind {
            if self.names.remove(&ident.name) {
                let init = local.init.unwrap();
                let hir::ExprKind::Path(ref path) = init.kind else {
                    panic!("typed seed path");
                };
                let typeck = self.tcx.typeck(self.owner);
                let Res::Local(original) = typeck.qpath_res(path, init.hir_id) else {
                    panic!("actual original seed binding");
                };
                assert_ne!(original, binding);
                assert_eq!(binding.owner.def_id, self.owner);
                assert!(
                    matches!(self.tcx.hir_node(binding),hir::Node::Pat(pattern) if std::ptr::eq(pattern,local.pat))
                );
                assert_eq!(typeck.node_type(original), typeck.pat_ty(local.pat));
                assert_eq!(typeck.expr_ty(init), typeck.pat_ty(local.pat));
                assert!(self
                    .tcx
                    .region_scope_tree(self.owner)
                    .var_scope(binding.local_id)
                    .is_some());
                assert!(self
                    .map
                    .insert(
                        original,
                        Shadow {
                            binding,
                            local: local.hir_id,
                            initializer: init.hir_id
                        }
                    )
                    .is_none());
            }
        }
        intravisit::walk_local(self, local);
    }
}
struct Calls<'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    found: HashMap<String, DefId>,
}
impl<'tcx> Visitor<'tcx> for Calls<'tcx> {
    fn visit_expr(&mut self, expression: &'tcx hir::Expr<'tcx>) {
        if let hir::ExprKind::Call(function, _) = expression.kind {
            if let hir::ExprKind::Path(ref path) = function.kind {
                if let Res::Def(_, definition) =
                    self.tcx.typeck(self.owner).qpath_res(path, function.hir_id)
                {
                    if !definition.is_local()
                        && self.tcx.crate_name(definition.krate).as_str() == "allocation_helper"
                    {
                        self.found.insert(
                            self.tcx.item_name(definition).as_str().to_owned(),
                            definition,
                        );
                    }
                }
            }
        }
        intravisit::walk_expr(self, expression);
    }
}
pub(super) fn arm(tcx: TyCtxt<'_>) -> LocalDefId {
    let (owner, names) = tcx.sess.with_trust_compiler_state::<State, _>(|state| {
        assert_eq!(state.expansions, 1);
        (state.owner.unwrap(), state.shadow_names.clone())
    });
    let mut published = Published {
        tcx,
        owner,
        names: names.into_iter().collect(),
        map: HashMap::new(),
    };
    published.visit_body(tcx.hir_body_owned_by(owner));
    assert!(published.names.is_empty());
    let anchor = tcx
        .hir_body_owners()
        .find(|owner| {
            tcx.opt_item_name(owner.to_def_id())
                .is_some_and(|name| name.as_str() == "helper_anchor")
        })
        .unwrap();
    let mut calls = Calls {
        tcx,
        owner: anchor,
        found: HashMap::new(),
    };
    calls.visit_body(tcx.hir_body_owned_by(anchor));
    assert_eq!(calls.found.len(), 3);
    let helpers = Helpers {
        erased: calls.found["erased"],
        shadow: calls.found["shadow"],
        tie: calls.found["tie"],
    };
    assert!(tcx.dcx().has_errors().is_none());
    tcx.sess.with_trust_compiler_state::<State, _>(|state| {
        assert_eq!(state.requests, 0);
        state.map = Some(published.map);
        state.helpers = Some(helpers);
    });
    owner
}
fn body<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
) -> Result<(&'tcx Steal<thir::Thir<'tcx>>, thir::ExprId), ErrorGuaranteed> {
    let (original, target, case, map, helpers) =
        tcx.sess.with_trust_compiler_state::<State, _>(|state| {
            if state.owner == Some(owner) {
                state.requests += 1;
            }
            (
                state.thir.unwrap(),
                state.owner,
                state.case.unwrap(),
                state.map.clone(),
                state.helpers,
            )
        });
    if target != Some(owner) {
        return original(tcx, owner);
    }
    let Some(map) = map else {
        return Err(tcx.dcx().span_err(
            tcx.def_span(owner),
            "shadow transaction requested before ready",
        ));
    };
    let helpers = helpers.unwrap();
    let plan = modes::plan(tcx, owner, &map);
    let (canonical, root) = original(tcx, owner)?;
    if canonical.is_stolen() {
        return Err(tcx
            .dcx()
            .span_err(tcx.def_span(owner), "shadow canonical body already stolen"));
    }
    let (physical, mut cloned) = {
        let graph = canonical.borrow();
        (
            sites::capture(tcx, owner, &graph, &map, &plan),
            graph.clone(),
        )
    };
    let counts = transform::apply(
        tcx,
        owner,
        &mut cloned,
        root,
        &map,
        helpers,
        plan,
        physical,
        case,
    );
    tcx.sess
        .with_trust_compiler_state::<State, _>(|state| state.counts = counts);
    Ok((tcx.alloc_steal_thir(cloned), root))
}
pub(super) fn counts(tcx: TyCtxt<'_>) -> Counts {
    tcx.sess.with_trust_compiler_state::<State, _>(|state| {
        assert_eq!(state.requests, 1);
        assert_eq!(state.counts.seeds, state.map.as_ref().unwrap().len());
        state.counts
    })
}
pub(super) fn helpers(tcx: TyCtxt<'_>) -> Helpers {
    tcx.sess
        .with_trust_compiler_state::<State, _>(|state| state.helpers.unwrap())
}
