//! Original, typed Spec dependency inputs retained by the actual Keep owner.
//!
//! These inputs precede semantic lowering. They are not an imported function,
//! a definition equation, a mode/WF/termination result, or a proof receipt.
//! In particular, retaining an original recommends expression never assumes it.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{BTreeMap, BTreeSet, HashSet};

use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{DefId, LOCAL_CRATE, LocalDefId};
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{self as hir};
use rustc_middle::hir::nested_filter::OnlyBodies;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::{Span, Symbol};
use serde_json::{Value, json};
use trust_vc_vcir::Mode;

use super::*;
use crate::declaration_alignment::source_bindings::SourceIdentity;
use crate::declaration_alignment::{AuthoredSpan, DeclarationType, GenericScope, SourceAnchor};
use crate::reader::{attrs, declaration_modes};

mod correspondence;
mod definitions;
mod dispatch;
mod intrinsics;

pub(super) use correspondence::{Pairs, View, roundtrip};
pub(in crate::reader) use definitions::ClientDefinitions;
pub(in crate::reader) use definitions::{CheckedSourceFunction, OwnedSourceHeader};
pub(super) use definitions::capture_forwarding;
pub(super) use definitions::{
    OwnedDefinitions, OwnedSourceFamily, for_client as definitions_for_client,
};
pub(super) use intrinsics::Intrinsics;

pub(super) fn nominal_pairs(
    view: &alignment::View,
    candidates: &alignment::Candidates,
) -> BTreeMap<NativeKey, NativeKey> {
    let keys = view
        .declarations
        .iter()
        .filter_map(|declaration| {
            matches!(
                declaration.shape,
                Observation::Observed(alignment::DeclarationShape::Nominal { .. })
            )
            .then_some(declaration.key)
        })
        .collect::<BTreeSet<_>>();
    candidates
        .matches
        .iter()
        .filter(|candidate| keys.contains(&candidate.keep))
        .map(|candidate| (candidate.keep, candidate.erase))
        .collect()
}

const MAX_WORK: usize = 262_144;
const MAX_FUNCTIONS: usize = 1024;

pub(super) struct Work(usize);

impl Work {
    pub(super) fn new() -> Self {
        Self(MAX_WORK)
    }
    fn charge(&mut self, tcx: TyCtxt<'_>, count: usize) -> Result<(), String> {
        diagnostics(tcx)?;
        self.0 = self
            .0
            .checked_sub(count)
            .ok_or("Spec graph work bound exhausted")?;
        Ok(())
    }
}

/// Every native node remains borrowed from this one original Keep context.
/// A later semantic producer must consume these exact bodies, not reload a
/// body from metadata, replace it with a role flag, or deserialize this graph.
struct OriginalFunction<'tcx> {
    owner: LocalDefId,
    body: &'tcx hir::Body<'tcx>,
    signature: ty::PolyFnSig<'tcx>,
    attributes: &'tcx [rustc_attr_ir::Attribute],
    clauses: Vec<dispatch::ClauseInput<'tcx>>,
    bodies: Vec<&'tcx hir::Body<'tcx>>,
    calls: Vec<dispatch::Call<'tcx>>,
}

pub(super) struct LiveGraph<'scope, 'tcx> {
    tcx: TyCtxt<'tcx>,
    root: LocalDefId,
    scope: &'scope Intrinsics<'scope, 'tcx>,
    pairs: &'scope Pairs,
    nodes: BTreeMap<NativeKey, OriginalFunction<'tcx>>,
}

/// Cross-session dependency inputs only. No typed body is discarded and then
/// claimed usable: these inputs explicitly require fresh semantic lowering in
/// the original live graph before any value import can be constructed.
pub(super) struct OwnedInputs {
    root: NativeKey,
    nodes: BTreeSet<NativeKey>,
    pairs: BTreeMap<NativeKey, NativeKey>,
    source: SourceIdentity,
}

impl OwnedInputs {
    fn revalidate(&self, inputs: &Inputs, pairs: &Pairs) -> Result<(), String> {
        if self.source != inputs.sources.identity()
            || !self.nodes.contains(&self.root)
            || self
                .nodes
                .iter()
                .any(|key| self.pairs.get(key) != pairs.erase(*key))
        {
            return Err(
                "the retained Spec dependency inputs changed source or correspondence".into(),
            );
        }
        Ok(())
    }
}

pub(super) fn revalidate_all<'a>(
    inputs: &Inputs,
    pairs: &Pairs,
    graphs: impl IntoIterator<Item = &'a OwnedInputs>,
) -> Result<(), String> {
    inputs.revalidate()?;
    for graph in graphs {
        graph.revalidate(inputs, pairs)?;
    }
    Ok(())
}

impl<'scope, 'tcx> LiveGraph<'scope, 'tcx> {
    fn current(&self) -> Result<(), String> {
        self.scope.current(self.tcx)?;
        for (key, function) in &self.nodes {
            if declaration_native::key(self.tcx, function.owner.to_def_id()) != *key
                || !declaration_modes::original_body_available(self.tcx, function.owner)
                || self
                    .tcx
                    .hir_maybe_body_owned_by(function.owner)
                    .is_none_or(|body| !std::ptr::eq(body, function.body))
                || self.pairs.erase(*key).is_none()
                || !std::ptr::eq(
                    self.tcx
                        .hir_attrs(self.tcx.local_def_id_to_hir_id(function.owner)),
                    function.attributes,
                )
            {
                return Err("an original Spec graph body or counterpart changed".into());
            }
            for body in &function.bodies {
                original_body(self.tcx, body)?;
            }
        }
        Ok(())
    }

    pub(super) fn observation(&self) -> Result<Value, String> {
        self.current()?;
        Ok(json!({"state": "OriginalNativeSpecDependencyInputs",
            "root": key_json(declaration_native::key(self.tcx, self.root.to_def_id())),
            "functions": self.nodes.iter().map(|(key, node)| json!({
                "keep": key_json(*key), "erase": self.pairs.erase(*key).map(|key| key_json(*key)),
                "signature_binders": node.signature.bound_vars().len(),
                "native_generic_clauses": node.clauses.len(),
                "original_bodies_including_clauses": node.bodies.len(),
                "calls": node.calls.iter().map(|call| call.observation(self.tcx)).collect::<Vec<_>>()
            })).collect::<Vec<_>>(),
            "semantic_lowering": "required while these original bodies are live",
            "modes_wf_purity_termination": "required",
            "recommends_assumed": false, "when_used_as_spec_redirected": false,
            "body_import_authorized": false, "verified_functions": null}))
    }

    pub(super) fn into_inputs(self) -> Result<OwnedInputs, String> {
        self.current()?;
        Ok(OwnedInputs {
            root: declaration_native::key(self.tcx, self.root.to_def_id()),
            nodes: self.nodes.keys().copied().collect(),
            pairs: self
                .nodes
                .keys()
                .map(|key| {
                    self.pairs
                        .erase(*key)
                        .copied()
                        .map(|erase| (*key, erase))
                        .ok_or_else(|| "a Spec graph function lost its counterpart".to_string())
                })
                .collect::<Result<_, _>>()?,
            source: self.scope.inputs.sources.identity(),
        })
    }
}

fn key_json(key: NativeKey) -> Value {
    json!({"crate": key.stable_crate_id, "hash": key.def_path_hash.to_string()})
}

fn original_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &hir::Body<'tcx>,
) -> Result<&'tcx hir::Body<'tcx>, String> {
    let raw = tcx
        .lower_to_hir(body.value.hir_id.owner.def_id)
        .as_owner()
        .ok_or("a Spec graph body has no canonical lowering")?;
    let original = raw
        .nodes
        .bodies
        .get(&body.id().hir_id.local_id)
        .copied()
        .ok_or("a Spec graph body is absent from the canonical lowering")?;
    if !std::ptr::eq(original, body) {
        return Err("a Spec graph body differs from its canonical lowering".into());
    }
    if body.contract.is_some() {
        return Err("native first-class contract syntax needs a typed Spec graph producer".into());
    }
    Ok(original)
}

struct Walk<'a, 'scope, 'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    scope: &'a Intrinsics<'scope, 'tcx>,
    work: &'a mut Work,
    bodies: Vec<&'tcx hir::Body<'tcx>>,
    calls: Vec<dispatch::Call<'tcx>>,
    direct_callees: HashSet<hir::HirId>,
    error: Option<String>,
}

impl<'tcx> Visitor<'tcx> for Walk<'_, '_, 'tcx> {
    type NestedFilter = OnlyBodies;
    fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_nested_item(&mut self, _: hir::ItemId) {
        self.error
            .get_or_insert("a nested item needs its own Spec graph owner".into());
    }

    fn visit_body(&mut self, body: &hir::Body<'tcx>) {
        if self.error.is_some() {
            return;
        }
        let result = (|| {
            self.work.charge(self.tcx, 1)?;
            let original = original_body(self.tcx, body)?;
            let owner = self.tcx.hir_body_owner_def_id(body.id());
            if owner != self.owner && self.tcx.def_kind(owner) != DefKind::Closure {
                return Err("a nested nonclosure body is outside the Spec graph owner".into());
            }
            self.bodies.push(original);
            Ok(())
        })();
        if let Err(error) = result {
            self.error = Some(error);
            return;
        }
        // This includes recommends/ensures closure bodies in original order.
        // It does not classify a reference as a logical precondition.
        intravisit::walk_body(self, body);
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        if self.error.is_some() {
            return;
        }
        let result = (|| {
            self.work.charge(self.tcx, 1)?;
            let raw = self
                .tcx
                .lower_to_hir(expr.hir_id.owner.def_id)
                .as_owner()
                .ok_or("a Spec graph expression has no canonical original attributes")?;
            if !std::ptr::eq(
                raw.attrs.get(expr.hir_id.local_id),
                self.tcx.hir_attrs(expr.hir_id),
            ) {
                return Err("a Spec graph expression's attributes were projected".into());
            }
            match expr.kind {
                hir::ExprKind::Call(callee, _) => {
                    let hir::ExprKind::Path(ref path) = callee.kind else {
                        return Err(
                            "an indirect Spec graph call needs explicit value-call semantics"
                                .into(),
                        );
                    };
                    let typeck = self
                        .tcx
                        .typeck(self.tcx.typeck_root_def_id_local(expr.hir_id.owner.def_id));
                    self.direct_callees.insert(callee.hir_id);
                    match typeck.qpath_res(path, callee.hir_id) {
                        Res::Def(DefKind::Fn | DefKind::AssocFn, definition) => {
                            self.calls.push(dispatch::capture(
                                self.tcx,
                                self.owner,
                                expr.span,
                                definition,
                                typeck.node_args(callee.hir_id),
                                self.scope,
                            )?);
                        }
                        Res::Def(DefKind::Ctor(..), _) => {
                            return Err(
                                "Spec graph constructors require the transparent datatype closure"
                                    .into(),
                            );
                        }
                        _ => {
                            return Err(
                                "an unresolved Spec graph call is not omitted from the closure"
                                    .into(),
                            );
                        }
                    }
                }
                hir::ExprKind::MethodCall(..) => {
                    let typeck = self
                        .tcx
                        .typeck(self.tcx.typeck_root_def_id_local(expr.hir_id.owner.def_id));
                    let definition = typeck
                        .type_dependent_def_id(expr.hir_id)
                        .ok_or("a Spec graph method has no native resolved declaration")?;
                    self.calls.push(dispatch::capture(
                        self.tcx,
                        self.owner,
                        expr.span,
                        definition,
                        typeck.node_args(expr.hir_id),
                        self.scope,
                    )?);
                }
                // Taking a function value also creates a dependency. This
                // first slice refuses it instead of overlooking an edge.
                hir::ExprKind::Path(ref path) => {
                    let typeck = self
                        .tcx
                        .typeck(self.tcx.typeck_root_def_id_local(expr.hir_id.owner.def_id));
                    if matches!(
                        typeck.qpath_res(path, expr.hir_id),
                        Res::Def(DefKind::Fn | DefKind::AssocFn, _)
                    ) {
                        if !self.direct_callees.contains(&expr.hir_id) {
                            return Err(
                                "a Spec graph function value needs explicit value-call semantics"
                                    .into(),
                            );
                        }
                    }
                }
                _ => {}
            }
            let typeck = self
                .tcx
                .typeck(self.tcx.typeck_root_def_id_local(expr.hir_id.owner.def_id));
            if !matches!(
                expr.kind,
                hir::ExprKind::Call(..) | hir::ExprKind::MethodCall(..)
            ) {
                if let Some(definition) = typeck.type_dependent_def_id(expr.hir_id) {
                    self.calls.push(dispatch::capture(
                        self.tcx,
                        self.owner,
                        expr.span,
                        definition,
                        typeck.node_args(expr.hir_id),
                        self.scope,
                    )?);
                }
            }
            // Overloaded autoderef introduces a call outside the expression's
            // direct method/operator resolution. Keep it explicit until the
            // graph has a faithful adjustment-to-method edge representation.
            if typeck.expr_adjustments(expr).iter().any(|adjustment| {
                !matches!(
                    adjustment.kind,
                    ty::adjustment::Adjust::Deref(ty::adjustment::DerefAdjustKind::Builtin)
                        | ty::adjustment::Adjust::Borrow(_)
                        | ty::adjustment::Adjust::NeverToAny
                )
            }) {
                return Err(
                    "a Spec graph adjustment needs its actual implicit call/representation edges"
                        .into(),
                );
            }
            Ok(())
        })();
        if let Err(error) = result {
            self.error = Some(error);
            return;
        }
        intravisit::walk_expr(self, expr);
    }

    fn visit_pat(&mut self, pattern: &'tcx hir::Pat<'tcx>) {
        if !matches!(
            pattern.kind,
            hir::PatKind::Wild | hir::PatKind::Binding(_, _, _, None)
        ) {
            self.error.get_or_insert("a Spec graph destructuring pattern needs its typed representation/adjustment closure".into());
            return;
        }
        intravisit::walk_pat(self, pattern);
    }
}

/// Capture a complete function-call dependency closure from an actual root, including
/// selected trait declarations and implementation bodies. Missing foreign
/// bodies refuse the graph even if another reader calls their role `Item`.
pub(super) fn capture<'scope, 'tcx>(
    tcx: TyCtxt<'tcx>,
    root: LocalDefId,
    scope: &'scope Intrinsics<'scope, 'tcx>,
    pairs: &'scope Pairs,
    work: &mut Work,
) -> Result<LiveGraph<'scope, 'tcx>, String> {
    scope.current(tcx)?;
    let mut pending = vec![root];
    let mut nodes = BTreeMap::new();
    while let Some(owner) = pending.pop() {
        work.charge(tcx, 1)?;
        let key = declaration_native::key(tcx, owner.to_def_id());
        if nodes.contains_key(&key) {
            continue;
        }
        if nodes.len() >= MAX_FUNCTIONS {
            return Err("Spec graph function bound exhausted".into());
        }
        let attributes = attrs::item_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner)));
        if !attributes.verus_macro
            || attributes.mode != Some(Mode::Spec)
            || attributes.external
            || attributes.external_body
            || attributes.uninterp
            || crate::reader::is_external(tcx, owner)
            || !declaration_modes::original_body_available(tcx, owner)
            || pairs.erase(key).is_none()
        {
            return Err(
                "a Spec graph node lacks an original Spec body and checked counterpart".into(),
            );
        }
        let body = tcx
            .hir_maybe_body_owned_by(owner)
            .ok_or("a Spec graph node has no body")?;
        let raw = tcx
            .lower_to_hir(owner)
            .as_owner()
            .ok_or("a Spec graph function has no canonical attributes")?;
        let attributes = raw.attrs.get(tcx.local_def_id_to_hir_id(owner).local_id);
        if !std::ptr::eq(attributes, tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner))) {
            return Err("the Spec graph function's original attributes were projected".into());
        }
        let env = ty::TypingEnv::non_body_analysis(tcx, owner.to_def_id());
        let signature = tcx
            .try_normalize_erasing_regions(env, tcx.fn_sig(owner).instantiate_identity())
            .map_err(|_| "a Spec graph declaration signature cannot be normalized")?;
        let clauses = dispatch::clauses(
            tcx,
            owner.to_def_id(),
            ty::GenericArgs::identity_for_item(tcx, owner.to_def_id()),
            env,
        )?;
        let mut walk = Walk {
            tcx,
            owner,
            scope,
            work,
            bodies: Vec::new(),
            calls: Vec::new(),
            direct_callees: HashSet::new(),
            error: None,
        };
        walk.visit_body(body);
        if let Some(error) = walk.error {
            return Err(error);
        }
        for call in &walk.calls {
            if call.is_intrinsic() {
                continue;
            }
            let target = call.target().as_local().ok_or(
                "a selected foreign Spec body requires an exact owner-held definition graph",
            )?;
            pending.push(target);
            if let Some(declaration) = call.trait_declaration() {
                // A trait declaration's clauses and binders are retained by
                // the correspondence view. Defaults need a separate original
                // body node; this slice admits only explicit selected members.
                if pairs
                    .erase(declaration_native::key(tcx, declaration))
                    .is_none()
                {
                    return Err("a selected trait declaration lacks its checked counterpart".into());
                }
            }
        }
        nodes.insert(
            key,
            OriginalFunction {
                owner,
                body,
                signature,
                attributes,
                clauses,
                bodies: walk.bodies,
                calls: walk.calls,
            },
        );
    }
    let graph = LiveGraph {
        tcx,
        root,
        scope,
        pairs,
        nodes,
    };
    graph.current()?;
    Ok(graph)
}
