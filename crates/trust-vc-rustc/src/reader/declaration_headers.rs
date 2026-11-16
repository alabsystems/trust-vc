//! Native, owner-scoped observations of empty and nonempty headers.
//!
//! The sealed empty result records a completed original-body traversal. It
//! authenticates neither macro/source provenance nor an Erase correspondence;
//! the separate declaration producer must establish those before import.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use std::collections::{HashMap, HashSet};

use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{self as hir};
use rustc_middle::hir::nested_filter::OnlyBodies;
use rustc_middle::ty::TyCtxt;
use rustc_span::{ExpnId, Span};
use serde_json::{json, Value};

use super::attrs::{self, VerusAttr};
use super::declaration_facts::{definition, expansion_chain};
use super::declaration_modes::original_body_available;
use crate::verus_items::VerusItem;

/// Classification labels are observations, never receipt constructors.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum HeaderClass {
    Empty,
    Nonempty,
    Unknown,
}

/// Only `check` can create this value, after checking the original body and
/// traversing every closure body. Its native owner and body cannot be replaced
/// by a caller, deserialized, or recovered from a JSON classification label.
pub(super) struct EmptyHeader<'tcx> {
    owner: LocalDefId,
    body: &'tcx hir::Body<'tcx>,
}

/// A syntax fact about one original, leading recommendation call. The
/// authenticated producer must still bind its builtin, lower its expression,
/// check modes/types/WF and retain its source before importing any clause.
pub(super) struct RecommendationHeader<'tcx> {
    owner: LocalDefId,
    body: &'tcx hir::Body<'tcx>,
    builtin: DefId,
    argument: &'tcx hir::Expr<'tcx>,
}

impl<'tcx> RecommendationHeader<'tcx> {
    pub(super) fn argument(&self) -> &'tcx hir::Expr<'tcx> {
        self.argument
    }
}

enum Outcome<'tcx> {
    Empty(EmptyHeader<'tcx>),
    Nonempty,
    Unknown,
}

/// One native check in one compiler context, with sealed result fields.
pub(super) struct CheckedHeaders<'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    outcome: Outcome<'tcx>,
    walk: HeaderWalk<'tcx>,
    recommendation: Option<RecommendationHeader<'tcx>>,
}

impl<'tcx> CheckedHeaders<'tcx> {
    pub(super) fn classification(&self) -> HeaderClass {
        match &self.outcome {
            Outcome::Empty(_) => HeaderClass::Empty,
            Outcome::Nonempty => HeaderClass::Nonempty,
            Outcome::Unknown => HeaderClass::Unknown,
        }
    }

    /// A future authenticated producer must request this fact for the actual
    /// owner it is importing. Matching a JSON label, name, or LocalDefId from
    /// another compiler context cannot supply it.
    pub(super) fn empty_for(
        &self,
        tcx: TyCtxt<'tcx>,
        owner: LocalDefId,
    ) -> Option<&EmptyHeader<'tcx>> {
        let Outcome::Empty(empty) = &self.outcome else {
            return None;
        };
        if !std::ptr::eq(*self.tcx, *tcx)
            || empty.owner != owner
            || !original_body_available(tcx, owner)
            || original_attributes(tcx, owner).is_none()
        {
            return None;
        }
        tcx.hir_maybe_body_owned_by(owner)
            .is_some_and(|body| std::ptr::eq(body, empty.body))
            .then_some(empty)
    }

    /// The caller must supply the actual fresh, authenticated builtin DefId;
    /// a diagnostic spelling or observation cannot establish that selection.
    pub(super) fn recommends_for(
        &self,
        tcx: TyCtxt<'tcx>,
        owner: LocalDefId,
        authenticated_builtin: DefId,
    ) -> Option<&RecommendationHeader<'tcx>> {
        let fact = self.recommendation.as_ref()?;
        if !std::ptr::eq(*self.tcx, *tcx)
            || fact.owner != owner
            || fact.builtin != authenticated_builtin
            || !original_body_available(tcx, owner)
            || original_attributes(tcx, owner).is_none()
            || tcx
                .hir_maybe_body_owned_by(owner)
                .is_none_or(|body| !std::ptr::eq(body, fact.body))
        {
            return None;
        }
        Some(fact)
    }

    /// Diagnostic JSON only. Even an empty traversal retains Unknown header
    /// authority until the other producer inputs are authenticated.
    pub(super) fn observation(&self) -> Value {
        let mut unknowns = self.walk.unknowns.clone();
        let state = match self.classification() {
            HeaderClass::Empty if self.empty_for(self.tcx, self.owner).is_some() => {
                "ObservedNoHeaderReference"
            }
            HeaderClass::Nonempty => "ObservedHeaderReferences",
            HeaderClass::Empty => {
                unknowns.push("the original body identity changed after header traversal".into());
                "Unknown"
            }
            HeaderClass::Unknown => "Unknown",
        };
        let mut expansion_ids = self.walk.expansions.iter().copied().collect::<Vec<_>>();
        expansion_ids.sort_by_key(|id| format!("{id:?}"));
        let expansions = expansion_ids
            .into_iter()
            .map(|id| expansion_chain(self.tcx, id))
            .collect::<Vec<_>>();
        json!({
            "state": state,
            "owner": definition(self.tcx, self.owner.to_def_id()),
            "expressions_visited": self.walk.expressions,
            "bodies_visited": self.walk.bodies,
            "includes_closure_bodies": true,
            "references": self.walk.references.iter().map(|reference| json!({
                "kind": format!("{:?}", reference.item),
                "definition": definition(self.tcx, reference.definition),
                "span_debug": format!("{:?}", reference.span),
                "expression_owner": definition(self.tcx, reference.expression_owner.to_def_id()),
            })).collect::<Vec<_>>(),
            "unknowns": unknowns,
            "expression_expansion_graphs": expansions,
            "header_authority": {"state": "Unknown", "reason":
                "native header observations still require source/macro authentication, builtin artifact authentication, and Erase declaration alignment"},
            "ordered_header_validation": {"state": "Unknown", "reason":
                "nonempty, duplicate, malformed or misplaced headers require an ordered header producer"},
            "single_leading_recommends_observation": self.recommendation.as_ref()
                .and_then(|fact| self.recommends_for(self.tcx, self.owner, fact.builtin)).map(|fact|
                json!({"state": "ObservedSingleOriginalLeadingRecommends",
                    "builtin": definition(self.tcx, fact.builtin),
                    "argument_span_debug": format!("{:?}", fact.argument.span),
                    "expression_semantics_checked": false,
                    "permission_from_observation": false})),
        })
    }
}

struct HeaderReference {
    item: VerusItem,
    definition: DefId,
    span: Span,
    expression_owner: LocalDefId,
    expression: hir::HirId,
}

struct HeaderWalk<'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    items: HashMap<DefId, VerusItem>,
    references: Vec<HeaderReference>,
    unknowns: Vec<String>,
    expansions: HashSet<ExpnId>,
    expressions: usize,
    bodies: usize,
}

impl HeaderWalk<'_> {
    fn reference(&mut self, definition: DefId, expr: &hir::Expr<'_>) {
        if let Some(item) = self.items.get(&definition).copied() {
            if item == VerusItem::Other {
                self.unknowns.push(format!(
                    "an unclassified Verus builtin reference: {definition:?}"
                ));
            }
            if item.is_header() {
                self.references.push(HeaderReference {
                    item,
                    definition,
                    span: expr.span,
                    expression_owner: expr.hir_id.owner.def_id,
                    expression: expr.hir_id,
                });
            }
        }
    }
}

impl<'tcx> Visitor<'tcx> for HeaderWalk<'tcx> {
    type NestedFilter = OnlyBodies;

    fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_nested_item(&mut self, _id: hir::ItemId) {
        self.unknowns
            .push("a nested item requires a separate owner-scoped header classification".into());
    }

    fn visit_body(&mut self, body: &hir::Body<'tcx>) {
        let owner = self.tcx.hir_body_owner_def_id(body.id());
        if owner != self.owner && self.tcx.def_kind(owner) != DefKind::Closure {
            self.unknowns.push(
                "a nested non-closure body requires a separate owner-scoped header classification"
                    .into(),
            );
            return;
        }
        // The ID comes from the body actually being visited. Look it up only
        // in the canonical lowering's own body map, never the reverse.
        let original = self
            .tcx
            .lower_to_hir(body.value.hir_id.owner.def_id)
            .as_owner()
            .and_then(|raw| raw.nodes.bodies.get(&body.id().hir_id.local_id).copied());
        if original.is_none_or(|raw| !std::ptr::eq(raw, body)) {
            self.unknowns
                .push("a traversed body differs from its original lowering".into());
            return;
        }
        // walk_body deliberately skips native first-class contract fields.
        // They need their own ordered classifier, even without a builtin call.
        if body.contract.is_some() {
            self.unknowns.push(
                "native first-class clauses require a separate header producer policy".into(),
            );
        }
        self.bodies += 1;
        intravisit::walk_body(self, body);
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        self.expressions += 1;
        self.expansions.insert(expr.span.ctxt().outer_expn());
        let attributes = self.tcx.hir_attrs(expr.hir_id);
        match attrs::verus_parse(attributes) {
            Err(problem) => self
                .unknowns
                .push(format!("an unclassified expression attribute: {problem:?}")),
            Ok(parsed) if parsed.rustc.is_some() || parsed.deprecated.is_some() => self
                .unknowns
                .push("an unsupported compiler/deprecated expression directive".into()),
            Ok(_) => {}
        }
        for (attribute, span) in attrs::verus_attrs(attributes) {
            if let VerusAttr::Unknown(name) = attribute {
                self.unknowns.push(format!(
                    "an unclassified expression directive: {name} at {span:?}"
                ));
            }
        }
        match expr.kind {
            hir::ExprKind::Path(path) => {
                let typeck = self
                    .tcx
                    .typeck(self.tcx.typeck_root_def_id_local(expr.hir_id.owner.def_id));
                match typeck.qpath_res(&path, expr.hir_id) {
                    Res::Def(_, def) => self.reference(def, expr),
                    Res::Err => self.unknowns.push("an unresolved expression path".into()),
                    _ => {}
                }
            }
            hir::ExprKind::MethodCall(..) => {
                let typeck = self
                    .tcx
                    .typeck(self.tcx.typeck_root_def_id_local(expr.hir_id.owner.def_id));
                match typeck.type_dependent_def_id(expr.hir_id) {
                    Some(def) => self.reference(def, expr),
                    None => self.unknowns.push("an unresolved method call".into()),
                }
            }
            _ => {}
        }
        intravisit::walk_expr(self, expr);
    }
}

fn original_attributes<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
) -> Option<&'tcx [rustc_attr_ir::Attribute]> {
    let hir_id = tcx.local_def_id_to_hir_id(owner);
    let original = tcx
        .lower_to_hir(owner)
        .as_owner()?
        .attrs
        .get(hir_id.local_id);
    std::ptr::eq(original, tcx.hir_attrs(hir_id)).then_some(original)
}

fn leading_recommendation<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    body: &'tcx hir::Body<'tcx>,
    walk: &HeaderWalk<'tcx>,
) -> Option<RecommendationHeader<'tcx>> {
    if !walk.unknowns.is_empty()
        || attrs::item_attrs(original_attributes(tcx, owner)?).mode
            != Some(trust_vc_vcir::Mode::Spec)
    {
        return None;
    }
    let [reference] = walk.references.as_slice() else {
        return None;
    };
    if reference.item != VerusItem::Recommends || reference.expression_owner != owner {
        return None;
    }
    let hir::ExprKind::Block(block, None) = body.value.kind else {
        return None;
    };
    let hir::StmtKind::Semi(call) = block.stmts.first()?.kind else {
        return None;
    };
    let hir::ExprKind::Call(function, [argument]) = call.kind else {
        return None;
    };
    let hir::ExprKind::Path(ref path) = function.kind else {
        return None;
    };
    let typeck = tcx.typeck(tcx.typeck_root_def_id_local(owner));
    if function.hir_id != reference.expression
        || !matches!(typeck.qpath_res(path, function.hir_id), Res::Def(DefKind::Fn, definition) if definition == reference.definition)
    {
        return None;
    }
    Some(RecommendationHeader {
        owner,
        body,
        builtin: reference.definition,
        argument,
    })
}

pub(super) fn check<'tcx>(tcx: TyCtxt<'tcx>, owner: LocalDefId) -> CheckedHeaders<'tcx> {
    check_inner(tcx, owner, false)
}

/// Inline declarations cannot donate an empty-header fact through this path.
/// Their actual body still needs its separate checked forwarding capability.
pub(super) fn check_inline_recommendations<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
) -> CheckedHeaders<'tcx> {
    check_inner(tcx, owner, true)
}

fn check_inner<'tcx>(tcx: TyCtxt<'tcx>, owner: LocalDefId, inline: bool) -> CheckedHeaders<'tcx> {
    let mut walk = HeaderWalk {
        tcx,
        owner,
        items: HashMap::new(),
        references: Vec::new(),
        unknowns: Vec::new(),
        expansions: HashSet::new(),
        expressions: 0,
        bodies: 0,
    };
    let body = if !matches!(tcx.def_kind(owner), DefKind::Fn | DefKind::AssocFn)
        || !original_body_available(tcx, owner)
    {
        walk.unknowns
            .push("the original unprojected function body is not established".into());
        None
    } else {
        tcx.hir_maybe_body_owned_by(owner)
    };
    if let Some(body) = body {
        let parent = tcx.local_parent(owner);
        if !matches!(
            tcx.def_kind(parent),
            DefKind::Mod | DefKind::Impl { of_trait: false }
        ) || tcx.trait_impl_of_assoc(owner.to_def_id()).is_some()
        {
            walk.unknowns.push("trait/default/inherited or nested declaration origin needs its own header producer policy".into());
        }
        let attributes = tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner));
        let parsed = attrs::item_attrs(attributes);
        let bodyless_spec = parsed.mode == Some(trust_vc_vcir::Mode::Spec)
            && parsed.uninterp
            && parsed.external_body;
        let inline_spec = inline
            && parsed.mode == Some(trust_vc_vcir::Mode::Spec)
            && parsed.inline
            && parsed.open
            && !parsed.uninterp
            && !parsed.external_body
            && tcx.visibility(owner).is_public();
        if !parsed.verus_macro
            || attrs::verus_parse(attributes).is_err()
            || original_attributes(tcx, owner).is_none()
            || (inline && !inline_spec)
        {
            walk.unknowns
                .push("an unclassified declaration attribute or non-Verus origin".into());
        }
        for (attribute, span) in attrs::verus_attrs(attributes) {
            // A bodyless Spec declaration supplies only a pure signature.
            // Still traverse its actual original body: hidden, misplaced or
            // nonempty headers cannot be erased along with the placeholder.
            if bodyless_spec && matches!(attribute, VerusAttr::Uninterp | VerusAttr::ExternalBody) {
                continue;
            }
            if inline_spec && matches!(attribute, VerusAttr::Inline) {
                continue;
            }
            if !matches!(
                attribute,
                VerusAttr::VerusMacro
                    | VerusAttr::Mode(_)
                    | VerusAttr::ReturnMode(_)
                    | VerusAttr::Visibility { .. }
            ) {
                walk.unknowns.push(format!(
                    "an unsupported declaration directive: {attribute:?} at {span:?}"
                ));
            }
        }
        if walk.unknowns.is_empty() {
            walk.items = tcx
                .all_diagnostic_items(())
                .name_to_id
                .iter()
                .filter_map(|(name, def)| {
                    VerusItem::from_name(name.as_str()).map(|item| (*def, item))
                })
                .collect();
            walk.visit_body(body);
        }
    }
    let recommendation = body.and_then(|body| leading_recommendation(tcx, owner, body, &walk));
    let outcome = if !walk.unknowns.is_empty() || (inline && walk.references.is_empty()) {
        Outcome::Unknown
    } else if walk.references.is_empty() {
        match body {
            Some(body) => Outcome::Empty(EmptyHeader { owner, body }),
            None => Outcome::Unknown,
        }
    } else {
        Outcome::Nonempty
    };
    CheckedHeaders {
        tcx,
        owner,
        outcome,
        walk,
        recommendation,
    }
}
