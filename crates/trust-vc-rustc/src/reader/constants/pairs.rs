//! Additional constant roles, bound to both original native definitions.
//!
//! A generated spelling only locates candidates. This module grants neither a
//! body equation nor ownership. New-role reads still need complete modes and
//! the normal native erased program, body, contract and dependency checks.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
use super::*;
use rustc_hir::def::{MacroKinds, Res};
use rustc_hir::def_id::DefId;
use rustc_span::{ExpnId, Span};

#[derive(Default)]
pub(super) struct Pairs<'tcx> {
    items: HashMap<LocalDefId, Pair<'tcx>>,
}

struct Pair<'tcx> {
    tcx: TyCtxt<'tcx>,
    proxy: LocalDefId,
    real: LocalDefId,
    kind: FnKind,
    proxy_body: &'tcx hir::Body<'tcx>,
    real_body: &'tcx hir::Body<'tcx>,
    expansion: ExpnId,
    macro_definition: DefId,
}

/// The selected native macro definition, not an expansion's displayed name.
/// Its image/source provenance is separately pinned by the genuine frontend
/// invocation. No saved identifier or caller-created registry can select it.
fn selected_macro(tcx: TyCtxt<'_>) -> Option<DefId> {
    let mut definitions = tcx.crates(()).iter().filter_map(|&krate| {
        if tcx.crate_name(krate).as_str() != "verus_builtin_macros" {
            return None;
        }
        let root = DefId {
            krate,
            index: rustc_hir::def_id::CRATE_DEF_INDEX,
        };
        let mut candidates = tcx
            .module_children(root)
            .iter()
            .filter_map(|child| match child.res {
                Res::Def(DefKind::Macro(MacroKinds::BANG), def)
                    if child.ident.name.as_str() == "verus" && def.krate == krate =>
                {
                    Some(def)
                }
                _ => None,
            });
        let selected = candidates.next()?;
        candidates.next().is_none().then_some(selected)
    });
    let selected = definitions.next()?;
    definitions.next().is_none().then_some(selected)
}

fn marker_expansion(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    keyword: &str,
    definition: DefId,
) -> Option<ExpnId> {
    use rustc_ast::{token::TokenKind, tokenstream::TokenTree};
    use rustc_attr_ir::{AttrArgs, Attribute};
    let mut found = None;
    for attribute in tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner)) {
        let Attribute::Tool(item) = attribute else {
            continue;
        };
        if item.path.segments.len() != 2
            || item.path.segments[0].as_str() != "verus"
            || item.path.segments[1].as_str() != "internal"
        {
            continue;
        }
        let AttrArgs::Delimited(arguments) = &item.args else {
            continue;
        };
        let mut tokens = arguments.tokens.iter();
        let Some(TokenTree::Token(token, _)) = tokens.next() else {
            continue;
        };
        let TokenKind::Ident(name, _) = token.kind else {
            continue;
        };
        if name.as_str() != keyword || tokens.next().is_some() {
            continue;
        }
        // A40's mk_verus_attr uses quote! for THIS keyword, while forwarding
        // source item/type/body spans. Forwarded user-written markers do not
        // become macro-generated merely because the item was inside verus!.
        if token.span.ctxt().is_root() {
            return None;
        }
        let expansion = token.span.ctxt().outer_expn();
        if expansion.expn_data().macro_def_id != Some(definition) || found.is_some() {
            return None;
        }
        found = Some(expansion);
    }
    found
}

fn function<'tcx>(tcx: TyCtxt<'tcx>, def: LocalDefId) -> Option<(&'tcx hir::FnSig<'tcx>, Span)> {
    match tcx.hir_node_by_def_id(def) {
        Node::Item(item) => match &item.kind {
            hir::ItemKind::Fn { sig, .. } => Some((sig, item.span)),
            _ => None,
        },
        Node::ImplItem(item) => match &item.kind {
            hir::ImplItemKind::Fn(sig, _) => Some((sig, item.span)),
            _ => None,
        },
        _ => None,
    }
}

fn generic_identity(tcx: TyCtxt<'_>, proxy: LocalDefId, real: LocalDefId) -> bool {
    let left = tcx.generics_of(proxy);
    let right = tcx.generics_of(real);
    left.parent == right.parent
        && left.parent_count == right.parent_count
        && left.own_params.len() == right.own_params.len()
        && left.own_params.iter().zip(&right.own_params).all(|(p, r)| {
            p.index == r.index
                && p.name == r.name
                && match (&p.kind, &r.kind) {
                    (ty::GenericParamDefKind::Lifetime, ty::GenericParamDefKind::Lifetime) => true,
                    (
                        ty::GenericParamDefKind::Type { has_default: a, .. },
                        ty::GenericParamDefKind::Type { has_default: b, .. },
                    ) => a == b,
                    _ => false, // const parameters require their own represented semantics
                }
        })
        && tcx.explicit_clauses_of(proxy).clauses == tcx.explicit_clauses_of(real).clauses
}

fn original_body(tcx: TyCtxt<'_>, def: LocalDefId, body: &hir::Body<'_>) -> bool {
    let Some(raw) = tcx.lower_to_hir(def).as_owner() else {
        return false;
    };
    let Some(id) = raw.node().body_id() else {
        return false;
    };
    let root = tcx.local_def_id_to_hir_id(def);
    !super::super::function_identity_observer::body_is_quarantined(tcx.sess, def)
        && std::ptr::eq(raw.attrs.get(root.local_id), tcx.hir_attrs(root))
        && raw
            .nodes
            .bodies
            .get(&id.hir_id.local_id)
            .is_some_and(|original| std::ptr::eq(*original, body))
}

impl<'tcx> Pairs<'tcx> {
    pub(super) fn collect(tcx: TyCtxt<'tcx>, owners: &[LocalDefId]) -> Self {
        let mut out = Self::default();
        let Some(macro_definition) = selected_macro(tcx) else {
            return out;
        };
        let mut candidates = HashMap::<_, Vec<_>>::new();
        for &real in owners {
            if marker_count(tcx, real, REAL) == 1 {
                candidates
                    .entry((tcx.local_parent(real), tcx.item_name(real.to_def_id())))
                    .or_default()
                    .push(real);
            }
        }
        for &proxy in owners {
            if marker_count(tcx, proxy, PROXY) != 1 || marker_count(tcx, proxy, REAL) != 0 {
                continue;
            }
            let parent = tcx.local_parent(proxy);
            if !matches!(
                tcx.def_kind(parent),
                DefKind::Mod | DefKind::Impl { of_trait: false }
            ) {
                continue;
            }
            let name = tcx.item_name(proxy.to_def_id());
            let Some(real_name) = name.as_str().strip_prefix(PROXY_PREFIX) else {
                continue;
            };
            let Some([real]) = candidates
                .get(&(parent, rustc_span::Symbol::intern(real_name)))
                .map(Vec::as_slice)
            else {
                continue;
            };
            let real = *real;
            let attributes = attrs::item_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(proxy)));
            let real_attrs = attrs::item_attrs(tcx.hir_attrs(tcx.local_def_id_to_hir_id(real)));
            if !attributes.verus_macro
                || attributes.external
                || !real_attrs.external
                || marker_count(tcx, real, PROXY) != 0
                || marker_count(tcx, real, CONSTANT) != 0
                || marker_count(tcx, real, STATIC) != 0
                || tcx.visibility(proxy) != tcx.visibility(real)
                || !generic_identity(tcx, proxy, real)
            {
                continue;
            }
            let Some((sig, proxy_span)) = function(tcx, proxy) else {
                continue;
            };
            let Some(proxy_body) = tcx.hir_maybe_body_owned_by(proxy) else {
                continue;
            };
            let Some(real_body) = tcx.hir_maybe_body_owned_by(real) else {
                continue;
            };
            if !sig.header.is_safe()
                || sig.header.is_async()
                || proxy_body.value.span != real_body.value.span
            {
                continue;
            }
            let Some(original_expansion) =
                marker_expansion(tcx, proxy, "unerased_proxy", macro_definition)
            else {
                continue;
            };
            if marker_expansion(tcx, real, "uses_unerased_proxy", macro_definition)
                != Some(original_expansion)
            {
                continue;
            }
            let const_marker = marker_count(tcx, proxy, CONSTANT);
            let static_marker = marker_count(tcx, proxy, STATIC);
            let kind = match tcx.hir_node_by_def_id(real) {
                Node::Item(item) => match &item.kind {
                    hir::ItemKind::Static(rustc_ast::Mutability::Not, _, real_ty, _)
                        if attributes.mode == Some(Mode::Exec)
                            && const_marker == 0
                            && static_marker == 1
                            && tcx.generics_of(proxy).count() == 0
                            && sig.decl.inputs.is_empty() =>
                    {
                        if !value_signature(tcx, proxy, real, sig, proxy_span, item.span, real_ty) {
                            continue;
                        }
                        FnKind::Static
                    }
                    hir::ItemKind::Const(_, _, real_ty, _)
                        if attributes.mode == Some(Mode::Exec)
                            && const_marker == 1
                            && static_marker == 0
                            && sig.decl.inputs.is_empty() =>
                    {
                        if !value_signature(tcx, proxy, real, sig, proxy_span, item.span, real_ty) {
                            continue;
                        }
                        FnKind::Constant(ConstMode::Exec)
                    }
                    hir::ItemKind::Fn { sig: real_sig, .. }
                        if const_marker == 0
                            && static_marker == 0
                            && matches!(
                                real_sig.header.constness,
                                hir::Constness::Const { .. }
                            ) =>
                    {
                        if !function_signature(
                            tcx, proxy, real, sig, real_sig, proxy_span, item.span,
                        ) {
                            continue;
                        }
                        FnKind::ConstFunction
                    }
                    _ => continue,
                },
                Node::ImplItem(item) => match &item.kind {
                    hir::ImplItemKind::Const(real_ty, _)
                        if attributes.mode == Some(Mode::Exec)
                            && const_marker == 1
                            && static_marker == 0
                            && sig.decl.inputs.is_empty() =>
                    {
                        if !value_signature(tcx, proxy, real, sig, proxy_span, item.span, real_ty) {
                            continue;
                        }
                        FnKind::Constant(ConstMode::Exec)
                    }
                    hir::ImplItemKind::Fn(real_sig, _)
                        if const_marker == 0
                            && static_marker == 0
                            && matches!(
                                real_sig.header.constness,
                                hir::Constness::Const { .. }
                            ) =>
                    {
                        if !function_signature(
                            tcx, proxy, real, sig, real_sig, proxy_span, item.span,
                        ) {
                            continue;
                        }
                        FnKind::ConstFunction
                    }
                    _ => continue,
                },
                _ => continue,
            };
            let encoded = match kind {
                FnKind::Static => Some("encoded_static"),
                FnKind::Constant(ConstMode::Exec) => Some("encoded_const"),
                FnKind::ConstFunction => None,
                _ => continue,
            };
            if encoded.is_some_and(|keyword| {
                marker_expansion(tcx, proxy, keyword, macro_definition) != Some(original_expansion)
            }) {
                continue;
            }
            out.items.insert(
                proxy,
                Pair {
                    tcx,
                    proxy,
                    real,
                    kind,
                    proxy_body,
                    real_body,
                    expansion: original_expansion,
                    macro_definition,
                },
            );
        }
        out
    }

    pub(super) fn items(
        &self,
    ) -> impl Iterator<Item = (LocalDefId, LocalDefId, FnKind)> + use<'_, 'tcx> {
        self.items.values().map(|p| (p.proxy, p.real, p.kind))
    }

    pub(super) fn kind(&self, proxy: LocalDefId) -> Option<FnKind> {
        self.items.get(&proxy).map(|p| p.kind)
    }

    pub(super) fn current(&self, tcx: TyCtxt<'tcx>, proxy: LocalDefId) -> bool {
        let Some(p) = self.items.get(&proxy) else {
            return false;
        };
        std::ptr::eq(*tcx, *p.tcx)
            && tcx.dcx().has_errors().is_none()
            && original_body(tcx, proxy, p.proxy_body)
            && original_body(tcx, p.real, p.real_body)
            && tcx
                .hir_maybe_body_owned_by(proxy)
                .is_some_and(|b| std::ptr::eq(b, p.proxy_body))
            && tcx
                .hir_maybe_body_owned_by(p.real)
                .is_some_and(|b| std::ptr::eq(b, p.real_body))
            && marker_expansion(tcx, proxy, "unerased_proxy", p.macro_definition)
                == Some(p.expansion)
            && marker_expansion(tcx, p.real, "uses_unerased_proxy", p.macro_definition)
                == Some(p.expansion)
            && match p.kind {
                FnKind::Static => {
                    marker_expansion(tcx, proxy, "encoded_static", p.macro_definition)
                        == Some(p.expansion)
                }
                FnKind::Constant(ConstMode::Exec) => {
                    marker_expansion(tcx, proxy, "encoded_const", p.macro_definition)
                        == Some(p.expansion)
                }
                FnKind::ConstFunction => true,
                _ => false,
            }
    }
}

fn value_signature(
    tcx: TyCtxt<'_>,
    proxy: LocalDefId,
    real: LocalDefId,
    sig: &hir::FnSig<'_>,
    proxy_span: Span,
    real_span: Span,
    real_ty: &hir::Ty<'_>,
) -> bool {
    let hir::FnRetTy::Return(output) = sig.decl.output else {
        return false;
    };
    sig.decl.inputs.is_empty()
        && matches!(sig.header.constness, hir::Constness::NotConst)
        && output.span == real_ty.span
        && proxy_span.lo() == real_span.lo()
        && tcx
            .try_normalize_erasing_regions(
                ty::TypingEnv::non_body_analysis(tcx, real.to_def_id()),
                tcx.type_of(real).instantiate_identity(),
            )
            .is_ok_and(|real_type| {
                tcx.fn_sig(proxy)
                    .instantiate_identity()
                    .skip_binder()
                    .output()
                    == real_type
            })
}

fn function_signature(
    tcx: TyCtxt<'_>,
    proxy: LocalDefId,
    real: LocalDefId,
    sig: &hir::FnSig<'_>,
    real_sig: &hir::FnSig<'_>,
    proxy_span: Span,
    real_span: Span,
) -> bool {
    // Identity projection only. Erased ghost parameters need a separately
    // authenticated source-mode/erasure map and remain refused here.
    sig.decl.inputs.len() == real_sig.decl.inputs.len()
        && sig
            .decl
            .inputs
            .iter()
            .zip(real_sig.decl.inputs)
            .all(|(a, b)| a.span == b.span)
        && sig.decl.output.span() == real_sig.decl.output.span()
        && proxy_span.lo() == real_span.lo()
        && real_sig.header.is_safe()
        && !real_sig.header.is_async()
        && tcx.erase_and_anonymize_regions(tcx.fn_sig(proxy).instantiate_identity().skip_binder())
            == tcx
                .erase_and_anonymize_regions(tcx.fn_sig(real).instantiate_identity().skip_binder())
}

/// Exact original occurrence selected during the complete native mode walk.
#[derive(Clone)]
pub(in crate::reader) struct Use<'tcx> {
    tcx: TyCtxt<'tcx>,
    caller: LocalDefId,
    body: &'tcx hir::Body<'tcx>,
    typeck: &'tcx ty::TypeckResults<'tcx>,
    expression: &'tcx hir::Expr<'tcx>,
    pub(in crate::reader) original: DefId,
    pub(in crate::reader) declaration: LocalDefId,
    pub(in crate::reader) arguments: ty::GenericArgs<'tcx>,
    pub(in crate::reader) kind: FnKind,
}
impl std::fmt::Debug for Use<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ConstantUse")
            .field("caller", &self.caller)
            .field("expression", &self.expression.hir_id)
            .field("declaration", &self.declaration)
            .field("kind", &self.kind)
            .finish_non_exhaustive()
    }
}
impl Use<'_> {
    pub(in crate::reader) fn same_selection(&self, other: &Self) -> bool {
        std::ptr::eq(*self.tcx, *other.tcx)
            && self.caller == other.caller
            && std::ptr::eq(self.body, other.body)
            && std::ptr::eq(self.typeck, other.typeck)
            && std::ptr::eq(self.expression, other.expression)
            && self.original == other.original
            && self.declaration == other.declaration
            && self.arguments == other.arguments
            && self.kind == other.kind
    }
}
impl<'tcx> Pairs<'tcx> {
    pub(in crate::reader) fn select(
        &self,
        tcx: TyCtxt<'tcx>,
        caller: LocalDefId,
        typeck: &'tcx ty::TypeckResults<'tcx>,
        expression: &'tcx hir::Expr<'tcx>,
    ) -> Result<Option<Use<'tcx>>, String> {
        let (original, arguments) = match expression.kind {
            hir::ExprKind::Path(ref path) => match typeck.qpath_res(path, expression.hir_id) {
                Res::Def(
                    DefKind::Const | DefKind::AssocConst | DefKind::Static { .. },
                    definition,
                ) => (definition, typeck.node_args(expression.hir_id)),
                _ => return Ok(None),
            },
            hir::ExprKind::Call(function, _) => {
                let hir::ExprKind::Path(ref path) = function.kind else {
                    return Ok(None);
                };
                match typeck.qpath_res(path, function.hir_id) {
                    Res::Def(DefKind::Fn | DefKind::AssocFn, definition) => {
                        (definition, typeck.node_args(function.hir_id))
                    }
                    _ => return Ok(None),
                }
            }
            hir::ExprKind::MethodCall(..) => {
                let Some(definition) = typeck.type_dependent_def_id(expression.hir_id) else {
                    return Ok(None);
                };
                (definition, typeck.node_args(expression.hir_id))
            }
            _ => return Ok(None),
        };
        let Some(pair) = self
            .items
            .values()
            .find(|pair| pair.real.to_def_id() == original)
        else {
            return Ok(None);
        };
        if !self.current(tcx, pair.proxy)
            || typeck.tainted_by_errors.is_some()
            || !std::ptr::eq(typeck, tcx.typeck(caller))
            || expression.hir_id.owner.def_id != caller
            || !super::super::declaration_modes::original_body_available(tcx, caller)
        {
            return Err("the constant use is not in its original current native body".into());
        }
        let body = tcx.hir_body_owned_by(caller);
        Ok(Some(Use {
            tcx,
            caller,
            body,
            typeck,
            expression,
            original,
            declaration: pair.proxy,
            arguments,
            kind: pair.kind,
        }))
    }
}
