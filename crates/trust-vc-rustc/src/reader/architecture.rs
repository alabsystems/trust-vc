//! Native primitive/architecture identities. Source names alone never select
//! the crate, primitive owner or a builtin function.

extern crate rustc_abi;

use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, TyCtxt};
use trust_vc_vcir::{IntRange, IntegerConstant};

/// A constant of the actual core primitive inherent implementation. `MIN`,
/// `MAX` and `BITS` choose a semantic operation only after native crate,
/// primitive Self, nongeneric owner and exact result-type checks.
pub(super) fn integer_constant(tcx: TyCtxt<'_>, definition: DefId) -> Option<IntegerConstant> {
    if tcx.dcx().has_errors().is_some()
        || definition.is_local()
        || tcx.def_kind(definition) != DefKind::AssocConst
        || tcx.lang_items().sized_trait()?.krate != definition.krate
    {
        return None;
    }
    let owner = tcx.parent(definition);
    if tcx.def_kind(owner) != (DefKind::Impl { of_trait: false })
        || tcx.generics_of(owner).count() != 0
        || tcx.generics_of(definition).count() != 0
        || !tcx.clauses_of(owner).clauses.is_empty()
        || !tcx.clauses_of(definition).clauses.is_empty()
    {
        return None;
    }
    let self_ty = tcx
        .try_normalize_erasing_regions(
            ty::TypingEnv::non_body_analysis(tcx, owner),
            tcx.type_of(owner).instantiate_identity(),
        )
        .ok()?;
    let range = match self_ty.kind() {
        ty::Uint(kind) => match kind.bit_width() {
            Some(bits) => IntRange::U(bits as u32),
            None => IntRange::USize,
        },
        ty::Int(kind) => match kind.bit_width() {
            Some(bits) => IntRange::I(bits as u32),
            None => IntRange::ISize,
        },
        _ => return None,
    };
    let result = tcx
        .try_normalize_erasing_regions(
            ty::TypingEnv::non_body_analysis(tcx, definition),
            tcx.type_of(definition).instantiate_identity(),
        )
        .ok()?;
    match tcx.item_name(definition).as_str() {
        "MIN" if result == self_ty => Some(IntegerConstant::Minimum(range)),
        "MAX" if result == self_ty => Some(IntegerConstant::Maximum(range)),
        "BITS" if matches!(result.kind(), ty::Uint(ty::UintTy::U32)) => {
            Some(IntegerConstant::Bits(range))
        }
        _ => None,
    }
}

use super::{attrs, Refusal, UserError};
use crate::{messages::Phase, verus_items::VerusItem};
use rustc_ast::token::TokenKind;
use rustc_ast::tokenstream::{TokenStream, TokenTree};
use rustc_attr_ir::{AttrArgs, Attribute};
use rustc_hir::{self as hir, def_id::LocalDefId, OwnerNode};
use std::collections::HashMap;
use trust_vc_vcir::bitvector::Architecture;

const GLOBAL: &str = "verus::internal(size_of)";

struct Directive<'tcx> {
    owner: LocalDefId,
    attributes: &'tcx [Attribute],
    body: &'tcx hir::Body<'tcx>,
}

/// A checked current-native directive, not macro provenance or a library
/// capability. Only the exact local const is consumed; its separately emitted
/// layout proof helper keeps every ordinary function/import obligation.
pub(super) struct Selection<'tcx> {
    tcx: TyCtxt<'tcx>,
    architecture: Architecture,
    directives: HashMap<LocalDefId, Directive<'tcx>>,
}

impl<'tcx> Selection<'tcx> {
    pub(super) fn architecture(&self) -> Architecture {
        self.architecture
    }

    pub(super) fn consumes(&self, tcx: TyCtxt<'tcx>, owner: LocalDefId) -> bool {
        std::ptr::eq(*tcx, *self.tcx)
            && tcx.dcx().has_errors().is_none()
            && self.directives.get(&owner).is_some_and(|entry| {
                entry.owner == owner
                    && !super::function_identity_observer::body_is_quarantined(tcx.sess, owner)
                    && std::ptr::eq(
                        entry.attributes,
                        tcx.hir_attrs(tcx.local_def_id_to_hir_id(owner)),
                    )
                    && tcx
                        .hir_maybe_body_owned_by(owner)
                        .is_some_and(|body| std::ptr::eq(body, entry.body))
            })
    }
}

fn token_work(stream: &TokenStream, work: &mut usize, depth: usize) -> Result<(), ()> {
    if depth >= 16 {
        return Err(());
    }
    for tree in stream.iter() {
        *work = work.checked_sub(1).ok_or(())?;
        match tree {
            TokenTree::Delimited(_, _, _, children) => token_work(children, work, depth + 1)?,
            TokenTree::Token(token, _) => {
                let bytes = match token.kind {
                    TokenKind::Ident(name, _) => name.as_str().len(),
                    TokenKind::Literal(literal) => literal.symbol.as_str().len(),
                    _ => 0,
                };
                *work = work.checked_sub(bytes).ok_or(())?;
            }
        }
    }
    Ok(())
}

fn candidate(attributes: &[Attribute], work: &mut usize) -> Result<bool, ()> {
    let mut found = false;
    for attribute in attributes {
        *work = work.checked_sub(1).ok_or(())?;
        let Attribute::Unparsed(item) = attribute else {
            continue;
        };
        if let AttrArgs::Delimited(delimited) = &item.args {
            if item.path.segments.len() == 2 && item.path.segments[0].as_str() == "verus"
                && item.path.segments[1].as_str() == "internal"
                && delimited.tokens.iter().next().is_some_and(|tree| matches!(tree,
                    TokenTree::Token(token, _) if matches!(token.kind, TokenKind::Ident(name, _) if name.as_str() == "size_of")))
            { found = true; }
        }
    }
    // Irrelevant items do not pay for or parse unrelated attribute payloads.
    // Once a marker is present, bound the complete ordinary parse before its
    // token/string constructors see any of this owner's Verus attributes.
    if found {
        for attribute in attributes {
            let Attribute::Unparsed(item) = attribute else {
                continue;
            };
            if item.path.segments.len() > 16 {
                return Err(());
            }
            for part in &item.path.segments {
                *work = work.checked_sub(part.as_str().len()).ok_or(())?;
            }
            if !item
                .path
                .segments
                .first()
                .is_some_and(|part| matches!(part.as_str(), "verus" | "verifier"))
            {
                continue;
            }
            if let AttrArgs::Delimited(delimited) = &item.args {
                token_work(&delimited.tokens, work, 0)?;
            }
        }
    }
    Ok(found)
}

fn pointer_directive<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    items: &HashMap<DefId, VerusItem>,
) -> Option<(Directive<'tcx>, bool, u128)> {
    let raw = tcx.lower_to_hir(owner).as_owner()?;
    let OwnerNode::Item(original) = raw.node() else {
        return None;
    };
    let hir::Node::Item(current) = tcx.hir_node_by_def_id(owner) else {
        return None;
    };
    if !std::ptr::eq(original, current) {
        return None;
    }
    let hir::ItemKind::Const(_, generics, _, hir::ConstItemRhs::Body(body_id)) = current.kind
    else {
        return None;
    };
    let native = tcx.generics_of(owner);
    let clauses = tcx.clauses_of(owner);
    if !generics.params.is_empty()
        || !generics.predicates.is_empty()
        || native.parent.is_some()
        || !native.own_params.is_empty()
        || clauses.parent.is_some()
        || !clauses.clauses.is_empty()
        || super::function_identity_observer::body_is_quarantined(tcx.sess, owner)
    {
        return None;
    }
    let declared_type = tcx
        .try_normalize_erasing_regions(
            ty::TypingEnv::non_body_analysis(tcx, owner),
            tcx.type_of(owner).instantiate_identity(),
        )
        .ok()?;
    if !declared_type.is_unit() {
        return None;
    }
    let body = tcx.hir_maybe_body_owned_by(owner)?;
    let original_body = raw.nodes.bodies.get(&body_id.hir_id.local_id).copied()?;
    if !std::ptr::eq(body, original_body) || !body.params.is_empty() {
        return None;
    }
    let hir::ExprKind::Block(block, None) = body.value.kind else {
        return None;
    };
    if block.stmts.len() != 1 || block.expr.is_some() {
        return None;
    }
    let hir::StmtKind::Semi(call) = block.stmts[0].kind else {
        return None;
    };
    let hir::ExprKind::Call(function, [argument]) = call.kind else {
        return None;
    };
    let typeck = tcx.typeck(owner);
    let ty::FnDef(callee, args) = *typeck.expr_ty(function).kind() else {
        return None;
    };
    if callee.is_local()
        || items.get(&callee) != Some(&VerusItem::GlobalSizeOf)
        || !typeck.expr_ty(call).is_unit()
    {
        return None;
    }
    let args = args.no_bound_vars()?;
    let actual_args = typeck.node_args(function.hir_id);
    if actual_args.len() != 1 || actual_args != args {
        return None;
    }
    let normalized = tcx
        .try_normalize_erasing_regions(
            ty::TypingEnv::post_analysis(tcx, owner),
            tcx.fn_sig(callee).instantiate(tcx, actual_args),
        )
        .ok()?;
    let signature = normalized.no_bound_vars()?;
    if signature.abi() != rustc_abi::ExternAbi::Rust
        || !signature.safety().is_safe()
        || signature.c_variadic()
        || signature.splatted().is_some()
        || signature.inputs() != [tcx.types.usize]
        || !signature.output().is_unit()
        || typeck.expr_ty(argument) != tcx.types.usize
    {
        return None;
    }
    let ty::GenericArgKind::Type(target) = actual_args[0].kind() else {
        return None;
    };
    let signed = match target.kind() {
        ty::Uint(ty::UintTy::Usize) => false,
        ty::Int(ty::IntTy::Isize) => true,
        _ => return None,
    };
    let hir::ExprKind::Lit(literal) = argument.kind else {
        return None;
    };
    let rustc_ast::ast::LitKind::Int(size, rustc_ast::ast::LitIntType::Unsuffixed) = literal.node
    else {
        return None;
    };
    Some((
        Directive {
            owner,
            attributes: tcx.hir_attrs(current.hir_id()),
            body,
        },
        signed,
        size.get(),
    ))
}

pub(super) fn collect<'tcx>(
    tcx: TyCtxt<'tcx>,
    items: &HashMap<DefId, VerusItem>,
) -> (Selection<'tcx>, Vec<UserError>, Vec<Refusal>) {
    let mut selection = Selection {
        tcx,
        architecture: Architecture::Either32Or64,
        directives: HashMap::new(),
    };
    let mut errors = Vec::new();
    let mut refusals = Vec::new();
    let mut sizes = HashMap::<bool, u128>::new();
    let mut work = 200_000usize;
    for owner in tcx.hir_crate_items(()).owners() {
        let definition = owner.def_id;
        let span = tcx.def_span(definition);
        let Some(next) = work.checked_sub(1) else {
            refusals.push(Refusal::new(
                "architecture-budget",
                "native architecture owner inventory exceeded its bound",
                span,
            ));
            break;
        };
        work = next;
        let attributes = tcx.hir_attrs(tcx.local_def_id_to_hir_id(definition));
        match candidate(attributes, &mut work) {
            Ok(false) => continue,
            Err(()) => {
                refusals.push(Refusal::new(
                    "architecture-budget",
                    "native architecture inventory exceeded its bound",
                    span,
                ));
                break;
            }
            Ok(true) => {}
        }
        if let Err(problem) = attrs::verus_parse(attributes) {
            match problem {
                attrs::AttrProblem::Error(at, message) => {
                    errors.push(UserError::new(Phase::RustToVir, at, message))
                }
                attrs::AttrProblem::Unmodelled(at, detail) => {
                    refusals.push(Refusal::new("architecture-attribute", detail, at))
                }
            }
            continue;
        }
        let parsed = attrs::verus_attrs(attributes);
        if parsed
            .iter()
            .filter(|(attr, _)| matches!(attr, attrs::VerusAttr::Unknown(name) if name == GLOBAL))
            .count()
            != 1
            || parsed.iter().any(|(attr, _)| {
                !matches!(attr, attrs::VerusAttr::VerusMacro)
                    && !matches!(attr, attrs::VerusAttr::Unknown(name) if name == GLOBAL)
            })
        {
            refusals.push(Refusal::new(
                "architecture-attribute",
                "unconsumed attributes on a global pointer-size declaration",
                span,
            ));
            continue;
        }
        let Some((directive, signed, bytes)) = pointer_directive(tcx, definition, items) else {
            refusals.push(Refusal::new(
                "global-size-of",
                "a global layout declaration outside the exact original pointer-size fragment",
                span,
            ));
            continue;
        };
        // Identity recognition is separate from semantic validity. A genuine
        // native directive with a source error must not fall through to the
        // generic outside-macro attribute refusal. It still selects no width
        // until the checks below succeed, and its error blocks verification.
        selection.directives.insert(definition, directive);
        if sizes.insert(signed, bytes).is_some() {
            errors.push(UserError::new(
                Phase::RustToVir,
                span,
                format!(
                    "the size of `{}` can only be set once per crate",
                    if signed { "isize" } else { "usize" }
                ),
            ));
            continue;
        }
        if !matches!(bytes, 4 | 8) {
            errors.push(UserError::new(
                Phase::RustToVir,
                span,
                "usize and isize can be either 32 or 64 bits",
            ));
            continue;
        }
        let width = (bytes * 8) as u32;
        if let Architecture::Exactly(previous) = selection.architecture {
            if previous != width {
                errors.push(UserError::new(
                    Phase::RustToVir,
                    span,
                    format!("usize or isize have already been set to {previous} bits"),
                ));
                continue;
            }
        }
        selection.architecture = Architecture::Exactly(width);
    }
    (selection, errors, refusals)
}
