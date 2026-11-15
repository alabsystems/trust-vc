//! Parse a genuine metadata-only Verus function-identity helper.
//!
//! A function declaration is not a function-pointer value instantiated at
//! arbitrary inferred type arguments. The syntax macro uses a dedicated
//! helper to carry that declaration identity through name resolution. This
//! parser inspects the original compiler graph; it neither replaces a body
//! nor grants import, reveal, body-verification or ownership authority.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

extern crate rustc_abi;

use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::DefId;
use rustc_hir::{self as hir, OwnerNode};
use rustc_span::Span;

use super::attrs::{self, VerusAttr};

/// Retain every supported explicit receiver argument without selecting a type.
/// Native declaration lookup must establish its actual parameter kind first.
pub(super) struct ReceiverPlaceholder {
    pub(super) original_hir_id: hir::HirId,
    pub(super) span: Span,
    pub(super) syntax_kind: hir::InferArgKind,
}

pub(super) struct ReceiverArguments {
    pub(super) segment: usize,
    pub(super) span: Span,
    pub(super) placeholders: Vec<ReceiverPlaceholder>,
}

pub(super) struct ReceiverSyntax<'tcx> {
    pub(super) original_type: &'tcx hir::Ty<'tcx>,
    pub(super) path: &'tcx hir::Path<'tcx>,
    pub(super) explicit_arguments: Option<ReceiverArguments>,
}

/// Original, compiler-resolved syntax. An associated target is deliberately
/// not converted to a concrete implementation by matching a display name.
pub(super) enum Target<'tcx> {
    /// A generic declaration's own DefId, without invented substitutions.
    Declaration(DefId),
    /// A direct associated declaration is a native identity too, but its
    /// inherent/trait/default correspondence needs an explicit resolver step.
    AssociatedDeclaration(DefId),
    /// A fully qualified path names a declaration, but its Self/trait and
    /// implementation correspondence still needs the native resolver.
    Qualified {
        declaration: DefId,
        receiver: ReceiverSyntax<'tcx>,
        path: &'tcx hir::Path<'tcx>,
    },
    /// Name resolution deferred this associated member. Res::Err here is
    /// neither a successful identity nor permission to select the first impl.
    TypeRelative {
        receiver: ReceiverSyntax<'tcx>,
        member: &'tcx hir::PathSegment<'tcx>,
    },
}

impl Target<'_> {
    /// ORIGINAL IDs only; never query these through projected HIR/typeck.
    pub(super) fn original_receiver_ids(&self) -> Vec<hir::HirId> {
        let receiver = match self {
            Self::Qualified { receiver, .. } | Self::TypeRelative { receiver, .. } => receiver,
            _ => return Vec::new(),
        };
        let mut ids = vec![receiver.original_type.hir_id];
        if let Some(arguments) = &receiver.explicit_arguments {
            ids.extend(
                arguments
                    .placeholders
                    .iter()
                    .map(|argument| argument.original_hir_id),
            );
        }
        ids
    }
}

/// A checked helper shape, retaining its original graph for header/provenance
/// reads. This type alone does not authorize a Unit projection or import.
pub(super) struct ParsedHelper<'tcx> {
    pub(super) target: Target<'tcx>,
    pub(super) original_body: &'tcx hir::Body<'tcx>,
    pub(super) original_call: &'tcx hir::Expr<'tcx>,
    pub(super) original_operand: &'tcx hir::Expr<'tcx>,
    pub(super) marker_definition: DefId,
}

/// A malformed or unsupported helper retains its real source boundary.
pub(super) struct Problem {
    pub(super) at: Span,
    pub(super) detail: &'static str,
}

/// A candidate filter only; this attribute is never origin authority.
pub(super) fn is_candidate(owner: &hir::OwnerInfo<'_>) -> bool {
    attrs::verus_attrs(owner.attrs.get(hir::ItemLocalId::ZERO))
        .iter()
        .any(|(attribute, _)| *attribute == VerusAttr::RevealFn)
}

fn path_has_no_arguments(path: &hir::Path<'_>) -> bool {
    // Explicit generic syntax, especially const argument expressions, must
    // have its own checked representation before a projection may discard it.
    path.segments.iter().all(|segment| segment.args.is_none())
}

fn receiver_syntax<'tcx>(
    receiver: &'tcx hir::Ty<'tcx>,
) -> Result<ReceiverSyntax<'tcx>, &'static str> {
    let hir::TyKind::Path(hir::QPath::Resolved(None, path)) = receiver.kind else {
        return Err("the associated receiver is outside the supported original path shape");
    };
    let mut explicit_arguments = None;
    for (index, segment) in path.segments.iter().enumerate() {
        let Some(arguments) = segment.args else {
            continue;
        };
        if index + 1 != path.segments.len() {
            return Err("generic arguments on a receiver prefix require separate native binding");
        }
        if !arguments.constraints.is_empty()
            || arguments.parenthesized != hir::GenericArgsParentheses::No
        {
            return Err(
                "receiver binding constraints or parenthesized arguments are not discarded",
            );
        }
        let mut placeholders = Vec::new();
        for argument in arguments.args {
            let hir::GenericArg::Infer(infer) = argument else {
                return Err(
                    "only pure inference placeholders are represented in receiver arguments",
                );
            };
            if infer.kind != hir::InferArgKind::TypeOrConst {
                return Err(
                    "const-only receiver placeholders need a separate native representation",
                );
            }
            placeholders.push(ReceiverPlaceholder {
                original_hir_id: infer.hir_id,
                span: infer.span,
                syntax_kind: infer.kind,
            });
        }
        explicit_arguments = Some(ReceiverArguments {
            segment: index,
            span: arguments.span_ext,
            placeholders,
        });
    }
    Ok(ReceiverSyntax {
        original_type: receiver,
        path,
        explicit_arguments,
    })
}

/// Inspect the raw lowered owner before any adapter projection. The caller
/// obtains the exact marker from the authenticated compiler-loaded foreign
/// builtin. Its pure declaration-carrier grammar does not depend on enclosing
/// macro spelling or provenance. The unverified observer separately binds the
/// original caller file; this parser grants no executable or reveal semantics.
///
/// None means an ordinary owner, which must be left completely unchanged.
pub(super) fn parse<'tcx>(
    owner: &'tcx hir::OwnerInfo<'tcx>,
    marker_definition: DefId,
) -> Result<Option<ParsedHelper<'tcx>>, Problem> {
    let raw_attributes = owner.attrs.get(hir::ItemLocalId::ZERO);
    let attributes = attrs::verus_attrs(raw_attributes);
    if !attributes
        .iter()
        .any(|(attr, _)| *attr == VerusAttr::RevealFn)
    {
        return Ok(None);
    }
    let OwnerNode::Item(item) = owner.node() else {
        return Err(Problem {
            at: attributes[0].1,
            detail: "a function-identity marker on a non-function owner",
        });
    };
    let problem = |detail| Problem {
        at: item.span,
        detail,
    };
    if raw_attributes.len() != 1
        || attributes.len() != 1
        || attributes[0].0 != VerusAttr::RevealFn
        || owner
            .attrs
            .map
            .iter()
            .any(|(id, _)| *id != hir::ItemLocalId::ZERO)
        || owner.attrs.define_opaque.is_some()
    {
        return Err(problem(
            "unexpected Verus directives on a function-identity helper",
        ));
    }
    let hir::ItemKind::Fn {
        sig,
        generics,
        body: body_id,
        ..
    } = &item.kind
    else {
        return Err(problem("a function-identity marker on a non-function item"));
    };
    if !sig.decl.inputs.is_empty()
        || !generics.params.is_empty()
        || !generics.predicates.is_empty()
        || !matches!(sig.decl.output, hir::FnRetTy::DefaultReturn(_))
        || !sig.header.is_safe()
        || sig.header.is_async()
        || !matches!(sig.header.constness, hir::Constness::NotConst)
        || sig.header.abi != rustc_abi::ExternAbi::Rust
        || sig.decl.c_variadic()
    {
        return Err(problem("a function-identity helper must have no parameters or generics and implicit unit return"));
    }
    if !owner.parenting.is_empty() || !owner.children.is_empty() || owner.nodes.bodies.len() != 1 {
        return Err(problem(
            "nested owners or extra bodies in a function-identity helper",
        ));
    }
    let Some(body) = owner.nodes.bodies.get(&body_id.hir_id.local_id).copied() else {
        return Err(problem("the function-identity helper has no original body"));
    };
    if !body.params.is_empty() || body.contract.is_some() {
        return Err(problem(
            "parameters or native Trust contracts in a function-identity helper body",
        ));
    }
    let hir::ExprKind::Block(block, None) = body.value.kind else {
        return Err(problem(
            "a function-identity helper body must be one plain block",
        ));
    };
    if !block.stmts.is_empty()
        || !matches!(block.rules, hir::BlockCheckMode::DefaultBlock)
        || block.targeted_by_break
    {
        return Err(problem("statements in a function-identity helper body"));
    }
    let Some(call) = block.expr else {
        return Err(problem("no marker call in a function-identity helper body"));
    };
    let hir::ExprKind::Call(callee, arguments) = call.kind else {
        return Err(problem(
            "a function-identity helper tail must be the marker call",
        ));
    };
    let hir::ExprKind::Path(hir::QPath::Resolved(None, path)) = callee.kind else {
        return Err(problem(
            "the identity marker callee must have a resolved native declaration",
        ));
    };
    if path.res != Res::Def(DefKind::Fn, marker_definition)
        || marker_definition.is_local()
        || !path_has_no_arguments(path)
    {
        return Err(problem(
            "the identity marker callee is not the approved foreign builtin definition",
        ));
    }
    let [argument] = arguments else {
        return Err(problem(
            "a function-identity marker requires exactly one path operand",
        ));
    };
    let target = match argument.kind {
        hir::ExprKind::Path(hir::QPath::Resolved(None, path)) => match path.res {
            Res::Def(DefKind::Fn, definition) if path_has_no_arguments(path) => {
                Target::Declaration(definition)
            }
            Res::Def(DefKind::AssocFn, definition) if path_has_no_arguments(path) => {
                Target::AssociatedDeclaration(definition)
            }
            _ => {
                return Err(problem(
                    "the identity operand does not resolve to a function declaration",
                ))
            }
        },
        hir::ExprKind::Path(hir::QPath::Resolved(Some(receiver), path)) => match path.res {
            Res::Def(DefKind::AssocFn, declaration) if path_has_no_arguments(path) => {
                Target::Qualified {
                    declaration,
                    receiver: receiver_syntax(receiver).map_err(problem)?,
                    path,
                }
            }
            _ => {
                return Err(problem(
                    "the qualified identity operand has no associated declaration",
                ))
            }
        },
        hir::ExprKind::Path(hir::QPath::TypeRelative(receiver, member)) => {
            if member.args.is_some() {
                return Err(problem(
                    "explicit associated method arguments need a separate representation",
                ));
            }
            Target::TypeRelative {
                receiver: receiver_syntax(receiver).map_err(problem)?,
                member,
            }
        }
        _ => return Err(problem("computations cannot be function-identity operands")),
    };
    Ok(Some(ParsedHelper {
        target,
        original_body: body,
        original_call: call,
        original_operand: argument,
        marker_definition,
    }))
}
