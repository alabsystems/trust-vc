// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Charged fixed-layout slots and iterative single-level type substitution.
use super::{charge, refusal, R};
use crate::vcgen::val::Ctx;
use crate::{AdtId, AdtKind, Projection, ProjectionId, SpanId, Ty};
use std::cell::Cell;

pub(super) fn price_type(work: &Cell<usize>, ty: &Ty, span: SpanId) -> R<()> {
    let mut pending = vec![ty];
    while let Some(ty) = pending.pop() {
        charge(work, 1, span)?;
        match ty {
            Ty::Tuple(fields) | Ty::Adt(_, fields) | Ty::Projection(_, fields) => {
                charge(work, fields.len(), span)?;
                pending.extend(fields);
            }
            Ty::Ref { inner, .. } | Ty::MutRef(inner) => pending.push(inner),
            _ => {}
        }
    }
    Ok(())
}

#[derive(Clone, Copy)]
struct View<'a> {
    ty: &'a Ty,
    environment: Option<usize>,
    recipe_only: bool,
}

/// Price expanded layout before Ctx::shape allocates it. Environments are
/// arena indices rather than recursively owned frames, so neither this walk
/// nor dropping its worklist consumes input-proportional call-stack depth.
pub(in crate::vcgen) fn price_layout(
    ctx: &Ctx<'_>,
    ty: &Ty,
    work: &Cell<usize>,
    span: SpanId,
) -> R<()> {
    charge(work, 2, span)?;
    let mut environments: Vec<Vec<View<'_>>> = Vec::new();
    let mut pending = vec![View {
        ty,
        environment: None,
        recipe_only: false,
    }];
    while let Some(view) = pending.pop() {
        charge(work, 1, span)?;
        if let Ty::Param(index) = view.ty {
            if let Some(environment) = view.environment {
                let Some(argument) = environments
                    .get(environment)
                    .and_then(|args| args.get(*index as usize))
                else {
                    return Err(refusal(
                        "resolution-type",
                        "invalid layout type substitution",
                        span,
                    ));
                };
                charge(work, 1, span)?;
                pending.push(View {
                    recipe_only: view.recipe_only,
                    ..*argument
                });
            }
            continue;
        }
        match view.ty {
            Ty::Tuple(fields) => {
                charge(work, fields.len(), span)?;
                for field in fields {
                    pending.push(View { ty: field, ..view });
                }
            }
            Ty::Ref { inner, .. } => pending.push(View { ty: inner, ..view }),
            Ty::MutRef(inner) => {
                // References are opaque layout leaves, but their type
                // argument recipes still need complete substituted pricing.
                pending.push(View {
                    ty: inner,
                    recipe_only: true,
                    ..view
                });
            }
            Ty::Projection(_, arguments) => {
                charge(work, arguments.len(), span)?;
                for ty in arguments {
                    pending.push(View { ty, recipe_only: true, ..view });
                }
            }
            Ty::Adt(id, args) => {
                charge(work, 1 + args.len(), span)?;
                let arguments: Vec<_> = args.iter().map(|ty| View { ty, ..view }).collect();
                let environment = environments.len();
                environments.push(arguments);
                let Some(adt) = ctx.adts.get(id) else {
                    return Err(refusal(
                        "resolution-type",
                        "unknown identity layout datatype",
                        span,
                    ));
                };
                if !view.recipe_only && adt.kind == AdtKind::Struct && adt.variants.len() == 1 {
                    charge(work, adt.variants[0].fields.len(), span)?;
                    for field in &adt.variants[0].fields {
                        pending.push(View {
                            ty: &field.ty,
                            environment: Some(environment),
                            recipe_only: false,
                        });
                    }
                } else {
                    charge(work, args.len(), span)?;
                    for argument in &environments[environment] {
                        pending.push(View {
                            recipe_only: true,
                            ..*argument
                        });
                    }
                }
            }
            _ => {}
        }
    }
    Ok(())
}

enum TypeFrame<'a> {
    Visit(&'a Ty, bool),
    Group(Option<AdtId>, usize),
    Projection(ProjectionId, usize),
    Ref(bool),
    MutRef,
}

fn rebuild_type<'a>(
    work: &Cell<usize>,
    ty: &'a Ty,
    args: Option<&'a [Ty]>,
    span: SpanId,
) -> R<Option<Ty>> {
    charge(work, 2, span)?;
    let mut pending = vec![TypeFrame::Visit(ty, args.is_some())];
    let mut values = Vec::new();
    while let Some(frame) = pending.pop() {
        charge(work, 1, span)?;
        match frame {
            TypeFrame::Visit(ty, substitute) => match ty {
                Ty::Param(index) if substitute => {
                    let Some(argument) = args.and_then(|args| args.get(*index as usize)) else {
                        return Ok(None);
                    };
                    // Actual caller parameters are not recursively substituted.
                    pending.push(TypeFrame::Visit(argument, false));
                }
                Ty::Tuple(fields) | Ty::Adt(_, fields) => {
                    charge(work, 1 + fields.len(), span)?;
                    let adt = match ty {
                        Ty::Adt(id, _) => Some(*id),
                        _ => None,
                    };
                    pending.push(TypeFrame::Group(adt, fields.len()));
                    for field in fields.iter().rev() {
                        pending.push(TypeFrame::Visit(field, substitute));
                    }
                }
                Ty::Projection(id, arguments) => {
                    charge(work, 1 + arguments.len(), span)?;
                    pending.push(TypeFrame::Projection(*id, arguments.len()));
                    for argument in arguments.iter().rev() {
                        pending.push(TypeFrame::Visit(argument, substitute));
                    }
                }
                Ty::Ref { mutable, inner } => {
                    charge(work, 2, span)?;
                    pending.push(TypeFrame::Ref(*mutable));
                    pending.push(TypeFrame::Visit(inner, substitute));
                }
                Ty::MutRef(inner) => {
                    charge(work, 2, span)?;
                    pending.push(TypeFrame::MutRef);
                    pending.push(TypeFrame::Visit(inner, substitute));
                }
                Ty::Bool => values.push(Ty::Bool),
                Ty::Int(range) => values.push(Ty::Int(*range)),
                Ty::Unit => values.push(Ty::Unit),
                Ty::Param(index) => values.push(Ty::Param(*index)),
            },
            TypeFrame::Group(adt, count) => {
                charge(work, count, span)?;
                let Some(start) = values.len().checked_sub(count) else {
                    return Err(refusal(
                        "resolution-type",
                        "invalid type reconstruction",
                        span,
                    ));
                };
                let fields = values.split_off(start);
                values.push(match adt {
                    Some(id) => Ty::Adt(id, fields),
                    None => Ty::Tuple(fields),
                });
            }
            TypeFrame::Ref(mutable) => {
                let Some(inner) = values.pop() else {
                    return Err(refusal(
                        "resolution-type",
                        "invalid reference reconstruction",
                        span,
                    ));
                };
                values.push(Ty::Ref {
                    mutable,
                    inner: Box::new(inner),
                });
            }
            TypeFrame::Projection(id, count) => {
                charge(work, count, span)?;
                let Some(start) = values.len().checked_sub(count) else {
                    return Err(refusal("resolution-type", "invalid associated-type reconstruction", span));
                };
                let arguments = values.split_off(start);
                values.push(Ty::Projection(id, arguments));
            }
            TypeFrame::MutRef => {
                let Some(inner) = values.pop() else {
                    return Err(refusal(
                        "resolution-type",
                        "invalid reference reconstruction",
                        span,
                    ));
                };
                values.push(Ty::MutRef(Box::new(inner)));
            }
        }
    }
    if values.len() != 1 {
        return Err(refusal(
            "resolution-type",
            "invalid reconstructed type count",
            span,
        ));
    }
    Ok(values.pop())
}

fn copy_type(work: &Cell<usize>, ty: &Ty, span: SpanId) -> R<Ty> {
    rebuild_type(work, ty, None, span)?
        .ok_or_else(|| refusal("resolution-type", "missing copied type", span))
}

fn substituted(work: &Cell<usize>, ty: &Ty, args: &[Ty], span: SpanId) -> R<Option<Ty>> {
    rebuild_type(work, ty, Some(args), span)
}

pub(in crate::vcgen) fn slot_type(
    ctx: &Ctx<'_>,
    ty: &Ty,
    path: &[Projection],
    work: &Cell<usize>,
    span: SpanId,
) -> R<Option<Ty>> {
    let mut ty = copy_type(work, ty, span)?;
    for projection in path {
        charge(work, 1, span)?;
        ty = match (projection, ty) {
            (Projection::TupleField(index), Ty::Tuple(fields)) => {
                let Some(field) = fields.into_iter().nth(*index as usize) else {
                    return Ok(None);
                };
                field
            }
            (Projection::Field { variant: 0, field }, Ty::Adt(id, args)) => {
                let Some(adt) = ctx.adts.get(&id) else {
                    return Ok(None);
                };
                if adt.kind != AdtKind::Struct || adt.variants.len() != 1 {
                    return Ok(None);
                }
                let Some(field) = adt.variants[0].fields.get(*field as usize) else {
                    return Ok(None);
                };
                let Some(ty) = substituted(work, &field.ty, &args, span)? else {
                    return Ok(None);
                };
                ty
            }
            // A dereferenced input is storage borrowed by the parameter,
            // rather than an owned carrier supplied as that argument value.
            _ => return Ok(None),
        };
    }
    Ok(Some(ty))
}

pub(in crate::vcgen) fn owned_slots(
    ctx: &Ctx<'_>,
    ty: &Ty,
    work: &Cell<usize>,
    span: SpanId,
) -> R<Vec<Vec<Projection>>> {
    let mut pending = vec![(copy_type(work, ty, span)?, Vec::new())];
    let mut slots = Vec::new();
    while let Some((ty, path)) = pending.pop() {
        charge(work, 1 + path.len(), span)?;
        match ty {
            Ty::MutRef(_) => slots.push(path),
            Ty::Tuple(fields) => {
                charge(work, fields.len(), span)?;
                for (index, ty) in fields.into_iter().enumerate().rev() {
                    charge(work, 1 + path.len(), span)?;
                    let mut child = path.clone();
                    child.push(Projection::TupleField(index as u32));
                    pending.push((ty, child));
                }
            }
            Ty::Adt(id, args) => {
                let Some(adt) = ctx.adts.get(&id) else {
                    continue;
                };
                if adt.kind != AdtKind::Struct || adt.variants.len() != 1 {
                    continue;
                }
                charge(work, adt.variants[0].fields.len(), span)?;
                for (index, field) in adt.variants[0].fields.iter().enumerate().rev() {
                    if field.mode == crate::Mode::Spec {
                        continue;
                    }
                    let Some(ty) = substituted(work, &field.ty, &args, span)? else {
                        return Ok(Vec::new());
                    };
                    charge(work, 1 + path.len(), span)?;
                    let mut child = path.clone();
                    child.push(Projection::Field {
                        variant: 0,
                        field: index as u32,
                    });
                    pending.push((ty, child));
                }
            }
            _ => {}
        }
    }
    Ok(slots)
}
