// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Backward resolution and forward typed ownership over one structured CFG.
use super::expr::R;
use super::val::{refusal, Ctx};
use crate::{
    AdtKind, Block, Expr, ExprKind, FnDecl, LocalId, LocalKind, LoopId, Mode, Place, Projection,
    Stmt, StmtKind, Ty,
};

mod call_capture;
mod call_finish;
mod call_sources;
mod call_state;
mod calls;
mod cfg;
mod classifier;
mod flow;
mod initialization;
mod layout;
mod provenance;
mod proxy;
mod state;
mod targets;
mod transfer;
mod types;
mod weak;

use call_finish::CallOutput;
use call_state::{CapturedArgument, CapturedRow, ExtraOrigin, PendingCall, ReturnBinding};
use cfg::{Action, Builder, Event};
pub(super) use classifier::Classifier;
pub(super) use state::{OwnershipState, Plan};

pub(super) fn overlaps(a: &Place, b: &Place) -> bool {
    a.local == b.local
        && a.projections
            .iter()
            .zip(&b.projections)
            .all(|(a, b)| a == b)
}

fn covers(a: &Place, b: &Place) -> bool {
    a.local == b.local
        && b.projections.starts_with(&a.projections)
        && !b.projections[a.projections.len()..].contains(&Projection::Deref)
}

pub(super) fn place_ty(ctx: &Ctx<'_>, decl: &FnDecl, place: &Place) -> Option<Ty> {
    let mut ty = decl.local(place.local)?.ty.clone();
    for projection in &place.projections {
        ty = match (projection, ty) {
            (Projection::Deref, Ty::MutRef(inner) | Ty::Ref { inner, .. }) => *inner,
            (Projection::TupleField(index), Ty::Tuple(fields)) => {
                fields.get(*index as usize)?.clone()
            }
            (Projection::Field { variant, field }, Ty::Adt(id, args)) => ctx
                .adts
                .get(&id)?
                .variants
                .get(*variant as usize)?
                .fields
                .get(*field as usize)?
                .ty
                .subst(&args),
            _ => return None,
        };
    }
    Some(ty)
}

pub(super) fn contains(ty: &Ty) -> bool {
    match ty {
        Ty::MutRef(_) | Ty::Adt(_, _) => true,
        Ty::Tuple(fields) => fields.iter().any(contains),
        Ty::Ref { .. } | Ty::Bool | Ty::Int(_) | Ty::Unit | Ty::Param(_) => false,
    }
}

/// Places transferred by an owned value; projections and predicates only borrow.
pub(super) fn moves(ctx: &Ctx<'_>, expression: &Expr, out: &mut Vec<Place>) {
    match &expression.kind {
        ExprKind::Read(place) if contains(&expression.ty) => out.push(place.clone()),
        ExprKind::Tuple(fields) => {
            for field in fields {
                moves(ctx, field, out);
            }
        }
        ExprKind::Ctor {
            adt,
            variant,
            fields,
            ..
        } => {
            for (index, value) in fields.iter().enumerate() {
                if ctx
                    .adts
                    .get(adt)
                    .and_then(|adt| adt.variants.get(*variant as usize))
                    .and_then(|variant| variant.fields.get(index))
                    .is_some_and(|field| field.mode == Mode::Spec)
                {
                    continue;
                }
                moves(ctx, value, out);
            }
        }
        ExprKind::Field {
            base,
            variant,
            field,
        } if contains(&expression.ty) => {
            if let Ty::Adt(id, _) = &base.ty {
                if ctx
                    .adts
                    .get(id)
                    .and_then(|adt| adt.variants.get(*variant as usize))
                    .and_then(|variant| variant.fields.get(*field as usize))
                    .is_some_and(|field| field.mode == Mode::Spec)
                {
                    return;
                }
            }
            if let ExprKind::Read(place) = &base.kind {
                let mut place = place.clone();
                place.projections.push(Projection::Field {
                    variant: *variant,
                    field: *field,
                });
                out.push(place);
            } else {
                moves(ctx, base, out);
            }
        }
        ExprKind::TupleField { base, index } if contains(&expression.ty) => {
            if let ExprKind::Read(place) = &base.kind {
                let mut place = place.clone();
                place.projections.push(Projection::TupleField(*index));
                out.push(place);
            } else {
                moves(ctx, base, out);
            }
        }
        ExprKind::If {
            then_expr,
            else_expr,
            ..
        } if contains(&expression.ty) => {
            let mut yes = Vec::new();
            let mut no = Vec::new();
            moves(ctx, then_expr, &mut yes);
            moves(ctx, else_expr, &mut no);
            out.extend(yes.iter().cloned());
            out.extend(no.into_iter().filter(|place| !yes.contains(place)));
        }
        ExprKind::Let { value, body, .. } => {
            moves(ctx, value, out);
            moves(ctx, body, out);
        }
        ExprKind::MutRefUpdate { reference, value } => {
            moves(ctx, reference, out);
            moves(ctx, value, out);
        }
        _ => {}
    }
}

pub(super) fn analyze<'a, 'ctx>(
    ctx: &'a Ctx<'ctx>,
    decl: &'a FnDecl,
    block: &'a Block,
    classifier: &'a Classifier<'a, 'ctx>,
) -> R<Plan> {
    classifier.validate(ctx, decl)?;
    let mut owned = false;
    for local in &decl.locals {
        if local.mode != Mode::Spec && classifier.contains(&local.ty, local.span)? {
            owned = true;
            break;
        }
    }
    if !owned {
        return Ok(Plan::default());
    }
    let mut builder = Builder::new(ctx, decl, classifier)?;
    let entry = builder.build(block)?;
    let mut places = Vec::new();
    let mut universe = Vec::new();
    for (index, local) in decl.locals.iter().enumerate() {
        if matches!(
            local.kind,
            LocalKind::Param | LocalKind::Let | LocalKind::Temp
        ) {
            builder.candidates(
                &local.ty,
                Place::local(LocalId(index as u32)),
                &mut universe,
                &mut places,
                0,
            )?;
        }
    }
    builder.index_initialization(&universe)?;
    let before = builder.backward(&places)?;
    let states = builder.forward(entry, &universe, &places, &before)?;
    let mut plan = Plan::new(builder.work.clone(), places);
    for (index, node) in builder.nodes.iter().enumerate() {
        if let Some(statement) = node.statement {
            let points = builder.resolution_points(&plan.places, &before[index])?;
            plan.before.insert(statement, points);
        }
    }
    for (id, index) in &builder.loops {
        let points = builder.selected(&plan.places, &before[*index], states[*index].as_ref())?;
        plan.loops.insert(*id, points);
        if let Some(state) = &states[*index] {
            plan.heads
                .insert(*id, state.copy(&builder.work, decl.span)?);
        }
    }
    for (id, index) in &builder.exits {
        if let Some(state) = &states[*index] {
            plan.exits
                .insert(*id, state.copy(&builder.work, decl.span)?);
        }
    }
    for (statement, index) in &builder.tails {
        let points = builder.resolution_points(&plan.places, &before[*index])?;
        plan.before_tail.insert(*statement, points);
    }
    for (statement, index) in &builder.after {
        if let Some(state) = &states[*index] {
            plan.after
                .insert(*statement, state.copy(&builder.work, decl.span)?);
        }
    }
    for (block, index) in &builder.block_ends {
        let points = builder.resolution_points(&plan.places, &before[*index])?;
        plan.record_block(*block, points);
    }
    Ok(plan)
}
