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
mod values;
mod weak;

use call_finish::CallOutput;
use call_state::{CapturedArgument, CapturedRow, ExtraOrigin, PendingCall, ReturnBinding};
use cfg::{Action, Builder, Event};
pub(super) use classifier::Classifier;
pub(super) use state::{OwnershipState, Plan};
pub(super) use values::ValueTarget;

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

pub(super) fn place_ty(
    ctx: &Ctx<'_>, decl: &FnDecl, place: &Place, work: &std::cell::Cell<usize>, span: crate::SpanId,
) -> R<Option<Ty>> {
    let Some(local) = decl.local(place.local) else { return Ok(None); };
    let mut ty = if ctx.source.projections.is_empty() { local.ty.clone() }
        else { ctx.normalize_type(&local.ty, work, span)? };
    for projection in &place.projections {
        if !ctx.source.projections.is_empty() { super::inline_work::items(work, 1, span)?; }
        ty = match (projection, ty) {
            (Projection::Deref, Ty::MutRef(inner) | Ty::Ref { inner, .. }) => *inner,
            (Projection::TupleField(index), Ty::Tuple(mut fields)) => {
                if *index as usize >= fields.len() { return Ok(None); }
                fields.swap_remove(*index as usize)
            }
            (Projection::Field { variant, field }, Ty::Adt(id, args)) => {
                let Some(field) = ctx.adts.get(&id)
                    .filter(|decl| decl.kind != AdtKind::Opaque && decl.type_params.len() == args.len())
                    .and_then(|decl| decl.variants.get(*variant as usize))
                    .and_then(|variant| variant.fields.get(*field as usize))
                    else { return Ok(None); };
                ctx.substitute_type(&field.ty, &args, work, span)?
            }
            _ => return Ok(None),
        };
    }
    Ok(Some(ty))
}

pub(super) fn contains(ty: &Ty) -> bool {
    match ty {
        Ty::MutRef(_) | Ty::Adt(_, _) => true,
        Ty::Tuple(fields) => fields.iter().any(contains),
        Ty::Ref { .. } | Ty::Bool | Ty::Int(_) | Ty::Unit | Ty::Param(_) | Ty::Projection(..) => false,
    }
}

/// Places transferred by an owned value; projections and predicates only borrow.
pub(super) fn moves(ctx: &Ctx<'_>, expression: &Expr, out: &mut Vec<Place>) {
    value_moves(ctx, expression, out, false);
}

fn resolution_moves(ctx: &Ctx<'_>, expression: &Expr, out: &mut Vec<Place>) {
    value_moves(ctx, expression, out, true);
}

fn value_moves(ctx: &Ctx<'_>, expression: &Expr, out: &mut Vec<Place>, abstract_values: bool) {
    fn projected_place(expression: &Expr) -> Option<Place> {
        match &expression.kind {
            ExprKind::Read(place) => Some(place.clone()),
            ExprKind::Field {
                base,
                variant,
                field,
            } => {
                let mut place = projected_place(base)?;
                place.projections.push(Projection::Field {
                    variant: *variant,
                    field: *field,
                });
                Some(place)
            }
            ExprKind::TupleField { base, index } => {
                let mut place = projected_place(base)?;
                place.projections.push(Projection::TupleField(*index));
                Some(place)
            }
            _ => None,
        }
    }
    fn relevant(ty: &Ty, abstract_values: bool) -> bool {
        match ty {
            Ty::Param(_) | Ty::Projection(..) => abstract_values,
            Ty::Tuple(fields) => fields.iter().any(|ty| relevant(ty, abstract_values)),
            _ => contains(ty),
        }
    }
    match &expression.kind {
        ExprKind::Read(place) if relevant(&expression.ty, abstract_values) => {
            out.push(place.clone())
        }
        ExprKind::Tuple(fields) => {
            for field in fields {
                value_moves(ctx, field, out, abstract_values);
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
                value_moves(ctx, value, out, abstract_values);
            }
        }
        ExprKind::Field {
            base,
            variant,
            field,
        } if relevant(&expression.ty, abstract_values) => {
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
            if abstract_values {
                if let Some(place) = projected_place(expression) {
                    out.push(place);
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
                value_moves(ctx, base, out, abstract_values);
            }
        }
        ExprKind::TupleField { base, index } if relevant(&expression.ty, abstract_values) => {
            if abstract_values {
                if let Some(place) = projected_place(expression) {
                    out.push(place);
                    return;
                }
            }
            if let ExprKind::Read(place) = &base.kind {
                let mut place = place.clone();
                place.projections.push(Projection::TupleField(*index));
                out.push(place);
            } else {
                value_moves(ctx, base, out, abstract_values);
            }
        }
        ExprKind::If {
            then_expr,
            else_expr,
            ..
        } if relevant(&expression.ty, abstract_values) => {
            let mut yes = Vec::new();
            let mut no = Vec::new();
            value_moves(ctx, then_expr, &mut yes, abstract_values);
            value_moves(ctx, else_expr, &mut no, abstract_values);
            out.extend(yes.iter().cloned());
            out.extend(no.into_iter().filter(|place| !yes.contains(place)));
        }
        ExprKind::Let { value, body, .. } => {
            value_moves(ctx, value, out, abstract_values);
            value_moves(ctx, body, out, abstract_values);
        }
        ExprKind::MutRefUpdate { reference, value } => {
            value_moves(ctx, reference, out, abstract_values);
            value_moves(ctx, value, out, abstract_values);
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
        if local.mode != Mode::Spec
            && (classifier.contains(&local.ty, local.span)?
                || classifier.contains_abstract(&local.ty, local.span)?)
        {
            owned = true;
            break;
        }
    }
    if !owned {
        // A Copy-only consumer can read `*shared` straight into a call while
        // having no abstract local or result storage. Keep the classifier's
        // SAME already-debited ledger for that typed origin check; no CFG,
        // resolution target, loan or replacement grant is created here.
        if !decl.copy_premises.is_empty() {
            return Ok(Plan::new(classifier.work(), Vec::new()));
        }
        return Ok(Plan::default());
    }
    let mut builder = Builder::new(ctx, decl, classifier)?;
    let entry = builder.build(block)?;
    let mut places = Vec::new();
    let mut universe = Vec::new();
    let mut values = Vec::new();
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
            if local.mode != Mode::Spec {
                builder.abstract_candidates(
                    &local.ty,
                    Place::local(LocalId(index as u32)),
                    &[],
                    &mut universe,
                    &mut values,
                    0,
                )?;
            }
        }
    }
    builder.index_initialization(&universe)?;
    let before = builder.backward(&places)?;
    let states = builder.forward(entry, &universe, &places, &before)?;
    let value_places = builder.value_places(&values)?;
    let value_before = builder.backward(&value_places)?;
    let mut plan = Plan::new(builder.work.clone(), places);
    plan.value_targets = values;
    for (index, node) in builder.nodes.iter().enumerate() {
        if let Some(statement) = node.statement {
            let mut points = builder.resolution_points(&plan.places, &before[index])?;
            points.extend(builder.selected(
                &value_places,
                &value_before[index],
                states[index].as_ref(),
            )?);
            plan.before.insert(statement, points);
        }
    }
    for (id, index) in &builder.loops {
        let mut points =
            builder.selected(&plan.places, &before[*index], states[*index].as_ref())?;
        points.extend(builder.selected(
            &value_places,
            &value_before[*index],
            states[*index].as_ref(),
        )?);
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
        let mut points = builder.resolution_points(&plan.places, &before[*index])?;
        points.extend(builder.selected(
            &value_places,
            &value_before[*index],
            states[*index].as_ref(),
        )?);
        plan.before_tail.insert(*statement, points);
    }
    for (statement, index) in &builder.after {
        if let Some(state) = &states[*index] {
            plan.after
                .insert(*statement, state.copy(&builder.work, decl.span)?);
        }
    }
    for (block, index) in &builder.block_ends {
        let mut points = builder.resolution_points(&plan.places, &before[*index])?;
        points.extend(builder.selected(
            &value_places,
            &value_before[*index],
            states[*index].as_ref(),
        )?);
        plan.record_block(*block, points);
    }
    Ok(plan)
}
