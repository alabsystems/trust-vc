// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Typed ownership identities licensed by ordinary, unlabelled postconditions.
//! This is derived data, not a producer permission or a new logical assumption.
use super::expr::R;
use super::val::{refusal, Ctx};
use crate::{
    BinOp, Expr, ExprKind, FnDecl, LocalId, LocalKind, Mode, Place, Projection, SpanId, Ty,
};
use std::cell::Cell;
use std::collections::{HashMap, HashSet};

mod types;
pub(super) use types::price_layout;
use types::price_type;
pub(super) use types::{owned_slots, slot_type};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct IdentityBinding {
    pub(super) result: Vec<Projection>,
    pub(super) parameter: usize,
    pub(super) argument: Vec<Projection>,
}

#[derive(Debug, Clone, Default)]
pub(super) struct IdentitySummary {
    pub(super) bindings: Vec<IdentityBinding>,
}

#[derive(Clone, Copy)]
enum Root {
    Result,
    Parameter(usize),
}

#[derive(Clone)]
struct Endpoint {
    root: Root,
    path: Vec<Projection>,
}

fn charge(work: &Cell<usize>, amount: usize, span: SpanId) -> R<()> {
    let remaining = work
        .get()
        .checked_sub(amount)
        .ok_or_else(|| refusal("resolution-size", "call identity work exhausted", span))?;
    work.set(remaining);
    Ok(())
}

struct Extract<'a, 'k> {
    target: &'a FnDecl,
    ctx: &'a Ctx<'k>,
    work: &'a Cell<usize>,
    span: SpanId,
    parameters: HashMap<LocalId, usize>,
}

impl Extract<'_, '_> {
    fn endpoint(
        &self,
        expression: &Expr,
        aliases: &HashMap<LocalId, Endpoint>,
    ) -> R<Option<Endpoint>> {
        let mut expression = expression;
        let mut suffix = Vec::new();
        loop {
            charge(self.work, 1, self.span)?;
            match &expression.kind {
                ExprKind::TupleField { base, index } => {
                    suffix.push(Projection::TupleField(*index));
                    expression = base;
                }
                ExprKind::Field {
                    base,
                    variant,
                    field,
                } => {
                    suffix.push(Projection::Field {
                        variant: *variant,
                        field: *field,
                    });
                    expression = base;
                }
                ExprKind::Read(place) | ExprKind::Old(place) => {
                    let root = if place.local == self.target.ret {
                        if matches!(expression.kind, ExprKind::Old(_)) {
                            return Ok(None);
                        }
                        Some(Root::Result)
                    } else {
                        self.parameters
                            .get(&place.local)
                            .copied()
                            .map(Root::Parameter)
                    };
                    let mut endpoint = if let Some(root) = root {
                        charge(self.work, place.projections.len(), self.span)?;
                        Endpoint {
                            root,
                            path: place.projections.clone(),
                        }
                    } else if matches!(expression.kind, ExprKind::Read(_)) {
                        let Some(alias) = aliases.get(&place.local) else {
                            return Ok(None);
                        };
                        charge(
                            self.work,
                            alias.path.len() + place.projections.len(),
                            self.span,
                        )?;
                        let mut alias = alias.clone();
                        alias.path.extend_from_slice(&place.projections);
                        alias
                    } else {
                        return Ok(None);
                    };
                    charge(self.work, suffix.len(), self.span)?;
                    endpoint.path.extend(suffix.into_iter().rev());
                    return Ok(Some(endpoint));
                }
                _ => return Ok(None),
            }
        }
    }

    fn ty(&self, endpoint: &Endpoint) -> R<Option<Ty>> {
        let local = match endpoint.root {
            Root::Result => self.target.ret,
            Root::Parameter(index) => self.target.params[index],
        };
        let Some(local) = self.target.local(local) else {
            return Ok(None);
        };
        price_layout(self.ctx, &local.ty, self.work, self.span)?;
        charge(self.work, 1 + endpoint.path.len(), self.span)?;
        let place = Place {
            local: match endpoint.root {
                Root::Result => self.target.ret,
                Root::Parameter(index) => self.target.params[index],
            },
            projections: endpoint.path.clone(),
        };
        let Some(mode) = crate::place_mode::place_mode(self.target, &self.ctx.adts, &place) else {
            return Ok(None);
        };
        if mode.mode == Mode::Spec || mode.through_spec_mut_ref {
            return Ok(None);
        }
        slot_type(self.ctx, &local.ty, &endpoint.path, self.work, self.span)
    }

    fn relation(
        &self,
        lhs: &Expr,
        rhs: &Expr,
        aliases: &HashMap<LocalId, Endpoint>,
    ) -> R<Vec<IdentityBinding>> {
        let Some(left) = self.endpoint(lhs, aliases)? else {
            return Ok(Vec::new());
        };
        let Some(right) = self.endpoint(rhs, aliases)? else {
            return Ok(Vec::new());
        };
        let Some(left_ty) = self.ty(&left)? else {
            return Ok(Vec::new());
        };
        let Some(right_ty) = self.ty(&right)? else {
            return Ok(Vec::new());
        };
        price_type(self.work, &left_ty, self.span)?;
        price_type(self.work, &right_ty, self.span)?;
        price_type(self.work, &lhs.ty, self.span)?;
        price_type(self.work, &rhs.ty, self.span)?;
        if left_ty != right_ty || lhs.ty != left_ty || rhs.ty != right_ty {
            return Ok(Vec::new());
        }
        let (result, parameter, argument) = match (left.root, right.root) {
            (Root::Result, Root::Parameter(index)) => (left.path, index, right.path),
            (Root::Parameter(index), Root::Result) => (right.path, index, left.path),
            _ => return Ok(Vec::new()),
        };
        let mut bindings = Vec::new();
        for slot in owned_slots(self.ctx, &left_ty, self.work, self.span)? {
            charge(
                self.work,
                result.len() + argument.len() + slot.len() * 2 + 1,
                self.span,
            )?;
            let mut output = result.clone();
            output.extend_from_slice(&slot);
            let mut input = argument.clone();
            input.extend(slot);
            bindings.push(IdentityBinding {
                result: output,
                parameter,
                argument: input,
            });
        }
        Ok(bindings)
    }

    fn aliases_copy(&self, aliases: &HashMap<LocalId, Endpoint>) -> R<HashMap<LocalId, Endpoint>> {
        charge(self.work, aliases.len(), self.span)?;
        for alias in aliases.values() {
            charge(self.work, 1 + alias.path.len(), self.span)?;
        }
        Ok(aliases.clone())
    }
}

fn derive_declaration(
    target: &FnDecl,
    ctx: &Ctx<'_>,
    work: &Cell<usize>,
    span: SpanId,
) -> R<IdentitySummary> {
    let Some(result) = target.local(target.ret) else {
        return Ok(IdentitySummary::default());
    };
    if target.mode == Mode::Spec || result.mode == Mode::Spec {
        return Ok(IdentitySummary::default());
    }
    // Reuse the existing signature/layout admission, not a new copy-depth cap.
    price_layout(ctx, &result.ty, work, span)?;
    ctx.shape_with_work(&result.ty, Some(target.id), span, work)?;
    if owned_slots(ctx, &result.ty, work, span)?.is_empty() {
        return Ok(IdentitySummary::default());
    }
    charge(work, target.params.len(), span)?;
    let mut parameters = HashMap::new();
    for (index, id) in target.params.iter().enumerate() {
        if let Some(local) = target.local(*id).filter(|local| local.mode != Mode::Spec) {
            price_layout(ctx, &local.ty, work, span)?;
            ctx.shape_with_work(&local.ty, Some(target.id), span, work)?;
            parameters.insert(*id, index);
        }
    }
    let extract = Extract {
        target,
        ctx,
        work,
        span,
        parameters,
    };
    let mut bindings = Vec::new();
    for clause in target
        .ensures
        .iter()
        .filter(|clause| !clause.attrs.is_labelled())
    {
        let mut pending = vec![(&clause.expr, HashMap::new())];
        while let Some((expression, aliases)) = pending.pop() {
            charge(work, 1, span)?;
            match &expression.kind {
                ExprKind::Binary {
                    op: BinOp::And,
                    lhs,
                    rhs,
                    check: None,
                } => {
                    pending.push((rhs.as_ref(), extract.aliases_copy(&aliases)?));
                    pending.push((lhs.as_ref(), aliases));
                }
                ExprKind::Binary {
                    op: BinOp::Eq,
                    lhs,
                    rhs,
                    check: None,
                } => {
                    let found = extract.relation(lhs, rhs, &aliases)?;
                    charge(work, found.len(), span)?;
                    bindings.extend(found);
                }
                ExprKind::Let { local, value, body } => {
                    let mut aliases = aliases;
                    let declared = target.local(*local);
                    if declared.is_some_and(|local| {
                        local.kind == LocalKind::Bound && local.mode == Mode::Spec
                    }) {
                        match extract.endpoint(value, &aliases)? {
                            Some(endpoint) => {
                                charge(work, 1, span)?;
                                aliases.insert(*local, endpoint);
                            }
                            None => {
                                aliases.remove(local);
                            }
                        }
                        pending.push((body.as_ref(), aliases));
                    }
                }
                _ => {}
            }
        }
    }
    // A consumed capability cannot be duplicated into two owned output slots.
    // Ambiguous output equations likewise carry no additional authority.
    let mut rejected = HashSet::new();
    for (index, binding) in bindings.iter().enumerate() {
        for (other_index, other) in bindings[..index].iter().enumerate() {
            charge(
                work,
                1 + binding.result.len()
                    + binding.argument.len()
                    + other.result.len()
                    + other.argument.len(),
                span,
            )?;
            let same_input =
                binding.parameter == other.parameter && binding.argument == other.argument;
            let same_output = binding.result == other.result;
            if same_input || same_output {
                if same_input && same_output {
                    rejected.insert(index);
                } else {
                    rejected.insert(index);
                    rejected.insert(other_index);
                }
            }
        }
    }
    charge(work, bindings.len(), span)?;
    let bindings = bindings
        .into_iter()
        .enumerate()
        .filter_map(|(index, binding)| (!rejected.contains(&index)).then_some(binding))
        .collect();
    Ok(IdentitySummary { bindings })
}

pub(super) fn derive(
    target: &FnDecl,
    ctx: &Ctx<'_>,
    work: &Cell<usize>,
    span: SpanId,
) -> R<IdentitySummary> {
    let actual = derive_declaration(target, ctx, work, span)?;
    let Some(origin) = &target.attrs.instance else {
        return Ok(actual);
    };
    let Some(original) = ctx.fns.get(&origin.declaration) else {
        return Ok(IdentitySummary::default());
    };
    if target.role != crate::FnRole::Instance
        || original.role != crate::FnRole::Item
        || original.attrs.instance.is_some()
    {
        return Ok(IdentitySummary::default());
    }
    // Instantiating an unknown T with a reference supplies no generic Copy/
    // Move authority. Retain only identities already licensed for known owned
    // slots by the original contract, using parameter ordinals rather than IDs.
    let declared = derive_declaration(original, ctx, work, span)?;
    let mut bindings = Vec::new();
    for binding in actual.bindings {
        let mut present = false;
        for candidate in &declared.bindings {
            charge(
                work,
                1 + binding.result.len()
                    + binding.argument.len()
                    + candidate.result.len()
                    + candidate.argument.len(),
                span,
            )?;
            present |= *candidate == binding;
        }
        if present {
            bindings.push(binding);
        }
    }
    Ok(IdentitySummary { bindings })
}
