// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Known affine content, not Copy or borrow-check authority. Nominal depth is
//! iterative; structural type-copy and materialized-layout bounds stay intact.
use super::*;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

enum Frame {
    Visit(Ty),
    Done(Ty, Vec<Ty>),
}

pub(in crate::vcgen) struct Classifier<'a, 'ctx> {
    ctx: &'a Ctx<'ctx>,
    decl: &'a FnDecl,
    work: state::Work,
    memo: RefCell<HashMap<Ty, bool>>,
    abstract_memo: RefCell<HashMap<Ty, bool>>,
}

impl<'a, 'ctx> Classifier<'a, 'ctx> {
    pub(in crate::vcgen) fn new(ctx: &'a Ctx<'ctx>, decl: &'a FnDecl) -> Self {
        Self {
            ctx,
            decl,
            work: state::Work::new(),
            memo: RefCell::new(HashMap::new()),
            abstract_memo: RefCell::new(HashMap::new()),
        }
    }

    pub(super) fn validate(&self, ctx: &Ctx<'_>, decl: &FnDecl) -> R<()> {
        if !std::ptr::eq(self.ctx, ctx) || !std::ptr::eq(self.decl, decl) {
            return Err(refusal(
                "resolution-type",
                "ownership classification belongs to another body or context",
                decl.span,
            ));
        }
        Ok(())
    }

    pub(super) fn work(&self) -> state::Work {
        self.work.clone()
    }

    /// Each subsequent hash/equality walk or payload copy is priced before
    /// performing it. Work::ty retains its original structural-depth limit.
    fn price(&self, ty: &Ty, operations: usize, span: crate::SpanId) -> R<()> {
        let before = self.work.remaining().get();
        self.work.ty(ty, span, 0)?;
        let size = before - self.work.remaining().get();
        self.work.charge(size.saturating_mul(operations), span)
    }

    fn copied(&self, ty: &Ty, span: crate::SpanId) -> R<Ty> {
        self.price(ty, 1, span)?;
        Ok(ty.clone())
    }

    fn substituted(&self, ty: &Ty, args: &[Ty], span: crate::SpanId) -> R<Ty> {
        let before = self.work.remaining().get();
        self.work.ty(ty, span, 0)?;
        for argument in args {
            self.work.ty(argument, span, 0)?;
        }
        let size = before - self.work.remaining().get();
        self.work.charge(size.saturating_mul(size), span)?;
        if ty.has_projection() || args.iter().any(Ty::has_projection) {
            self.ctx.substitute_type(ty, args, self.work.remaining(), span)
        } else { Ok(ty.subst(args)) }
    }

    fn children(&self, ty: &Ty, span: crate::SpanId, abstract_values: bool) -> R<Option<Vec<Ty>>> {
        match ty {
            Ty::MutRef(_) if !abstract_values => Ok(None),
            Ty::Param(_) | Ty::Projection(..) if abstract_values => Ok(None),
            Ty::Tuple(fields) => {
                self.work.charge(fields.len(), span)?;
                let mut children = Vec::new();
                for field in fields {
                    children.push(self.copied(field, span)?);
                }
                Ok(Some(children))
            }
            Ty::Adt(id, args) => {
                self.work.charge(1, span)?;
                let adt = self.ctx.adts.get(id).ok_or_else(|| {
                    refusal("resolution-type", "unknown ownership datatype", span)
                })?;
                if args.len() != adt.type_params.len() {
                    return Err(refusal(
                        "resolution-type",
                        "ownership datatype arguments disagree",
                        span,
                    ));
                }
                let mut children = Vec::new();
                for variant in &adt.variants {
                    self.work.charge(1, span)?;
                    for field in &variant.fields {
                        self.work.charge(1, span)?;
                        if field.mode != Mode::Spec {
                            let child = self.substituted(&field.ty, args, span)?;
                            self.work.charge(1, span)?;
                            children.push(child);
                        }
                    }
                }
                Ok(Some(children))
            }
            // A shared/legacy carrier or bare type parameter is not a known
            // locally-owned opaque mutable reference. This is no Copy claim.
            Ty::Ref { .. } | Ty::MutRef(_) | Ty::Param(_) | Ty::Projection(..) | Ty::Unit | Ty::Bool | Ty::Int(_) => {
                Ok(Some(Vec::new()))
            }
        }
    }

    pub(in crate::vcgen) fn contains(&self, ty: &Ty, span: crate::SpanId) -> R<bool> {
        self.classify(ty, span, false)
    }

    /// Abstract owned values need resolution analysis without acquiring a
    /// concrete loan identity, a Copy classification, or pointee ownership.
    pub(in crate::vcgen) fn contains_abstract(&self, ty: &Ty, span: crate::SpanId) -> R<bool> {
        self.classify(ty, span, true)
    }

    fn classify(&self, ty: &Ty, span: crate::SpanId, abstract_values: bool) -> R<bool> {
        let normalized = if ty.has_projection() {
            Some(self.ctx.normalize_type(ty, self.work.remaining(), span)?)
        } else { None };
        let ty = normalized.as_ref().unwrap_or(ty);
        let mut memo = if abstract_values {
            self.abstract_memo.borrow_mut()
        } else {
            self.memo.borrow_mut()
        };
        self.work.charge(1, span)?;
        let mut pending = vec![Frame::Visit(self.copied(ty, span)?)];
        let mut active = HashSet::new();
        while !pending.is_empty() {
            self.work.charge(1, span)?;
            let Some(frame) = pending.pop() else {
                return Err(refusal(
                    "resolution-type",
                    "missing ownership traversal frame",
                    span,
                ));
            };
            match frame {
                Frame::Visit(key) => {
                    self.price(&key, 2, span)?;
                    if memo.contains_key(&key) {
                        continue;
                    }
                    self.price(&key, 2, span)?;
                    if active.contains(&key) {
                        return Err(refusal(
                            "resolution-type",
                            "cyclic ownership datatype",
                            span,
                        ));
                    }
                    let Some(children) = self.children(&key, span, abstract_values)? else {
                        self.price(&key, 2, span)?;
                        memo.insert(key, true);
                        continue;
                    };
                    if children.is_empty() {
                        self.price(&key, 2, span)?;
                        memo.insert(key, false);
                        continue;
                    }
                    let active_key = self.copied(&key, span)?;
                    self.price(&key, 2, span)?;
                    active.insert(active_key);
                    let mut visits = Vec::new();
                    for child in children.iter().rev() {
                        let child = self.copied(child, span)?;
                        self.work.charge(1, span)?;
                        visits.push(Frame::Visit(child));
                    }
                    self.work.charge(1 + visits.len(), span)?;
                    pending.push(Frame::Done(key, children));
                    pending.extend(visits);
                }
                Frame::Done(key, children) => {
                    let mut owned = false;
                    for child in &children {
                        self.price(child, 2, span)?;
                        let child = memo.get(child).copied().ok_or_else(|| {
                            refusal("resolution-type", "unfinished ownership child", span)
                        })?;
                        owned |= child;
                    }
                    self.price(&key, 2, span)?;
                    active.remove(&key);
                    self.price(&key, 2, span)?;
                    memo.insert(key, owned);
                }
            }
        }
        self.price(ty, 2, span)?;
        memo.get(ty)
            .copied()
            .ok_or_else(|| refusal("resolution-type", "missing ownership result", span))
    }
}

#[cfg(test)]
mod tests;
