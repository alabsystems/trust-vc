// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

impl Walk<'_, '_> {
    pub(super) fn expression(&mut self, expr: &Expr, expected: Mode) -> Mode {
        match &expr.kind {
            ExprKind::Lit(_) | ExprKind::IntegerConstant(_) => Mode::Exec,
            ExprKind::Read(place) => {
                if let Some(mode) = self.read_origin(place) {
                    return mode;
                }
                let Some(access) = place_mode(self.decl, &self.index.adts, place) else {
                    return Mode::Spec;
                };
                if expected == Mode::Exec
                    && self.ambient == Mode::Exec
                    && !access.exec_accessible
                    && (access.mode == Mode::Exec || expr.ty == Ty::Unit)
                {
                    self.error(expr.span, Mode::Proof, Mode::Exec);
                }
                join(access.mode, expected)
            }
            ExprKind::Old(_) => Mode::Spec,
            ExprKind::Field {
                base,
                variant,
                field,
            } => {
                let base_mode = self.expression(base, expected);
                let mut ty = &base.ty;
                while let Ty::Ref {
                    mutable: false,
                    inner,
                } = ty
                {
                    ty = inner;
                }
                let field_mode = match ty {
                    Ty::Adt(id, _) => self
                        .index
                        .adts
                        .get(id)
                        .and_then(|adt| adt.variants.get(*variant as usize))
                        .and_then(|variant| variant.fields.get(*field as usize))
                        .map(|field| field.mode),
                    _ => None,
                };
                join(base_mode, field_mode.unwrap_or(Mode::Spec))
            }
            ExprKind::TupleField { base, .. }
            | ExprKind::Borrow(base)
            | ExprKind::Cast { arg: base, .. }
            | ExprKind::Unary { arg: base, .. } => self.expression(base, expected),
            ExprKind::Binary { lhs, rhs, .. } => {
                let a = self.expression(lhs, expected);
                let b = self.expression(rhs, expected);
                join(a, b)
            }
            ExprKind::If {
                cond,
                then_expr,
                else_expr,
            } => {
                self.value_has_mode(
                    cond,
                    if self.ambient == Mode::Exec && expected == Mode::Exec {
                        Mode::Exec
                    } else {
                        Mode::Spec
                    },
                );
                let before = self.origins.clone();
                let a = self.expression(then_expr, expected);
                let yes = self.origins.clone();
                self.origins = before;
                let b = self.expression(else_expr, expected);
                let no = self.origins.clone();
                self.merge(&yes, &no);
                join(a, b)
            }
            ExprKind::Let { local, value, body } => {
                let mode = self
                    .decl
                    .local(*local)
                    .map_or(Mode::Spec, |local| local.mode);
                self.value_has_mode(value, mode);
                self.expression(body, expected)
            }
            ExprKind::Call { callee, args, .. } => {
                let Some(target) = self.index.fns.get(callee).copied() else {
                    return Mode::Spec;
                };
                self.arguments(target, args);
                target.local(target.ret).map_or(Mode::Spec, |ret| ret.mode)
            }
            ExprKind::Ctor {
                adt,
                variant,
                fields,
            } => {
                let Some(declaration) = self
                    .index
                    .adts
                    .get(adt)
                    .copied()
                    .and_then(|adt| adt.variants.get(*variant as usize))
                else {
                    return Mode::Spec;
                };
                let mut mode = Mode::Exec;
                for (value, field) in fields.iter().zip(&declaration.fields) {
                    let actual = self.expression(value, join(expected, field.mode));
                    if !allows(actual, field.mode) {
                        mode = join(mode, actual);
                    }
                }
                mode
            }
            ExprKind::Tuple(fields) => fields.iter().fold(Mode::Exec, |mode, field| {
                join(mode, self.expression(field, expected))
            }),
            ExprKind::IsVariant { base, .. } => self.expression(base, expected),
            ExprKind::MutRefCurrent(value)
            | ExprKind::MutRefFuture(value)
            | ExprKind::HasResolved(value) => {
                self.value_has_mode(value, Mode::Spec);
                Mode::Spec
            }
            ExprKind::MutRefUpdate { reference, value } => {
                self.value_has_mode(reference, Mode::Spec);
                self.value_has_mode(value, Mode::Spec);
                Mode::Spec
            }
            ExprKind::ProofInSpec(block) | ExprKind::ProofInSpecTail { block, .. } => {
                let ambient = self.ambient;
                self.ambient = Mode::Proof;
                let bindings = self.statements(block);
                let mode = match &expr.kind {
                    ExprKind::ProofInSpecTail { tail, .. } => self.expression(tail, Mode::Spec),
                    _ => Mode::Proof,
                };
                for (local, saved) in bindings.into_iter().rev() {
                    self.origins[local] = saved;
                }
                self.ambient = ambient;
                mode
            }
            ExprKind::Quant { .. }
            | ExprKind::Choose { .. }
            | ExprKind::UntriggeredQuant { .. }
            | ExprKind::UntriggeredChoose { .. } => {
                expr.for_each_child(&mut |child| {
                    self.value_has_mode(child, Mode::Spec);
                });
                Mode::Spec
            }
        }
    }
}
