//! Native fieldless enum discriminants with one evaluation of the source.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use super::*;

impl<'a, 'tcx> FnReader<'a, 'tcx> {
    pub(super) fn scalar_cast(
        &mut self,
        source: &'tcx hir::Expr<'tcx>,
        value: Expr,
        target: Ty,
        context: Ctx,
        span: Span,
    ) -> R<Expr> {
        let ty::Adt(adt, arguments) = self.expr_rty(source).kind() else {
            return self.int_cast(value, target, span);
        };
        if !adt.is_enum() || !target.int_range().is_some_and(|r| r != IntRange::Char) {
            return self.int_cast(value, target, span);
        }
        let Some(identity) = self.cx.adt_id(adt.did()) else {
            return refuse(
                "enum-cast",
                "an enum without its checked local declaration",
                span,
            );
        };
        if !adt.did().is_local()
            || self.cx.imported_nominal(adt.did()).is_some()
            || self.cx.source_opaque_nominal(adt.did())
            || !arguments.is_empty()
            || value.ty != Ty::Adt(identity, Vec::new())
        {
            return refuse(
                "enum-cast",
                "an enum cast without local representation authority",
                span,
            );
        }
        self.check_datatype_access(*adt, span, "enum cast");
        if adt
            .variants()
            .iter()
            .any(|variant| !variant.fields.is_empty())
        {
            return Err(FnProblem::Rejected(UserError::new(
                Phase::RustToVir,
                span,
                "Enum variant should not contain any fields.",
            )));
        }
        if adt.variants().is_empty() {
            return Err(FnProblem::Rejected(UserError::new(
                Phase::RustToVir,
                span,
                "Zero-sized empty Enum expr",
            )));
        }
        let at = self.sp(span);
        let mode = self.operand_mode(&value, context);
        let mut declaration = self.local_decl(
            "enum_cast",
            value.ty.clone(),
            mode,
            false,
            LocalKind::Bound,
            span,
        );
        if mode == Mode::Spec {
            declaration.prophecy = DeclProphecy::DelayedInfer;
        }
        let local = self.add_local(declaration, true);
        // A40 uses rustc's actual Discr.val, including explicit gaps, rather
        // than the variant ordinal. Build mathematical literals before the
        // unchanged ordinary destination clip.
        let mut result = None;
        for (index, _) in adt.variants().iter_enumerated().rev() {
            let literal = Expr::new(
                Ty::Int(IntRange::Int),
                at,
                ExprKind::Lit(Lit::Int(IntLit {
                    negative: false,
                    magnitude: adt.discriminant_for_variant(self.tcx, index).val,
                })),
            );
            result = Some(match result {
                None => literal,
                Some(otherwise) => Expr::new(
                    Ty::Int(IntRange::Int),
                    at,
                    ExprKind::If {
                        cond: Box::new(Expr::new(
                            Ty::Bool,
                            at,
                            ExprKind::IsVariant {
                                base: Box::new(self.read_local(local, span)),
                                variant: index.as_u32(),
                            },
                        )),
                        then_expr: Box::new(literal),
                        else_expr: Box::new(otherwise),
                    },
                ),
            });
        }
        let body = self.int_cast(result.unwrap(), target.clone(), span)?;
        Ok(Expr::new(
            target,
            at,
            ExprKind::Let {
                local,
                value: Box::new(value),
                body: Box::new(body),
            },
        ))
    }

    pub(super) fn derived_clone_ensures(&self, ensures: &mut Vec<Clause>, span: Span) -> R<()> {
        if !self.cx.derived_clones.admitted(self.cx, self.def_id) {
            return Ok(());
        }
        let [parameter] = self.params.as_slice() else {
            return refuse("derive", "the native Clone parameter changed", span);
        };
        let result = self.read_local(self.ret, span);
        if self.locals[parameter.index()].ty
            != (Ty::Ref {
                mutable: false,
                inner: Box::new(result.ty.clone()),
            })
        {
            return refuse("derive", "the native Clone signature changed", span);
        }
        let source = self.builtin_reference_value(
            self.read_local(*parameter, span),
            result.ty.clone(),
            span,
        )?;
        let at = self.sp(span);
        ensures.push(Clause {
            expr: Expr::binary(BinOp::Eq, result, source, Ty::Bool, at),
            span: at,
            attrs: ClauseAttrs::default(),
        });
        Ok(())
    }
}
