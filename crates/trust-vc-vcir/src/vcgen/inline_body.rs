//! Closed source-type substitution and independently named inline bodies.
//!
//! Closed substitution copies the checked source body. A concrete instance
//! instead expands its own body in its own scope, without equating it to the
//! generic origin. Call-origin, role and full signature checks precede entry.
//! The same finite inline grant pays each copied node before allocation; caller
//! type arguments keep their own namespace, never the callee's parameters.

use super::expr::R;
use super::val::{refusal, Ctx};
use crate::{Body, Expr, ExprKind, FnDecl, FnRole, Mode, SpanId, Ty};
use std::cell::Cell;

fn pay(work: &Cell<usize>, count: usize, span: SpanId) -> R<()> {
    super::inline_work::items(work, count, span)
}

pub(super) fn closed(arguments: &[Ty], work: &Cell<usize>, span: SpanId) -> R<bool> {
    fn visit(value: &Ty, work: &Cell<usize>, span: SpanId, depth: usize) -> R<bool> {
        pay(work, 1, span)?;
        if depth >= 64 {
            return Err(refusal(
                "inline-size",
                "inline argument type depth exhausted",
                span,
            ));
        }
        match value {
            Ty::Param(_) => Ok(false),
            Ty::Tuple(children) | Ty::Adt(_, children) => {
                let mut result = true;
                for child in children {
                    result &= visit(child, work, span, depth + 1)?;
                }
                Ok(result)
            }
            Ty::Ref { inner, .. } | Ty::MutRef(inner) => visit(inner, work, span, depth + 1),
            Ty::Bool | Ty::Int(_) | Ty::Unit => Ok(true),
        }
    }
    let mut result = true;
    for argument in arguments {
        result &= visit(argument, work, span, 0)?;
    }
    Ok(result)
}

/// A concrete native instance keeps its own body and logical identity when
/// trait selection changed a call. This checks only independent body expansion;
/// it never licenses sharing the original generic function's UF or definition.
pub(super) fn independent_instance(
    ctx: &Ctx<'_>,
    declaration: &FnDecl,
    arguments: &[Ty],
    work: &Cell<usize>,
    span: SpanId,
) -> R<bool> {
    if declaration.role != FnRole::Instance {
        return Ok(declaration.attrs.instance.is_none());
    }
    let Some(origin) = &declaration.attrs.instance else {
        return Ok(false);
    };
    let Some(original) = ctx.fns.get(&origin.declaration).copied() else {
        return Ok(false);
    };
    pay(
        work,
        origin
            .type_args
            .len()
            .saturating_add(declaration.params.len())
            .saturating_add(1),
        span,
    )?;
    if !arguments.is_empty()
        || !declaration.type_params.is_empty()
        || original.role != FnRole::Item
        || original.attrs.instance.is_some()
        || !original.attrs.inline
        || original.attrs.opaque
        || original.attrs.external_body
        || original.attrs.is_trait_method_impl
        || original.mode != Mode::Spec
        || declaration.mode != original.mode
        || declaration.kind != original.kind
        || declaration.attrs.without_instance() != original.attrs
        || !matches!(original.body, Body::Spec(_))
        || ctx.group(origin.declaration).is_some()
        || !original.decreases.is_empty()
        || original.decreases_when.is_some()
        || original.unwind.is_some()
        || original.decreases_by.is_some()
        || origin.type_args.len() != original.type_params.len()
        || declaration.params.len() != original.params.len()
        || !closed(&origin.type_args, work, span)?
    {
        return Ok(false);
    }
    for (actual, formal) in declaration.params.iter().zip(&original.params) {
        let (Some(actual), Some(formal)) = (declaration.local(*actual), original.local(*formal))
        else {
            return Ok(false);
        };
        if actual.mode != formal.mode
            || actual.mutable != formal.mutable
            || actual.kind != formal.kind
            || actual.ty != ty(ctx, &formal.ty, &origin.type_args, work, span)?
        {
            return Ok(false);
        }
    }
    let (Some(actual), Some(formal)) = (
        declaration.local(declaration.ret),
        original.local(original.ret),
    ) else {
        return Ok(false);
    };
    Ok(actual.mode == formal.mode
        && actual.kind == formal.kind
        && actual.ty == ty(ctx, &formal.ty, &origin.type_args, work, span)?)
}

pub(super) fn ty(
    ctx: &Ctx<'_>,
    source: &Ty,
    arguments: &[Ty],
    work: &Cell<usize>,
    span: SpanId,
) -> R<Ty> {
    fn copy(
        ctx: &Ctx<'_>,
        source: &Ty,
        arguments: Option<&[Ty]>,
        work: &Cell<usize>,
        span: SpanId,
        depth: usize,
    ) -> R<Ty> {
        pay(work, 1, span)?;
        if depth >= 64 {
            return Err(refusal(
                "inline-size",
                "closed inline type depth exhausted",
                span,
            ));
        }
        Ok(match source {
            Ty::Param(index) => {
                if let Some(arguments) = arguments {
                    let actual = arguments.get(*index as usize).ok_or_else(|| {
                        refusal(
                            "inline-body",
                            "a source parameter outside the inline binder",
                            span,
                        )
                    })?;
                    copy(ctx, actual, None, work, span, depth + 1)?
                } else {
                    source.clone()
                }
            }
            Ty::Tuple(children) => {
                pay(work, children.len(), span)?;
                let mut result = Vec::with_capacity(children.len());
                for child in children {
                    result.push(copy(ctx, child, arguments, work, span, depth + 1)?);
                }
                Ty::Tuple(result)
            }
            Ty::Adt(id, children) => {
                let declaration = ctx.adts.get(id).ok_or_else(|| {
                    refusal("inline-body", "an unknown closed inline nominal type", span)
                })?;
                if declaration.type_params.len() != children.len() {
                    return Err(refusal(
                        "inline-body",
                        "a closed inline nominal arity mismatch",
                        span,
                    ));
                }
                pay(work, children.len(), span)?;
                let mut result = Vec::with_capacity(children.len());
                for child in children {
                    result.push(copy(ctx, child, arguments, work, span, depth + 1)?);
                }
                Ty::Adt(*id, result)
            }
            Ty::MutRef(inner) => Ty::MutRef(Box::new(copy(
                ctx,
                inner,
                arguments,
                work,
                span,
                depth + 1,
            )?)),
            Ty::Ref { mutable, inner } => Ty::Ref {
                mutable: *mutable,
                inner: Box::new(copy(ctx, inner, arguments, work, span, depth + 1)?),
            },
            Ty::Bool | Ty::Int(_) | Ty::Unit => source.clone(),
        })
    }
    copy(ctx, source, Some(arguments), work, span, 0)
}

pub(super) fn expression(
    ctx: &Ctx<'_>,
    source: &Expr,
    arguments: &[Ty],
    work: &Cell<usize>,
) -> R<Expr> {
    fn visit(
        ctx: &Ctx<'_>,
        source: &Expr,
        arguments: &[Ty],
        work: &Cell<usize>,
        depth: usize,
    ) -> R<Expr> {
        pay(work, 1, source.span)?;
        if depth >= 256 {
            return Err(refusal(
                "inline-size",
                "closed inline expression depth exhausted",
                source.span,
            ));
        }
        let ty = ty(ctx, &source.ty, arguments, work, source.span)?;
        let child = |value: &Expr| visit(ctx, value, arguments, work, depth + 1).map(Box::new);
        let list = |values: &[Expr]| -> R<Vec<Expr>> {
            pay(work, values.len(), source.span)?;
            let mut copied = Vec::with_capacity(values.len());
            for value in values {
                copied.push(visit(ctx, value, arguments, work, depth + 1)?);
            }
            Ok(copied)
        };
        let binders = |vars: &[(crate::LocalId, Ty)]| -> R<Vec<(crate::LocalId, Ty)>> {
            pay(work, vars.len(), source.span)?;
            let mut copied = Vec::with_capacity(vars.len());
            for (id, source_ty) in vars {
                copied.push((*id, self::ty(ctx, source_ty, arguments, work, source.span)?));
            }
            Ok(copied)
        };
        let triggers = |groups: &[Vec<Expr>]| -> R<Vec<Vec<Expr>>> {
            pay(work, groups.len(), source.span)?;
            let mut copied = Vec::with_capacity(groups.len());
            for group in groups {
                copied.push(list(group)?);
            }
            Ok(copied)
        };
        let kind = match &source.kind {
            ExprKind::UntriggeredQuant { .. } | ExprKind::UntriggeredChoose { .. } => {
                return Err(refusal(
                    "source-construction",
                    "an incomplete binder in an inline body",
                    source.span,
                ));
            }
            ExprKind::Lit(value) => ExprKind::Lit(*value),
            ExprKind::IntegerConstant(value) => ExprKind::IntegerConstant(*value),
            ExprKind::Read(place) | ExprKind::Old(place) => {
                pay(work, place.projections.len(), source.span)?;
                if matches!(&source.kind, ExprKind::Read(_)) {
                    ExprKind::Read(place.clone())
                } else {
                    ExprKind::Old(place.clone())
                }
            }
            ExprKind::Unary { op, arg, check } => ExprKind::Unary {
                op: *op,
                arg: child(arg)?,
                check: *check,
            },
            ExprKind::Binary {
                op,
                lhs,
                rhs,
                check,
            } => ExprKind::Binary {
                op: *op,
                lhs: child(lhs)?,
                rhs: child(rhs)?,
                check: *check,
            },
            ExprKind::If {
                cond,
                then_expr,
                else_expr,
            } => ExprKind::If {
                cond: child(cond)?,
                then_expr: child(then_expr)?,
                else_expr: child(else_expr)?,
            },
            ExprKind::Let { local, value, body } => ExprKind::Let {
                local: *local,
                value: child(value)?,
                body: child(body)?,
            },
            ExprKind::Call {
                callee,
                type_args,
                args,
            } => {
                pay(work, type_args.len(), source.span)?;
                let mut actual = Vec::with_capacity(type_args.len());
                for source_ty in type_args {
                    actual.push(self::ty(ctx, source_ty, arguments, work, source.span)?);
                }
                ExprKind::Call {
                    callee: *callee,
                    type_args: actual,
                    args: list(args)?,
                }
            }
            ExprKind::Cast { arg, kind } => ExprKind::Cast {
                arg: child(arg)?,
                kind: *kind,
            },
            ExprKind::Ctor {
                adt,
                variant,
                fields,
            } => ExprKind::Ctor {
                adt: *adt,
                variant: *variant,
                fields: list(fields)?,
            },
            ExprKind::IsVariant { base, variant } => ExprKind::IsVariant {
                base: child(base)?,
                variant: *variant,
            },
            ExprKind::Tuple(values) => ExprKind::Tuple(list(values)?),
            ExprKind::Field {
                base,
                variant,
                field,
            } => ExprKind::Field {
                base: child(base)?,
                variant: *variant,
                field: *field,
            },
            ExprKind::TupleField { base, index } => ExprKind::TupleField {
                base: child(base)?,
                index: *index,
            },
            ExprKind::Borrow(value) => ExprKind::Borrow(child(value)?),
            ExprKind::MutRefCurrent(value) => ExprKind::MutRefCurrent(child(value)?),
            ExprKind::MutRefFuture(value) => ExprKind::MutRefFuture(child(value)?),
            ExprKind::HasResolved(value) => ExprKind::HasResolved(child(value)?),
            ExprKind::MutRefUpdate { reference, value } => ExprKind::MutRefUpdate {
                reference: child(reference)?,
                value: child(value)?,
            },
            ExprKind::Quant {
                kind,
                vars,
                triggers: groups,
                body,
            } => ExprKind::Quant {
                kind: *kind,
                vars: binders(vars)?,
                triggers: triggers(groups)?,
                body: child(body)?,
            },
            ExprKind::Choose {
                vars,
                triggers: groups,
                cond,
                result,
            } => ExprKind::Choose {
                vars: binders(vars)?,
                triggers: triggers(groups)?,
                cond: child(cond)?,
                result: child(result)?,
            },
            ExprKind::ProofInSpec(_) | ExprKind::ProofInSpecTail { .. } => {
                return Err(refusal(
                    "inline-body",
                    "a closed inline body with embedded proof statements",
                    source.span,
                ))
            }
        };
        Ok(Expr::new(ty, source.span, kind))
    }
    visit(ctx, source, arguments, work, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{DefHash, ExprKind, FnId, IntRange, LocalId, Place, VcCrate};

    #[test]
    fn closed_inline_substitution_covers_choice_binders_result_and_nested_call_types() {
        let krate = VcCrate::new("inline_copy");
        let ctx = Ctx::for_width(&krate, 64);
        let span = SpanId(7);
        let bound = LocalId(3);
        let read = Expr::read(Place::local(bound), Ty::Param(0), span);
        let source = Expr::new(
            Ty::Param(0),
            span,
            ExprKind::Choose {
                vars: vec![(bound, Ty::Param(0))],
                triggers: vec![vec![Expr::new(
                    Ty::Param(0),
                    span,
                    ExprKind::Call {
                        callee: FnId(DefHash::new(0, 9)),
                        type_args: vec![Ty::Param(0)],
                        args: vec![read.clone()],
                    },
                )]],
                cond: Box::new(Expr::bool_lit(true, span)),
                result: Box::new(read),
            },
        );
        let work = Cell::new(200_000);
        let actual = Ty::Int(IntRange::U(128));
        let copied = expression(&ctx, &source, std::slice::from_ref(&actual), &work).unwrap();
        assert_eq!(copied.ty, actual);
        let ExprKind::Choose {
            vars,
            triggers,
            result,
            ..
        } = copied.kind
        else {
            panic!("choice retained")
        };
        assert_eq!(vars, vec![(bound, actual.clone())]);
        assert_eq!(result.ty, actual);
        let ExprKind::Call {
            callee,
            type_args,
            args,
        } = &triggers[0][0].kind
        else {
            panic!("call retained")
        };
        assert_eq!(*callee, FnId(DefHash::new(0, 9)));
        assert_eq!(type_args, std::slice::from_ref(&actual));
        assert_eq!(args[0].ty, actual);
        assert_eq!(source.ty, Ty::Param(0), "checked source remains unchanged");
    }

    #[test]
    fn caller_parameter_identity_is_not_reinterpreted_as_a_callee_argument() {
        let krate = VcCrate::new("inline_scope");
        let ctx = Ctx::for_width(&krate, 64);
        let work = Cell::new(100);
        assert_eq!(
            ty(&ctx, &Ty::Param(0), &[Ty::Param(1)], &work, SpanId(0)).unwrap(),
            Ty::Param(1)
        );
        assert!(!closed(&[Ty::Param(1)], &work, SpanId(0)).unwrap());
        assert!(ty(&ctx, &Ty::Param(1), &[Ty::Bool], &work, SpanId(0)).is_err());
    }

    #[test]
    fn type_expansion_and_expression_copy_share_one_budget_before_allocating() {
        let krate = VcCrate::new("inline_budget");
        let ctx = Ctx::for_width(&krate, 64);
        let source = Expr::read(
            Place::local(LocalId(0)),
            Ty::Tuple(vec![Ty::Param(0); 32]),
            SpanId(0),
        );
        let work = Cell::new(100);
        assert!(expression(&ctx, &source, &[Ty::Tuple(vec![Ty::Bool; 32])], &work).is_err());
        assert!(work.get() < 100);
    }
}
