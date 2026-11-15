//! Finite transparent source products are tuples of isolated scalar values.
//! Their nominal identity is checked before layout expansion; this grants no
//! fields to an imported opaque carrier and introduces no datatype axioms.

use super::*;

/// Debit the complete expanded type before each owned node. Parameter
/// occurrences copy their actual argument in its caller namespace, never
/// recursively reinterpret the caller's parameters as the callee's own.
pub(super) fn substitute(
    ctx: &Ctx<'_>,
    ty: &Ty,
    arguments: &[Ty],
    work: &mut usize,
    span: crate::SpanId,
) -> R<Ty> {
    fn copy(
        ctx: &Ctx<'_>,
        ty: &Ty,
        arguments: Option<&[Ty]>,
        work: &mut usize,
        span: crate::SpanId,
        depth: usize,
    ) -> R<Ty> {
        *work = work
            .checked_sub(4)
            .ok_or_else(|| refusal("bit-vector-budget", "expanded BV type work exhausted", span))?;
        if depth >= 64 {
            return Err(refusal(
                "bit-vector-type",
                "expanded BV type depth exhausted",
                span,
            ));
        }
        Ok(match ty {
            Ty::Param(index) => {
                match arguments.and_then(|arguments| arguments.get(*index as usize)) {
                    Some(actual) => copy(ctx, actual, None, work, span, depth + 1)?,
                    None => Ty::Param(*index),
                }
            }
            Ty::Tuple(children) => {
                let mut result = Vec::new();
                for child in children {
                    result.push(copy(ctx, child, arguments, work, span, depth + 1)?);
                }
                Ty::Tuple(result)
            }
            Ty::Adt(id, children) => {
                let declaration = ctx.adts.get(id).ok_or_else(|| {
                    refusal(
                        "bit-vector-type",
                        "an unknown native type-argument declaration",
                        span,
                    )
                })?;
                if children.len() != declaration.type_params.len() {
                    return Err(refusal(
                        "bit-vector-type",
                        "a native type-argument arity mismatch",
                        span,
                    ));
                }
                let mut result = Vec::new();
                for child in children {
                    result.push(copy(ctx, child, arguments, work, span, depth + 1)?);
                }
                Ty::Adt(*id, result)
            }
            Ty::Ref { mutable, inner } => Ty::Ref {
                mutable: *mutable,
                inner: Box::new(copy(ctx, inner, arguments, work, span, depth + 1)?),
            },
            Ty::Bool | Ty::Int(_) | Ty::Unit => ty.clone(),
        })
    }
    copy(ctx, ty, Some(arguments), work, span, 0)
}

impl Lower<'_, '_> {
    /// Native result typing is proved along with the isolated assertion.
    /// Layout matching alone says nothing about mathematical integer range.
    pub(super) fn constant_result(
        &mut self,
        e: &Expr,
        value: &Value,
        ty: &Ty,
        depth: usize,
    ) -> R<()> {
        self.debit(e, 1)?;
        if depth >= 64 {
            return self.error(e, "constant result layout depth exhausted");
        }
        match (value, ty) {
            (Value::Bool(_), Ty::Bool) => Ok(()),
            (Value::Integer(value), Ty::Int(range)) => self.valid_range(e, value, *range),
            (Value::Product(children), Ty::Unit) if children.is_empty() => Ok(()),
            (Value::Product(children), Ty::Tuple(types)) if children.len() == types.len() => {
                for (value, ty) in children.iter().zip(types) {
                    self.constant_result(e, value, ty, depth + 1)?;
                }
                Ok(())
            }
            (Value::Product(children), Ty::Adt(id, arguments)) => {
                let ctx = self.ctx;
                let declaration = ctx
                    .adts
                    .get(id)
                    .ok_or_else(|| refusal("bit-vector-type", "unknown constant result", e.span))?;
                if declaration.kind != crate::AdtKind::Struct
                    || declaration.variants.len() != 1
                    || declaration.type_params.len() != arguments.len()
                    || declaration.variants[0].fields.len() != children.len()
                {
                    return self.error(e, "unsupported constant result layout");
                }
                for (value, field) in children.iter().zip(&declaration.variants[0].fields) {
                    let actual = self.substitute(e, &field.ty, arguments)?;
                    self.constant_result(e, value, &actual, depth + 1)?;
                }
                Ok(())
            }
            _ => self.error(e, "unsupported constant result type"),
        }
    }

    pub(super) fn place_value(
        &mut self,
        e: &Expr,
        place: &Place,
        old: bool,
        ty: &Ty,
        depth: usize,
    ) -> R<Value> {
        self.debit(e, 1)?;
        if depth >= 64 {
            return self.error(e, "a BV product place exceeds its finite layout depth");
        }
        match ty {
            Ty::Bool => self.scalar_place(e, place, old, None),
            Ty::Int(range) => self.scalar_place(e, place, old, Some(*range)),
            Ty::Ref {
                mutable: false,
                inner,
            } => {
                let mut projected = place.clone();
                projected.projections.push(Projection::Deref);
                self.place_value(e, &projected, old, inner, depth + 1)
            }
            Ty::Unit => Ok(Value::Product(std::sync::Arc::new(Vec::new()))),
            Ty::Tuple(types) => {
                self.debit(e, types.len())?;
                let mut children = Vec::new();
                for (index, ty) in types.iter().enumerate() {
                    let mut projected = place.clone();
                    projected.projections.push(Projection::TupleField(
                        u32::try_from(index).map_err(|_| {
                            refusal("bit-vector-type", "a tuple field index overflow", e.span)
                        })?,
                    ));
                    children.push(self.place_value(e, &projected, old, ty, depth + 1)?);
                }
                Ok(Value::Product(std::sync::Arc::new(children)))
            }
            Ty::Adt(id, arguments) => {
                let ctx = self.ctx;
                let declaration = ctx.adts.get(id).ok_or_else(|| {
                    refusal(
                        "bit-vector-type",
                        "an unknown BV product declaration",
                        e.span,
                    )
                })?;
                if declaration.kind != crate::AdtKind::Struct
                    || declaration.variants.len() != 1
                    || declaration.type_params.len() != arguments.len()
                {
                    return self.error(
                        e,
                        "a BV product requires its exact finite transparent declaration",
                    );
                }
                let fields = &declaration.variants[0].fields;
                self.debit(e, fields.len())?;
                let mut children = Vec::new();
                for (index, field) in fields.iter().enumerate() {
                    let mut projected = place.clone();
                    projected.projections.push(Projection::Field {
                        variant: 0,
                        field: u32::try_from(index).map_err(|_| {
                            refusal("bit-vector-type", "a struct field index overflow", e.span)
                        })?,
                    });
                    let actual = self.substitute(e, &field.ty, arguments)?;
                    children.push(self.place_value(e, &projected, old, &actual, depth + 1)?);
                }
                Ok(Value::Product(std::sync::Arc::new(children)))
            }
            _ => self.error(
                e,
                "an unsupported mutable, abstract or opaque BV product place",
            ),
        }
    }

    pub(super) fn matches_value(
        &mut self,
        e: &Expr,
        value: &Value,
        ty: &Ty,
        depth: usize,
    ) -> R<bool> {
        self.debit(e, 1)?;
        if depth >= 64 {
            return self.error(e, "a BV product signature exceeds its finite layout depth");
        }
        match (value, ty) {
            (Value::Bool(_), Ty::Bool) | (Value::Integer(_), Ty::Int(_)) => Ok(true),
            (
                value,
                Ty::Ref {
                    mutable: false,
                    inner,
                },
            ) => self.matches_value(e, value, inner, depth + 1),
            (Value::Product(children), Ty::Unit) => Ok(children.is_empty()),
            (Value::Product(children), Ty::Tuple(types)) if children.len() == types.len() => {
                for (value, ty) in children.iter().zip(types) {
                    if !self.matches_value(e, value, ty, depth + 1)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (Value::Product(children), Ty::Adt(id, arguments)) => {
                let ctx = self.ctx;
                let declaration = ctx.adts.get(id).ok_or_else(|| {
                    refusal(
                        "bit-vector-type",
                        "an unknown BV result declaration",
                        e.span,
                    )
                })?;
                if declaration.kind != crate::AdtKind::Struct
                    || declaration.variants.len() != 1
                    || declaration.type_params.len() != arguments.len()
                    || declaration.variants[0].fields.len() != children.len()
                {
                    return Ok(false);
                }
                for (value, field) in children.iter().zip(&declaration.variants[0].fields) {
                    let actual = self.substitute(e, &field.ty, arguments)?;
                    if !self.matches_value(e, value, &actual, depth + 1)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    pub(super) fn equal_value(
        &mut self,
        e: &Expr,
        left: Value,
        right: Value,
        depth: usize,
    ) -> R<Term> {
        self.debit(e, 1)?;
        if depth >= 64 {
            return self.error(e, "a BV product equality exceeds its finite depth");
        }
        match (left, right) {
            (Value::Bool(left), Value::Bool(right)) => Ok(binary(Op::Eq, left, right)),
            (Value::Integer(left), Value::Integer(right)) => {
                self.operation(e, left.compare(right, Comparison::Eq))
            }
            (Value::Product(left), Value::Product(right)) if left.len() == right.len() => {
                let mut equality = Term::Bool(true);
                for (left, right) in left.iter().zip(right.iter()) {
                    let field = self.equal_value(e, left.clone(), right.clone(), depth + 1)?;
                    equality = binary(Op::And, equality, field);
                }
                Ok(equality)
            }
            _ => self.error(e, "a BV equality with mismatched source layouts"),
        }
    }

    pub(super) fn conditional_value(
        &mut self,
        e: &Expr,
        condition: &Term,
        yes: Value,
        no: Value,
        depth: usize,
    ) -> R<Value> {
        self.debit(e, 1)?;
        if depth >= 64 {
            return self.error(e, "a BV product conditional exceeds its finite depth");
        }
        match (yes, no) {
            (Value::Bool(yes), Value::Bool(no)) => Ok(Value::Bool(shared(Term::If {
                condition: Box::new(condition.clone()),
                then_term: Box::new(yes),
                else_term: Box::new(no),
            }))),
            (Value::Integer(yes), Value::Integer(no)) => Ok(Value::Integer(
                self.operation(e, Integer::conditional(condition.clone(), yes, no))?,
            )),
            (Value::Product(yes), Value::Product(no)) if yes.len() == no.len() => {
                self.debit(e, yes.len())?;
                let mut children = Vec::new();
                for (yes, no) in yes.iter().zip(no.iter()) {
                    children.push(self.conditional_value(
                        e,
                        condition,
                        yes.clone(),
                        no.clone(),
                        depth + 1,
                    )?);
                }
                Ok(Value::Product(std::sync::Arc::new(children)))
            }
            _ => self.error(e, "a BV conditional with mismatched source layouts"),
        }
    }
}
