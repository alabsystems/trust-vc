//! Isolated finite BV translation. `Reads` is consulted ONLY for definite
//! availability/valid projection; none of its SSA values or path facts enter
//! the question. Every actual source place becomes an independent BV symbol.

use std::collections::HashMap;

use trust_vc_bitvector::integer::{Arithmetic, Comparison, Integer};
use trust_vc_bitvector::{Op, Query, Sort, Term};

use super::expr::{Reads, R};
use super::val::{refusal, Ctx};
use crate::{
    BinOp, Body, Expr, ExprKind, FnId, FnRole, IntRange, Lit, LocalId, Mode, Place, Projection,
    QuantKind, Ty, UnOp,
};

mod source_simplify;
mod specialization;
mod values;

#[derive(Clone)]
enum Value {
    Bool(Term),
    Integer(Integer),
    Product(std::sync::Arc<Vec<Value>>),
}

fn shared(term: Term) -> Term {
    Term::Shared(std::sync::Arc::new(term))
}
fn unary(op: Op, term: Term) -> Term {
    shared(Term::App {
        op,
        args: vec![term],
    })
}
fn binary(op: Op, left: Term, right: Term) -> Term {
    shared(Term::App {
        op,
        args: vec![left, right],
    })
}

struct Lower<'a, 'ctx> {
    ctx: &'a Ctx<'ctx>,
    reads: &'a Reads,
    architecture: u32,
    work: usize,
    places: HashMap<(Place, bool), String>,
    variables: Vec<(String, Sort)>,
    bound: HashMap<LocalId, Value>,
    types: Vec<Ty>,
    inline_stack: Vec<FnId>,
    next_binder: usize,
    owner: Option<FnId>,
    constant_depth: usize,
    validity_guard: Term,
    validity: Vec<Term>,
    /// Syntax admission visits dead code without creating a value witness.
    /// Its translated data are always discarded; live queries use false.
    admission_only: bool,
    /// A source-language restriction, independent of the IR's product support.
    scalar_inputs: bool,
}

impl Lower<'_, '_> {
    fn debit(&mut self, e: &Expr, amount: usize) -> R<()> {
        self.work = self.work.checked_sub(amount).ok_or_else(|| {
            refusal(
                "bit-vector-budget",
                "isolated BV translation work exhausted",
                e.span,
            )
        })?;
        Ok(())
    }

    fn error<T>(&self, e: &Expr, detail: &'static str) -> R<T> {
        Err(refusal("bit-vector-expression", detail, e.span))
    }

    fn ty(&mut self, e: &Expr, ty: &Ty) -> R<Ty> {
        let actual = values::substitute(self.ctx, ty, &self.types, &mut self.work, e.span)?;
        if actual.has_param() {
            return self.error(
                e,
                "a BV expression with an unrepresented actual type parameter",
            );
        }
        Ok(actual)
    }

    fn substitute(&mut self, e: &Expr, ty: &Ty, arguments: &[Ty]) -> R<Ty> {
        values::substitute(self.ctx, ty, arguments, &mut self.work, e.span)
    }

    fn bits(&mut self, e: &Expr) -> R<(u32, bool)> {
        let Some(range) = self.ty(e, &e.ty)?.int_range() else {
            return self.error(e, "a non-integer BV operand");
        };
        self.range_bits(e, range)
    }

    fn range_bits(&self, e: &Expr, range: IntRange) -> R<(u32, bool)> {
        if !range.is_valid() || matches!(range, IntRange::Int | IntRange::Nat | IntRange::Char) {
            return self.error(e, "expected finite-width integer");
        }
        Ok((
            range
                .bits(self.architecture)
                .ok_or_else(|| refusal("bit-vector-type", "missing finite BV width", e.span))?,
            range.is_signed_machine(),
        ))
    }

    fn boolean(&mut self, e: &Expr, depth: usize) -> R<Term> {
        if self.ty(e, &e.ty)? != Ty::Bool {
            return self.error(e, "a non-Boolean BV clause");
        }
        match self.expr(e, depth)? {
            Value::Bool(term) => Ok(term),
            _ => self.error(e, "a non-Boolean BV expression"),
        }
    }

    fn integer(&mut self, e: &Expr, depth: usize) -> R<Integer> {
        match self.expr(e, depth)? {
            Value::Integer(value) => Ok(value),
            _ => self.error(e, "a non-integer BV expression"),
        }
    }

    fn operation<T>(&self, e: &Expr, value: Result<T, &'static str>) -> R<T> {
        value.map_err(|detail| refusal("bit-vector-expression", detail, e.span))
    }

    fn call(
        &mut self,
        e: &Expr,
        callee: FnId,
        type_args: &[Ty],
        args: &[Expr],
        depth: usize,
    ) -> R<Value> {
        self.debit(
            e,
            type_args.len().saturating_add(args.len()).saturating_add(1),
        )?;
        let actual_types: Vec<_> = type_args
            .iter()
            .map(|ty| self.ty(e, ty))
            .collect::<R<_>>()?;
        let (callee, actual_types) = self.ctx.call_origin(callee, &actual_types, e.span)?;
        let declaration = *self.ctx.fns.get(&callee).ok_or_else(|| {
            refusal(
                "bit-vector-inline",
                "an unknown original inline declaration",
                e.span,
            )
        })?;
        let (body, constant) = match &declaration.body {
            Body::Spec(body) => (body, false),
            Body::Constant(body)
                if declaration.kind == crate::FnKind::Constant(crate::ConstMode::Dual) =>
            {
                (body, true)
            }
            _ => return self.error(e, "a BV call without a checked value body"),
        };
        if (self.constant_depth > 0 && !constant)
            || (constant
                && (declaration.attrs.opaque
                    || self
                        .owner
                        .and_then(|owner| self.ctx.def_order(owner))
                        .is_some_and(|order| {
                            order.contains_key(&callee)
                                || declaration
                                    .attrs
                                    .instance
                                    .as_ref()
                                    .is_some_and(|origin| order.contains_key(&origin.declaration))
                        })))
            || (!constant && !declaration.attrs.inline)
            || declaration.mode != Mode::Spec
            || matches!(declaration.role, FnRole::Imported | FnRole::TraitDecl)
            || declaration.attrs.external_body
            || self.ctx.group(callee).is_some()
            || !declaration.decreases.is_empty()
            || self.inline_stack.contains(&callee)
            || self.inline_stack.len() >= 256
            || actual_types.len() != declaration.type_params.len()
            || args.len() != declaration.params.len()
        {
            return self.error(
                e,
                "a BV call without a checked nonrecursive inline body and exact signature",
            );
        }
        // Source substitution retains the entire nominal/decorated type;
        // only genuine finite transparent layouts can be expanded below.
        // Imported/opaque declarations never acquire field/body authority.
        let result_ty = self.substitute(
            e,
            declaration.ret_ty().ok_or_else(|| {
                refusal(
                    "bit-vector-inline",
                    "a missing inline result declaration",
                    e.span,
                )
            })?,
            &actual_types,
        )?;
        if result_ty.has_param() {
            return self.error(e, "an incomplete inline result type substitution");
        }
        if result_ty != self.ty(e, &e.ty)? {
            return self.error(
                e,
                "an inline result substitution differs from its actual type",
            );
        }
        if self.substitute(e, &body.ty, &actual_types)? != result_ty {
            return self.error(
                e,
                "an inline body differs from its original declared result type",
            );
        }
        let mut parameters = HashMap::new();
        for (local, arg) in declaration.params.iter().zip(args) {
            let formal = declaration.local(*local).ok_or_else(|| {
                refusal(
                    "bit-vector-inline",
                    "a missing inline source parameter",
                    e.span,
                )
            })?;
            let formal_type = self.substitute(e, &formal.ty, &actual_types)?;
            if formal_type != self.ty(arg, &arg.ty)? {
                return self.error(
                    e,
                    "an inline parameter substitution differs from its actual type",
                );
            }
            let value = self.expr(arg, depth)?;
            if !self.matches_value(arg, &value, &formal_type, 0)? {
                return self.error(
                    e,
                    "an inline argument value differs from its actual typed layout",
                );
            }
            parameters.insert(*local, value);
        }
        let saved_parameters = std::mem::replace(&mut self.bound, parameters);
        let saved_types = std::mem::replace(&mut self.types, actual_types);
        self.inline_stack.push(callee);
        self.constant_depth += usize::from(constant);
        let result = self.expr(body, depth).and_then(|value| {
            if constant {
                self.constant_result(e, &value, &result_ty, 0)?;
            }
            Ok(value)
        });
        self.constant_depth -= usize::from(constant);
        self.inline_stack.pop();
        self.types = saved_types;
        self.bound = saved_parameters;
        let value = result?;
        if !self.matches_value(e, &value, &result_ty, 0)? {
            return self.error(e, "an inline body has the wrong result kind");
        }
        Ok(value)
    }

    fn valid(&mut self, e: &Expr, condition: Term) -> R<()> {
        self.debit(e, 1)?;
        self.validity
            .push(binary(Op::Implies, self.validity_guard.clone(), condition));
        Ok(())
    }

    fn valid_range(&mut self, e: &Expr, value: &Integer, range: IntRange) -> R<()> {
        let range = super::val::concrete_range(range, self.architecture);
        if let Some(minimum) = range.min(self.architecture) {
            let lower = Integer::literal(trust_vc_bitvector::IntLit {
                negative: minimum < 0,
                magnitude: minimum.unsigned_abs(),
            });
            let condition = self.operation(e, lower.compare(value.clone(), Comparison::Le))?;
            self.valid(e, condition)?;
        }
        if let Some(maximum) = range.max(self.architecture) {
            let upper = Integer::literal(trust_vc_bitvector::IntLit {
                negative: false,
                magnitude: maximum,
            });
            let condition = self.operation(e, value.clone().compare(upper, Comparison::Le))?;
            self.valid(e, condition)?;
        }
        Ok(())
    }

    fn place(&mut self, e: &Expr, place: &Place, old: bool) -> R<Value> {
        let scalar_ty = if self.scalar_inputs {
            Some(self.ty(e, &e.ty)?)
        } else {
            None
        };
        if let Some(ty) = &scalar_ty {
            let mut input = ty;
            while let Ty::Ref { inner, .. } | Ty::MutRef(inner) = input {
                self.debit(e, 1)?;
                input = inner;
            }
            if !matches!(input, Ty::Bool | Ty::Int(_)) {
                return Err(refusal(
                    "bit-vector-type",
                    format!(
                        "bit_vector prover cannot handle type `{}`",
                        crate::pretty::ty_name(self.ctx.source, input)
                    ),
                    e.span,
                ));
            }
        }
        if let Some(value) = self.available_place(e, place, old)? {
            return Ok(value.clone());
        }
        let ty = match scalar_ty {
            Some(ty) => ty,
            None => self.ty(e, &e.ty)?,
        };
        self.place_value(e, place, old, &ty, 0)
    }

    /// Source availability is independent of finite BV input conversion.
    /// A preprocessing identity may remove a product/integer input, but may
    /// never manufacture an initialized value or cross an inline namespace.
    fn available_place(&mut self, e: &Expr, place: &Place, old: bool) -> R<Option<&Value>> {
        self.debit(e, place.projections.len().saturating_add(1))?;
        if !old {
            if let Some(value) = self.bound.get(&place.local) {
                let mut value = value;
                for projection in &place.projections {
                    value = match (projection, value) {
                        (Projection::Deref, _) => value,
                        (
                            Projection::TupleField(index)
                            | Projection::Field {
                                variant: 0,
                                field: index,
                            },
                            Value::Product(children),
                        ) => children.get(*index as usize).ok_or_else(|| {
                            refusal(
                                "bit-vector-place",
                                "an inline product projection out of range",
                                e.span,
                            )
                        })?,
                        _ => return self.error(e, "an unsupported inline product projection"),
                    };
                }
                return Ok(Some(value));
            }
        }
        if !self.inline_stack.is_empty() {
            return self.error(
                e,
                "an inline body read outside its actual parameter/binder scope",
            );
        }
        if self.admission_only {
            // WF already checked the original place and its declared type.
            // This branch admits syntax, never definite initialization.
            if place.projections.iter().any(|projection| {
                !matches!(
                    projection,
                    Projection::Deref
                        | Projection::TupleField(_)
                        | Projection::Field { variant: 0, .. }
                )
            }) {
                return self.error(e, "an unsupported BV enum projection");
            }
        } else {
            let source = if old {
                &self.reads.old
            } else {
                &self.reads.read
            };
            let Some(root) = source.get(&place.local) else {
                return self.error(e, "an unavailable or uninitialized BV place");
            };
            // Validate actual projection/availability, then deliberately discard
            // its mathematical value. Ambient bindings are not BV assumptions.
            let mut value = root;
            for projection in &place.projections {
                value = match projection {
                    Projection::Deref => value,
                    Projection::TupleField(index)
                    | Projection::Field {
                        variant: 0,
                        field: index,
                    } => value.child(*index).ok_or_else(|| {
                        refusal("bit-vector-place", "a BV projection out of range", e.span)
                    })?,
                    _ => return self.error(e, "an unsupported BV enum projection"),
                };
            }
        }
        Ok(None)
    }

    fn scalar_place(
        &mut self,
        e: &Expr,
        place: &Place,
        old: bool,
        range: Option<IntRange>,
    ) -> R<Value> {
        let key = (place.clone(), old);
        let name = if let Some(name) = self.places.get(&key) {
            name.clone()
        } else {
            let name = format!("bv_place_{}", self.places.len());
            let sort = if let Some(range) = range {
                Sort::Bits(self.range_bits(e, range)?.0)
            } else {
                Sort::Bool
            };
            self.variables.push((name.clone(), sort));
            self.places.insert(key, name.clone());
            name
        };
        let term = Term::Var(name);
        if let Some(range) = range {
            let (width, signed) = self.range_bits(e, range)?;
            Ok(Value::Integer(
                self.operation(e, Integer::from_bits(term, width, signed))?,
            ))
        } else {
            Ok(Value::Bool(term))
        }
    }

    fn expr(&mut self, e: &Expr, depth: usize) -> R<Value> {
        self.debit(e, 1)?;
        if depth >= 256 {
            return self.error(e, "isolated BV translation depth exhausted");
        }
        if self.ctx.bitvector_policy == super::BitvectorPolicy::VerusSyntactic {
            if let Some(value) = source_simplify::comparison(self, e, depth)? {
                return Ok(Value::Bool(Term::Bool(value)));
            }
        }
        let next = depth + 1;
        match &e.kind {
            ExprKind::Lit(Lit::Bool(value)) => Ok(Value::Bool(Term::Bool(*value))),
            ExprKind::Lit(Lit::Int(value)) => Ok(Value::Integer(Integer::literal((*value).into()))),
            ExprKind::IntegerConstant(value) => Ok(Value::Integer(Integer::literal(
                value
                    .value(self.architecture)
                    .ok_or_else(|| {
                        refusal(
                            "bit-vector-type",
                            "an unsupported primitive constant",
                            e.span,
                        )
                    })?
                    .into(),
            ))),
            ExprKind::Lit(Lit::Unit) => Ok(Value::Product(std::sync::Arc::new(Vec::new()))),
            ExprKind::Read(place) => self.place(e, place, false),
            ExprKind::Old(place) => self.place(e, place, true),
            ExprKind::Unary { op, arg, check } => {
                if check.is_some() && (self.constant_depth == 0 || *op != UnOp::Neg) {
                    return self.error(
                        e,
                        "an unsupported checked unary operation in an isolated BV value",
                    );
                }
                match op {
                    UnOp::Not if self.ty(arg, &arg.ty)? == Ty::Bool => {
                        Ok(Value::Bool(unary(Op::Not, self.boolean(arg, next)?)))
                    }
                    UnOp::Not => {
                        let value = self.integer(arg, next)?;
                        // Pinned signed ! is the unbounded signed operation;
                        // only unsigned ! is explicitly width-clipped.
                        let clip = self
                            .ty(e, &e.ty)?
                            .int_range()
                            .filter(|range| !range.is_signed_machine())
                            .and_then(|range| range.bits(self.architecture));
                        Ok(Value::Integer(self.operation(e, value.bit_not(clip))?))
                    }
                    UnOp::Neg => {
                        let value = self.integer(arg, next)?;
                        let zero = Integer::literal(trust_vc_bitvector::IntLit {
                            negative: false,
                            magnitude: 0,
                        });
                        let value = self.operation(e, zero.arithmetic(value, Arithmetic::Sub))?;
                        if check.is_some() {
                            let range = self.ty(e, &e.ty)?.int_range().ok_or_else(|| {
                                refusal("bit-vector-type", "a checked noninteger constant", e.span)
                            })?;
                            self.valid_range(e, &value, range)?;
                        }
                        Ok(Value::Integer(value))
                    }
                }
            }
            ExprKind::Binary {
                op,
                lhs,
                rhs,
                check,
            } => {
                if check.is_some() && (self.constant_depth == 0 || !op.is_arithmetic()) {
                    // In particular, checking the shifted result's range is
                    // insufficient: it does not establish 0 <= count < width.
                    // Ordinary initializer translation also refuses checked
                    // shifts until both obligations are represented there.
                    return self.error(
                        e,
                        "an unsupported checked binary operation in an isolated BV value",
                    );
                }
                self.binary(e, *op, lhs, rhs, next, check.is_some())
            }
            ExprKind::Call {
                callee,
                type_args,
                args,
            } => self.call(e, *callee, type_args, args, next),
            ExprKind::If {
                cond,
                then_expr,
                else_expr,
            } => {
                let test = self.boolean(cond, next)?;
                let outer = self.validity_guard.clone();
                self.validity_guard = binary(Op::And, outer.clone(), test.clone());
                let yes = self.expr(then_expr, next)?;
                self.validity_guard = binary(Op::And, outer.clone(), unary(Op::Not, test.clone()));
                let no = self.expr(else_expr, next)?;
                self.validity_guard = outer;
                self.conditional_value(e, &test, yes, no, 0)
            }
            ExprKind::Let { local, value, body } => {
                let value = self.expr(value, next)?;
                let old = self.bound.insert(*local, value);
                let result = self.expr(body, next);
                if let Some(old) = old {
                    self.bound.insert(*local, old);
                } else {
                    self.bound.remove(local);
                }
                result
            }
            ExprKind::Cast { arg, kind } => {
                let value = self.integer(arg, next)?;
                if *kind == crate::CastKind::Exact {
                    return Ok(Value::Integer(value));
                }
                match self.ty(e, &e.ty)?.int_range() {
                    Some(IntRange::Int) => Ok(Value::Integer(value)),
                    Some(IntRange::Nat) => Ok(Value::Integer(self.operation(e, value.clip_nat())?)),
                    Some(range) if range.is_bounded() && !matches!(range, IntRange::Char) => {
                        let bits = range.bits(self.architecture).ok_or_else(|| {
                            refusal("bit-vector-type", "missing finite cast width", e.span)
                        })?;
                        // Exact casts already passed VcIR's range-containment
                        // check; clipping a contained value is the identity.
                        Ok(Value::Integer(self.operation(
                            e,
                            value.clip(bits, range.is_signed_machine()),
                        )?))
                    }
                    _ => self.error(e, "an unsupported BV cast target"),
                }
            }
            ExprKind::IsVariant { .. } => self.error(e, "an enum variant test in a BV query"),
            ExprKind::Ctor {
                adt,
                variant,
                fields,
            } => {
                let ty = self.ty(e, &e.ty)?;
                if *variant != 0
                    || !matches!(&ty, Ty::Adt(actual, _) if actual == adt)
                    || !self.ctx.adts.get(adt).is_some_and(|declaration| {
                        declaration.kind == crate::AdtKind::Struct
                            && declaration.variants.len() == 1
                    })
                {
                    return self.error(e, "an unsupported or opaque BV constructor");
                }
                let Ty::Adt(_, arguments) = &ty else {
                    return self.error(e, "a BV constructor without its full nominal type");
                };
                let ctx = self.ctx;
                let declaration = ctx.adts.get(adt).ok_or_else(|| {
                    refusal("bit-vector-type", "an unknown BV constructor", e.span)
                })?;
                if arguments.len() != declaration.type_params.len()
                    || fields.len() != declaration.variants[0].fields.len()
                {
                    return self.error(e, "a BV constructor with the wrong complete arity");
                }
                for (field, native) in fields.iter().zip(&declaration.variants[0].fields) {
                    if self.ty(field, &field.ty)? != self.substitute(e, &native.ty, arguments)? {
                        return self.error(
                            e,
                            "a BV constructor field differs from its native ordered signature",
                        );
                    }
                }
                let mut children = Vec::new();
                for field in fields {
                    children.push(self.expr(field, next)?);
                }
                let value = Value::Product(std::sync::Arc::new(children));
                if !self.matches_value(e, &value, &ty, 0)? {
                    return self.error(e, "a BV constructor with a mismatched layout");
                }
                Ok(value)
            }
            ExprKind::Tuple(fields) => {
                let Ty::Tuple(types) = self.ty(e, &e.ty)? else {
                    return self.error(e, "a BV tuple without its actual tuple type");
                };
                if types.len() != fields.len() || types.is_empty() {
                    return self.error(e, "a BV tuple with an invalid actual arity");
                }
                let mut children = Vec::new();
                for (field, ty) in fields.iter().zip(&types) {
                    if self.ty(field, &field.ty)? != *ty {
                        return self
                            .error(e, "a BV tuple element differs from its ordered signature");
                    }
                    children.push(self.expr(field, next)?);
                }
                Ok(Value::Product(std::sync::Arc::new(children)))
            }
            ExprKind::Field {
                base,
                variant: 0,
                field,
            }
            | ExprKind::TupleField { base, index: field } => {
                let Value::Product(children) = self.expr(base, next)? else {
                    return self.error(e, "a BV field of a scalar or opaque value");
                };
                children.get(*field as usize).cloned().ok_or_else(|| {
                    refusal(
                        "bit-vector-expression",
                        "a BV field index out of range",
                        e.span,
                    )
                })
            }
            ExprKind::Borrow(inner) => self.expr(inner, next),
            ExprKind::MutRefCurrent(_)
            | ExprKind::MutRefFuture(_)
            | ExprKind::MutRefUpdate { .. }
            | ExprKind::HasResolved(_)
            | ExprKind::ProofInSpecTail { .. } => Err(refusal(
                "bit-vector-type",
                "an opaque reference or embedded proof in a BV expression",
                e.span,
            )),
            ExprKind::Quant {
                kind,
                vars,
                body,
                triggers,
            } => {
                self.debit(e, vars.len())?;
                let mut binders = Vec::new();
                let mut saved = Vec::new();
                for (local, ty) in vars {
                    // LocalId is only function-local. Inlining may introduce
                    // another binder with the same numeric ID while an actual
                    // argument still refers to the caller's binder.
                    let name = format!("bv_bound_{}", self.next_binder);
                    self.next_binder = self.next_binder.checked_add(1).ok_or_else(|| {
                        refusal(
                            "bit-vector-budget",
                            "isolated BV binder identity exhausted",
                            e.span,
                        )
                    })?;
                    let ty = self.ty(e, ty)?;
                    let (sort, value) = if ty == Ty::Bool {
                        (Sort::Bool, Value::Bool(Term::Var(name.clone())))
                    } else {
                        let Some(range) = ty.int_range() else {
                            return self.error(e, "a non-scalar BV quantified binder");
                        };
                        if !range.is_valid()
                            || !range.is_bounded()
                            || matches!(range, IntRange::Char)
                        {
                            return self.error(
                                e,
                                "a BV quantified binder without a finite supported domain",
                            );
                        }
                        let bits = range.bits(self.architecture).ok_or_else(|| {
                            refusal("bit-vector-type", "missing binder width", e.span)
                        })?;
                        (
                            Sort::Bits(bits),
                            Value::Integer(self.operation(
                                e,
                                Integer::from_bits(
                                    Term::Var(name.clone()),
                                    bits,
                                    range.is_signed_machine(),
                                ),
                            )?),
                        )
                    };
                    saved.push((*local, self.bound.insert(*local, value)));
                    binders.push((name, sort));
                }
                let translated = (|| {
                    let body = self.boolean(body, next)?;
                    self.debit(e, triggers.len())?;
                    let mut patterns = Vec::new();
                    for group in triggers {
                        self.debit(e, group.len().saturating_add(1))?;
                        let mut terms = Vec::new();
                        for pattern in group {
                            // Exactly the body's typed operator/integer
                            // lowering, with the SAME active bound values and
                            // remaining grant; no replacement UF or premise.
                            let term = match self.expr(pattern, next)? {
                                Value::Bool(term) => term,
                                Value::Integer(value) => value.into_term(),
                                Value::Product(_) => {
                                    return self.error(pattern, "a non-scalar BV trigger")
                                }
                            };
                            terms.push(term);
                        }
                        patterns.push(terms);
                    }
                    Ok((body, patterns))
                })();
                for (local, old) in saved.into_iter().rev() {
                    if let Some(old) = old {
                        self.bound.insert(local, old);
                    } else {
                        self.bound.remove(&local);
                    }
                }
                let (body, triggers) = translated?;
                Ok(Value::Bool(shared(Term::Quant {
                    forall: *kind == QuantKind::Forall,
                    binders,
                    body: Box::new(body),
                    triggers,
                })))
            }
            _ => self.error(
                e,
                "an isolated BV expression requiring unsupported lowering or inlining",
            ),
        }
    }

    fn binary(
        &mut self,
        e: &Expr,
        op: BinOp,
        lhs: &Expr,
        rhs: &Expr,
        depth: usize,
        checked: bool,
    ) -> R<Value> {
        if matches!(op, BinOp::Eq | BinOp::Ne) {
            let left = self.expr(lhs, depth)?;
            let right = self.expr(rhs, depth)?;
            let equality = self.equal_value(e, left, right, 0)?;
            return Ok(Value::Bool(if op == BinOp::Eq {
                equality
            } else {
                unary(Op::Not, equality)
            }));
        }
        if self.ty(lhs, &lhs.ty)? == Ty::Bool {
            let left = self.boolean(lhs, depth)?;
            let outer = self.validity_guard.clone();
            if matches!(op, BinOp::And | BinOp::Or | BinOp::Implies) {
                let taken = if op == BinOp::Or {
                    unary(Op::Not, left.clone())
                } else {
                    left.clone()
                };
                self.validity_guard = binary(Op::And, outer.clone(), taken);
            }
            let right = self.boolean(rhs, depth)?;
            self.validity_guard = outer;
            let term = match op {
                BinOp::And | BinOp::BitAnd => binary(Op::And, left, right),
                BinOp::Or | BinOp::BitOr => binary(Op::Or, left, right),
                BinOp::BitXor => binary(Op::Xor, left, right),
                BinOp::Implies => binary(Op::Implies, left, right),
                BinOp::Eq => binary(Op::Eq, left, right),
                BinOp::Ne => unary(Op::Not, binary(Op::Eq, left, right)),
                _ => return self.error(e, "an unsupported Boolean BV operator"),
            };
            return Ok(Value::Bool(term));
        }
        let left = self.integer(lhs, depth)?;
        let right = self.integer(rhs, depth)?;
        if checked && matches!(op, BinOp::Div | BinOp::Rem) {
            let range = self
                .ty(e, &e.ty)?
                .int_range()
                .ok_or_else(|| refusal("bit-vector-type", "checked noninteger division", e.span))?;
            if range.is_signed_machine() {
                return self.error(
                    e,
                    "signed machine constant division requires operator-trait semantics",
                );
            }
            let zero = Integer::literal(trust_vc_bitvector::IntLit {
                negative: false,
                magnitude: 0,
            });
            let nonzero = unary(
                Op::Not,
                self.operation(e, right.clone().compare(zero, Comparison::Eq))?,
            );
            self.valid(e, nonzero)?;
        }
        let value = match op {
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let (left, right, comparison) = match op {
                    BinOp::Eq | BinOp::Ne => (left, right, Comparison::Eq),
                    BinOp::Lt => (left, right, Comparison::Lt),
                    BinOp::Le => (left, right, Comparison::Le),
                    BinOp::Gt => (right, left, Comparison::Lt),
                    _ => (right, left, Comparison::Le),
                };
                let term = self.operation(e, left.compare(right, comparison))?;
                return Ok(Value::Bool(if op == BinOp::Ne {
                    unary(Op::Not, term)
                } else {
                    term
                }));
            }
            BinOp::Add | BinOp::Sub | BinOp::Mul => self.operation(
                e,
                left.arithmetic(
                    right,
                    match op {
                        BinOp::Add => Arithmetic::Add,
                        BinOp::Sub => Arithmetic::Sub,
                        _ => Arithmetic::Mul,
                    },
                ),
            )?,
            BinOp::Div | BinOp::Rem => {
                let left_extra = u32::from(!left.is_signed() && right.is_signed());
                let right_extra = u32::from(left.is_signed() && !right.is_signed());
                let aligned = left
                    .bits()
                    .checked_add(left_extra)
                    .and_then(|a| right.bits().checked_add(right_extra).map(|b| a.max(b)))
                    .ok_or_else(|| refusal("bit-vector-type", "division width overflow", e.span))?;
                let output = aligned
                    .checked_add(u32::from(
                        (left.is_signed() || right.is_signed()) && op == BinOp::Div,
                    ))
                    .ok_or_else(|| refusal("bit-vector-type", "division width overflow", e.span))?;
                let arbitrary = format!("bv_arbitrary_{}", self.variables.len());
                self.variables.push((arbitrary.clone(), Sort::Bits(output)));
                self.operation(
                    e,
                    left.euclidean(right, op == BinOp::Rem, Term::Var(arbitrary)),
                )?
            }
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => self.operation(
                e,
                left.bitwise(
                    right,
                    match op {
                        BinOp::BitAnd => Op::BitAnd,
                        BinOp::BitOr => Op::BitOr,
                        _ => Op::BitXor,
                    },
                ),
            )?,
            BinOp::Shr => self.operation(e, left.shift_right(right))?,
            BinOp::Shl => {
                let (width, signed) = self.bits(e)?;
                self.operation(e, left.shift_left(right, width, signed))?
            }
            _ => return self.error(e, "an unsupported integer BV operator"),
        };
        if checked && !matches!(op, BinOp::Div | BinOp::Rem) {
            let range = self.ty(e, &e.ty)?.int_range().ok_or_else(|| {
                refusal("bit-vector-type", "checked noninteger arithmetic", e.span)
            })?;
            self.valid_range(e, &value, range)?;
        }
        Ok(Value::Integer(value))
    }
}

pub(super) fn lower_detailed(
    ctx: &Ctx<'_>,
    requires: &[&Expr],
    goal: &Expr,
    reads: &Reads,
    architecture: u32,
    owner: Option<FnId>,
) -> R<(Query, bool)> {
    if !matches!(architecture, 32 | 64) {
        return Err(refusal(
            "bit-vector-architecture",
            "an unsupported BV architecture",
            goal.span,
        ));
    }
    let mut lower = Lower {
        ctx,
        reads,
        architecture,
        work: 200_000,
        places: HashMap::new(),
        variables: Vec::new(),
        bound: HashMap::new(),
        types: Vec::new(),
        inline_stack: Vec::new(),
        next_binder: 0,
        owner,
        constant_depth: 0,
        validity_guard: Term::Bool(true),
        validity: Vec::new(),
        admission_only: false,
        scalar_inputs: owner
            .and_then(|id| ctx.fns.get(&id))
            .is_some_and(|decl| decl.attrs.bitvector_scalar_inputs),
    };
    let mut hypotheses = Vec::new();
    for requirement in requires {
        hypotheses.push(lower.boolean(requirement, 0)?);
    }
    let mut goal_term = lower.boolean(goal, 0)?;
    for validity in std::mem::take(&mut lower.validity) {
        goal_term = binary(Op::And, validity, goal_term);
    }
    let query = Query {
        variables: lower.variables,
        requires: hypotheses,
        goal: goal_term,
        architecture,
    };
    query
        .validate()
        .map_err(|detail| refusal("bit-vector-query", detail, goal.span))?;
    // Diagnostic-only normalization uses the REMAINING translation grant.
    // It never changes this query, adds a premise, or creates solver authority.
    let consumed = specialization::consumed(ctx, requires, goal, &mut lower.work)?;
    Ok((query, consumed))
}

#[cfg(test)]
pub(super) fn lower(
    ctx: &Ctx<'_>,
    requires: &[&Expr],
    goal: &Expr,
    reads: &Reads,
    architecture: u32,
) -> R<Query> {
    lower_detailed(ctx, requires, goal, reads, architecture, None).map(|(query, _)| query)
}

/// Language admission also visits dead source branches. It grants no value
/// availability or query hypothesis; that remains the live lowering's job.
pub(super) fn admit_syntax(ctx: &Ctx<'_>, expr: &Expr, work: &mut usize) -> R<()> {
    let reads = Reads::default();
    let mut lower = Lower {
        ctx,
        reads: &reads,
        architecture: ctx.pointer_width,
        work: *work,
        places: HashMap::new(),
        variables: Vec::new(),
        bound: HashMap::new(),
        types: Vec::new(),
        inline_stack: Vec::new(),
        next_binder: 0,
        owner: None,
        constant_depth: 0,
        validity_guard: Term::Bool(true),
        validity: Vec::new(),
        admission_only: true,
        scalar_inputs: false,
    };
    // Both branches, Boolean operands and every inline body use exactly the
    // same typed operation rules as live lowering. Only place availability is
    // deferred. No resulting term, variable or premise leaves this function.
    let result = lower.boolean(expr, 0);
    *work = lower.work;
    // Reader/WF/effect admission already checked the complete source. This
    // conversion walk applies to every retained independent SST event,
    // including ordinary-dead paths. An actual Maybe::Never-pruned suffix
    // never becomes an SST BV query and never calls this conversion phase.
    result.map(|_| ())
}

#[cfg(test)]
mod tests {
    use super::super::term::Term as MathTerm;
    use super::super::val::Val;
    use super::*;
    use crate::{IntLit, SpanId};

    fn lower(requires: &[&Expr], goal: &Expr, reads: &Reads, architecture: u32) -> R<Query> {
        let krate = crate::VcCrate::new("isolated scalar control");
        let ctx = Ctx::new(&krate);
        super::lower(&ctx, requires, goal, reads, architecture)
    }

    fn read(local: u32, range: IntRange) -> Expr {
        Expr {
            ty: Ty::Int(range),
            span: SpanId(0),
            kind: ExprKind::Read(Place::local(LocalId(local))),
        }
    }

    fn zero() -> Expr {
        Expr {
            ty: Ty::Int(IntRange::Int),
            span: SpanId(0),
            kind: ExprKind::Lit(Lit::Int(IntLit::from_i128(0))),
        }
    }

    #[test]
    fn translation_checks_availability_but_never_copies_an_ambient_value_fact() {
        let x = read(0, IntRange::U(8));
        let goal = Expr::binary(BinOp::Eq, x, zero(), Ty::Bool, SpanId(0));
        let mut reads = Reads::default();
        reads.read.insert(LocalId(0), Val::Leaf(MathTerm::Int(0)));
        let question = lower(&[], &goal, &reads, 64).unwrap();
        assert_eq!(question.variables, [("bv_place_0".into(), Sort::Bits(8))]);
        assert!(question.requires.is_empty());
        assert_ne!(question.goal, Term::Bool(true));
        assert!(lower(&[], &goal, &Reads::default(), 64).is_err());
    }

    #[test]
    fn original_old_and_current_places_are_distinct_isolated_symbols() {
        let current = read(0, IntRange::I(16));
        let mut old = current.clone();
        old.kind = ExprKind::Old(Place::local(LocalId(0)));
        let goal = Expr::binary(BinOp::Eq, current, old, Ty::Bool, SpanId(0));
        let mut reads = Reads::default();
        reads.read.insert(LocalId(0), Val::Leaf(MathTerm::Int(7)));
        reads.old.insert(LocalId(0), Val::Leaf(MathTerm::Int(7)));
        let question = lower(&[], &goal, &reads, 32).unwrap();
        assert_eq!(question.variables.len(), 2);
        assert_ne!(question.variables[0].0, question.variables[1].0);
        assert!(question.requires.is_empty());
    }

    #[test]
    fn mathematical_input_domains_and_signed_shift_counts_are_honestly_refused() {
        let mut reads = Reads::default();
        reads.read.insert(LocalId(0), Val::Leaf(MathTerm::Int(0)));
        let mathematical = Expr::binary(
            BinOp::Eq,
            read(0, IntRange::Int),
            zero(),
            Ty::Bool,
            SpanId(0),
        );
        assert!(lower(&[], &mathematical, &reads, 64).is_err());
        let shifted = Expr::binary(
            BinOp::Shr,
            read(0, IntRange::U(8)),
            Expr {
                ty: Ty::Int(IntRange::Int),
                span: SpanId(0),
                kind: ExprKind::Lit(Lit::Int(IntLit::from_i128(-1))),
            },
            Ty::Int(IntRange::U(8)),
            SpanId(0),
        );
        let goal = Expr::binary(BinOp::Eq, shifted, zero(), Ty::Bool, SpanId(0));
        assert!(lower(&[], &goal, &reads, 64).is_err());
    }
}

#[cfg(test)]
#[path = "bitvector_trigger_tests.rs"]
mod trigger_tests;
