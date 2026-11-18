//! Diagnostic-only counterpart of pinned sst_elaborate/interpreter before
//! bitvector_to_air::bitwidth_exact. It observes effective source values,
//! including literal folding and actual inline substitution. These private
//! nodes never enter a query, crate, definition registry, or ownership gate.
//! The real lowerer still admits/translates ALL original syntax first.

use super::*;
use num_bigint::BigInt;
use std::sync::Arc;

type N = Arc<Node>;
struct Node {
    kind: Kind,
    consumed: bool,
    size: usize,
    unsupported: Option<crate::SpanId>,
}
// Pinned syntactic equality ignores source spans and derived cached metadata.
impl PartialEq for Node {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}
impl Eq for Node {}
#[derive(PartialEq, Eq)]
enum Kind {
    Bool(bool),
    Int(BigInt),
    Read(Place, bool, Ty),
    Bound(usize, Ty),
    Primitive(crate::IntegerConstant),
    Unary(UnOp, N),
    Binary(BinOp, N, N),
    Cast(IntRange, N),
    If(N, N, N),
    Product(Vec<N>),
    Quant(QuantKind, Vec<N>, N),
}

struct Observe<'a, 'ctx, 'pay> {
    ctx: &'a Ctx<'ctx>,
    pay: &'pay mut usize,
    bound: HashMap<LocalId, N>,
    types: Vec<Ty>,
    stack: Vec<FnId>,
    next: usize,
}

impl Observe<'_, '_, '_> {
    fn debit(&mut self, e: &Expr, n: usize) -> R<()> {
        *self.pay = self.pay.checked_sub(n).ok_or_else(|| {
            refusal(
                "bit-vector-budget",
                "effective BV source diagnostic work exhausted",
                e.span,
            )
        })?;
        Ok(())
    }
    fn error<T>(&self, e: &Expr, s: &'static str) -> R<T> {
        Err(refusal("bit-vector-diagnostic", s, e.span))
    }
    fn ty(&mut self, e: &Expr, ty: &Ty) -> R<Ty> {
        values::substitute(self.ctx, ty, &self.types, self.pay, e.span)
    }
    fn node(&mut self, e: &Expr, kind: Kind, intrinsic: bool, children: &[N]) -> R<N> {
        self.debit(
            e,
            4usize.checked_add(children.len()).ok_or_else(|| {
                refusal(
                    "bit-vector-budget",
                    "effective BV node size overflow",
                    e.span,
                )
            })?,
        )?;
        let payload = match &kind {
            Kind::Int(i) => usize::try_from(i.bits() / 64 + 1)
                .map_err(|_| refusal("bit-vector-budget", "effective payload overflow", e.span))?,
            Kind::Read(place, ..) => place.projections.len(),
            _ => 0,
        };
        let mut size = 1usize
            .checked_add(payload)
            .ok_or_else(|| refusal("bit-vector-budget", "effective payload overflow", e.span))?;
        let mut consumed = intrinsic;
        let mut unsupported = if matches!(
            &kind,
            Kind::Primitive(
                crate::IntegerConstant::Maximum(IntRange::USize | IntRange::ISize)
                    | crate::IntegerConstant::Minimum(IntRange::ISize)
            )
        ) {
            Some(e.span)
        } else {
            None
        };
        for child in children {
            size = size.checked_add(child.size).ok_or_else(|| {
                refusal(
                    "bit-vector-budget",
                    "effective BV source size overflow",
                    e.span,
                )
            })?;
            if size > 200_000 {
                return self.error(e, "effective BV source is oversized");
            }
            consumed |= child.consumed;
            if unsupported.is_none() {
                unsupported = child.unsupported;
            }
        }
        Ok(Arc::new(Node {
            kind,
            consumed,
            size,
            unsupported,
        }))
    }
    fn boolean(&mut self, e: &Expr, value: bool) -> R<N> {
        self.node(e, Kind::Bool(value), false, &[])
    }
    fn integer(&mut self, e: &Expr, value: BigInt) -> R<N> {
        self.debit(
            e,
            usize::try_from(value.bits() / 64 + 1).map_err(|_| {
                refusal(
                    "bit-vector-budget",
                    "effective integer size overflow",
                    e.span,
                )
            })?,
        )?;
        self.node(e, Kind::Int(value), false, &[])
    }
    fn equal(&mut self, e: &Expr, a: &N, b: &N) -> R<bool> {
        self.debit(
            e,
            a.size.checked_add(b.size).ok_or_else(|| {
                refusal(
                    "bit-vector-budget",
                    "effective equality size overflow",
                    e.span,
                )
            })?,
        )?;
        Ok(a == b)
    }
    fn copy(&mut self, e: &Expr, n: &N) -> R<N> {
        self.debit(e, 1)?;
        Ok(Arc::clone(n))
    }
    fn pointer(range: IntRange) -> bool {
        matches!(range, IntRange::USize | IntRange::ISize)
    }
    fn int(n: &N) -> Option<&BigInt> {
        if let Kind::Int(i) = &n.kind {
            Some(i)
        } else {
            None
        }
    }
    fn truth(n: &N) -> Option<bool> {
        if let Kind::Bool(b) = n.kind {
            Some(b)
        } else {
            None
        }
    }
    fn in_range(i: &BigInt, range: IntRange, width: u32) -> bool {
        if range == IntRange::Int {
            return true;
        }
        if range == IntRange::Nat {
            return i >= &BigInt::from(0);
        }
        if !range.is_valid() || range == IntRange::Char {
            return false;
        }
        let Some(bits) = range.bits(width) else {
            return false;
        };
        if range.is_signed_machine() {
            let half = BigInt::from(1) << (bits - 1) as usize;
            i >= &(-&half) && i < &half
        } else {
            i >= &BigInt::from(0) && i < &(BigInt::from(1) << bits as usize)
        }
    }
    fn truncate_integer(&mut self, e: &Expr, value: BigInt, range: IntRange) -> R<Option<BigInt>> {
        self.debit(e, 16)?;
        let at = |width| -> Option<BigInt> {
            let bits = range.bits(width)?;
            let modulus = BigInt::from(1) << bits as usize;
            let mut out = &value % &modulus;
            if out < BigInt::from(0) {
                out += &modulus;
            }
            if range.is_signed_machine() && out >= (BigInt::from(1) << (bits - 1) as usize) {
                out -= modulus;
            }
            Some(out)
        };
        Ok(match self.ctx.architecture {
            crate::bitvector::Architecture::Exactly(width) => at(width),
            crate::bitvector::Architecture::Either32Or64 if Self::pointer(range) => {
                match (at(32), at(64)) {
                    (Some(a), Some(b)) if a == b => Some(a),
                    _ => None,
                }
            }
            crate::bitvector::Architecture::Either32Or64 => at(32),
        })
    }
    fn clip(&mut self, e: &Expr, range: IntRange, arg: N) -> R<N> {
        // Upstream folds an in-range literal cast under default only if it
        // fits32 (therefore64). Out-of-range clipping stays symbolic there.
        if let Some(i) = Self::int(&arg) {
            self.debit(e, 8)?;
            let width = match self.ctx.architecture {
                crate::bitvector::Architecture::Either32Or64 => 32,
                crate::bitvector::Architecture::Exactly(width) => width,
            };
            if Self::in_range(i, range, width) {
                return Ok(arg);
            }
        }
        let consumed = Self::pointer(range);
        self.node(e, Kind::Cast(range, Arc::clone(&arg)), consumed, &[arg])
    }
    fn precharge_type_copy(&mut self, e: &Expr, ty: &Ty, depth: usize) -> R<()> {
        self.debit(e, 4)?;
        if depth >= 64 {
            return self.error(e, "effective source type copy depth exhausted");
        }
        match ty {
            Ty::Tuple(children) | Ty::Adt(_, children) | Ty::Projection(_, children) => {
                for child in children {
                    self.precharge_type_copy(e, child, depth + 1)?;
                }
            }
            Ty::Ref { inner, .. } | Ty::MutRef(inner) => {
                self.precharge_type_copy(e, inner, depth + 1)?
            }
            _ => {}
        }
        Ok(())
    }
    fn finite_leaf(&mut self, e: &Expr, place: &Place, old: bool, ty: &Ty, depth: usize) -> R<N> {
        self.debit(e, 4 + place.projections.len())?;
        if depth >= 64 {
            return self.error(e, "effective product depth exhausted");
        }
        match ty {
            Ty::Bool | Ty::Int(_) => self.node(
                e,
                Kind::Read(place.clone(), old, ty.clone()),
                ty.int_range().is_some_and(Self::pointer),
                &[],
            ),
            Ty::Ref {
                mutable: false,
                inner,
            } => {
                let mut place = place.clone();
                place.projections.push(Projection::Deref);
                self.finite_leaf(e, &place, old, inner, depth + 1)
            }
            Ty::Unit => self.node(e, Kind::Product(Vec::new()), false, &[]),
            Ty::Tuple(types) => {
                self.debit(
                    e,
                    types.len().checked_mul(2).ok_or_else(|| {
                        refusal(
                            "bit-vector-budget",
                            "effective tuple inventory overflow",
                            e.span,
                        )
                    })?,
                )?;
                let mut fields = Vec::new();
                for (index, ty) in types.iter().enumerate() {
                    let mut place = place.clone();
                    place
                        .projections
                        .push(Projection::TupleField(u32::try_from(index).map_err(
                            |_| {
                                refusal(
                                    "bit-vector-diagnostic",
                                    "effective tuple index overflow",
                                    e.span,
                                )
                            },
                        )?));
                    fields.push(self.finite_leaf(e, &place, old, ty, depth + 1)?);
                }
                self.node(e, Kind::Product(fields.clone()), false, &fields)
            }
            Ty::Adt(id, args) => {
                let ctx = self.ctx;
                let declaration = ctx.adts.get(id).ok_or_else(|| {
                    refusal("bit-vector-diagnostic", "unknown effective product", e.span)
                })?;
                if declaration.kind != crate::AdtKind::Struct
                    || declaration.variants.len() != 1
                    || args.len() != declaration.type_params.len()
                {
                    return self.error(e, "unsupported effective product");
                }
                self.debit(
                    e,
                    declaration.variants[0]
                        .fields
                        .len()
                        .checked_mul(2)
                        .ok_or_else(|| {
                            refusal(
                                "bit-vector-budget",
                                "effective layout inventory overflow",
                                e.span,
                            )
                        })?,
                )?;
                let mut fields = Vec::new();
                for (index, field) in declaration.variants[0].fields.iter().enumerate() {
                    let actual = values::substitute(ctx, &field.ty, args, self.pay, e.span)?;
                    let mut place = place.clone();
                    place.projections.push(Projection::Field {
                        variant: 0,
                        field: u32::try_from(index).map_err(|_| {
                            refusal(
                                "bit-vector-diagnostic",
                                "effective field index overflow",
                                e.span,
                            )
                        })?,
                    });
                    fields.push(self.finite_leaf(e, &place, old, &actual, depth + 1)?);
                }
                self.node(e, Kind::Product(fields.clone()), false, &fields)
            }
            _ => self.error(e, "unsupported effective source type"),
        }
    }
    fn go(&mut self, e: &Expr, depth: usize) -> R<N> {
        // Constant allocation/Arc work is paid before constructing even a
        // literal. Variable-size integer and copy work is charged separately.
        self.debit(e, 8)?;
        if depth >= 256 {
            return self.error(e, "effective source depth exhausted");
        }
        let d = depth + 1;
        match &e.kind {
            ExprKind::Lit(Lit::Bool(b)) => self.boolean(e, *b),
            ExprKind::Lit(Lit::Int(i)) => self.integer(
                e,
                if i.negative {
                    -BigInt::from(i.magnitude)
                } else {
                    BigInt::from(i.magnitude)
                },
            ),
            ExprKind::Lit(Lit::Unit) => self.node(e, Kind::Product(vec![]), false, &[]),
            ExprKind::IntegerConstant(value) => {
                let pointer = match value {
                    crate::IntegerConstant::WordBits => true,
                    crate::IntegerConstant::Minimum(r) => *r == IntRange::ISize,
                    crate::IntegerConstant::Maximum(r) | crate::IntegerConstant::Bits(r) => {
                        Self::pointer(*r)
                    }
                };
                if pointer && self.ctx.architecture == crate::bitvector::Architecture::Either32Or64
                {
                    self.node(e, Kind::Primitive(*value), true, &[])
                } else {
                    let i = value.value(self.ctx.pointer_width).ok_or_else(|| {
                        refusal(
                            "bit-vector-diagnostic",
                            "invalid effective primitive constant",
                            e.span,
                        )
                    })?;
                    self.integer(
                        e,
                        if i.negative {
                            -BigInt::from(i.magnitude)
                        } else {
                            BigInt::from(i.magnitude)
                        },
                    )
                }
            }
            ExprKind::Read(place) | ExprKind::Old(place) => {
                let old = matches!(&e.kind, ExprKind::Old(_));
                self.debit(e, 1)?;
                if !old {
                    if let Some(bound) = self.bound.get(&place.local).cloned() {
                        self.debit(e, 1 + place.projections.len())?;
                        let mut value = bound;
                        for projection in &place.projections {
                            value = match (projection, &value.kind) {
                                (Projection::Deref, _) => Arc::clone(&value),
                                (
                                    Projection::TupleField(i)
                                    | Projection::Field {
                                        variant: 0,
                                        field: i,
                                    },
                                    Kind::Product(fields),
                                ) => fields.get(*i as usize).cloned().ok_or_else(|| {
                                    refusal(
                                        "bit-vector-diagnostic",
                                        "effective projection outside product",
                                        e.span,
                                    )
                                })?,
                                _ => return self.error(e, "unsupported effective projection"),
                            };
                        }
                        return Ok(value);
                    }
                }
                let ty = self.ty(e, &e.ty)?;
                self.finite_leaf(e, place, old, &ty, 0)
            }
            ExprKind::Unary { op, arg, .. } => {
                let arg = self.go(arg, d)?;
                if let Some(b) = Self::truth(&arg) {
                    if *op == UnOp::Not {
                        return self.boolean(e, !b);
                    }
                }
                if let Some(i) = Self::int(&arg) {
                    self.debit(
                        e,
                        usize::try_from(i.bits() / 64 + 8).map_err(|_| {
                            refusal("bit-vector-budget", "effective unary size overflow", e.span)
                        })?,
                    )?;
                    if *op == UnOp::Neg {
                        return self.integer(e, -i);
                    }
                    if *op == UnOp::Not {
                        let range = self.ty(e, &e.ty)?.int_range();
                        if let Some(range) = range {
                            // Pinned signed ! folds only an i128 constant;
                            // unsigned pointer ! remains symbolic at default.
                            if range.is_signed_machine() {
                                if let Ok(i) = i128::try_from(i) {
                                    return self.integer(e, BigInt::from(!i));
                                }
                            } else if let Ok(i) = u128::try_from(i) {
                                if let Some(value) =
                                    self.truncate_integer(e, BigInt::from(!i), range)?
                                {
                                    return self.integer(e, value);
                                }
                            }
                        }
                    }
                }
                if *op == UnOp::Neg {
                    let zero = self.integer(e, BigInt::from(0))?;
                    return self.node(
                        e,
                        Kind::Binary(BinOp::Sub, Arc::clone(&zero), Arc::clone(&arg)),
                        false,
                        &[zero, arg],
                    );
                }
                let consumes = if *op == UnOp::Not {
                    self.ty(e, &e.ty)?
                        .int_range()
                        .is_some_and(|r| Self::pointer(r) && !r.is_signed_machine())
                } else {
                    false
                };
                self.node(e, Kind::Unary(*op, Arc::clone(&arg)), consumes, &[arg])
            }
            ExprKind::Binary { op, lhs, rhs, .. } => {
                let left = self.go(lhs, d)?;
                match (op, Self::truth(&left)) {
                    (BinOp::And, Some(false)) => return self.boolean(e, false),
                    (BinOp::Or | BinOp::Implies, Some(true)) if *op == BinOp::Or => {
                        return self.boolean(e, true)
                    }
                    (BinOp::Implies, Some(false)) => return self.boolean(e, true),
                    (BinOp::And | BinOp::Implies, Some(true)) | (BinOp::Or, Some(false)) => {
                        return self.go(rhs, d)
                    }
                    _ => {}
                }
                let right = self.go(rhs, d)?;
                self.binary(e, *op, left, right)
            }
            ExprKind::If {
                cond,
                then_expr,
                else_expr,
            } => {
                let cond = self.go(cond, d)?;
                if let Some(b) = Self::truth(&cond) {
                    return self.go(if b { then_expr } else { else_expr }, d);
                }
                let yes = self.go(then_expr, d)?;
                let no = self.go(else_expr, d)?;
                self.node(
                    e,
                    Kind::If(Arc::clone(&cond), Arc::clone(&yes), Arc::clone(&no)),
                    false,
                    &[cond, yes, no],
                )
            }
            ExprKind::Let { local, value, body } => {
                let value = self.go(value, d)?;
                let old = self.bound.insert(*local, value);
                let out = self.go(body, d);
                if let Some(old) = old {
                    self.bound.insert(*local, old);
                } else {
                    self.bound.remove(local);
                }
                out
            }
            ExprKind::Cast { arg, kind } => {
                let value = self.go(arg, d)?;
                // Exact is VcIR's identity coercion, not a source clipping op;
                // this is the same distinction the real lowerer consumes.
                if *kind == crate::CastKind::Exact {
                    return Ok(value);
                }
                let range = self.ty(e, &e.ty)?.int_range().ok_or_else(|| {
                    refusal("bit-vector-diagnostic", "noninteger effective cast", e.span)
                })?;
                self.clip(e, range, value)
            }
            ExprKind::Call {
                callee,
                type_args,
                args,
            } => {
                self.debit(e, type_args.len() + args.len() + 1)?;
                let actual: Vec<_> = type_args
                    .iter()
                    .map(|ty| self.ty(e, ty))
                    .collect::<R<_>>()?;
                // call_origin's current sealed API returns owned type copies.
                // Prepay BOTH possible source vectors by borrowed census before
                // invoking it; never clone a native instance's payload first.
                for ty in &actual {
                    self.precharge_type_copy(e, ty, 0)?;
                }
                let ctx = self.ctx;
                if let Some(origin) = ctx.fns.get(callee).and_then(|f| f.attrs.instance.as_ref()) {
                    for ty in &origin.type_args {
                        self.precharge_type_copy(e, ty, 0)?;
                    }
                }
                let (callee, actual) = self.ctx.call_origin(*callee, &actual, e.span)?;
                let declaration = *self.ctx.fns.get(&callee).ok_or_else(|| {
                    refusal(
                        "bit-vector-diagnostic",
                        "unknown effective inline source",
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
                    _ => return self.error(e, "missing effective checked value body"),
                };
                if (!constant && !declaration.attrs.inline)
                    || self.stack.contains(&callee)
                    || self.stack.len() >= 256
                    || declaration.params.len() != args.len()
                {
                    return self.error(e, "invalid effective inline source");
                }
                let mut params = HashMap::new();
                for (param, arg) in declaration.params.iter().zip(args) {
                    params.insert(*param, self.go(arg, d)?);
                }
                let saved = std::mem::replace(&mut self.bound, params);
                let saved_types = std::mem::replace(&mut self.types, actual);
                self.stack.push(callee);
                let out = self.go(body, d);
                self.stack.pop();
                self.bound = saved;
                self.types = saved_types;
                out
            }
            ExprKind::IsVariant { .. } => self.error(e, "an enum variant test in a BV query"),
            ExprKind::Ctor { adt, .. }
                if self
                    .ctx
                    .adts
                    .get(adt)
                    .is_some_and(|declaration| declaration.kind == crate::AdtKind::Enum) =>
            {
                self.error(e, "an enum constructor in a BV query")
            }
            ExprKind::Ctor { fields, .. } | ExprKind::Tuple(fields) => {
                self.debit(
                    e,
                    fields.len().checked_mul(2).ok_or_else(|| {
                        refusal(
                            "bit-vector-budget",
                            "effective field inventory overflow",
                            e.span,
                        )
                    })?,
                )?;
                let fields = fields
                    .iter()
                    .map(|f| self.go(f, d))
                    .collect::<R<Vec<_>>>()?;
                self.node(e, Kind::Product(fields.clone()), false, &fields)
            }
            ExprKind::Field {
                base,
                variant: 0,
                field,
            }
            | ExprKind::TupleField { base, index: field } => {
                let base = self.go(base, d)?;
                let Kind::Product(fields) = &base.kind else {
                    return self.error(e, "nonproduct effective projection");
                };
                let field = fields.get(*field as usize).ok_or_else(|| {
                    refusal(
                        "bit-vector-diagnostic",
                        "missing effective product field",
                        e.span,
                    )
                })?;
                self.copy(e, field)
            }
            ExprKind::Borrow(inner) => self.go(inner, d),
            ExprKind::MutRefCurrent(_)
            | ExprKind::MutRefFuture(_)
            | ExprKind::MutRefUpdate { .. }
            | ExprKind::HasResolved(_)
            | ExprKind::ProofInSpecTail { .. } => {
                self.error(e, "opaque reference operation or embedded proof")
            }
            ExprKind::Quant {
                kind, vars, body, ..
            } => {
                self.debit(
                    e,
                    vars.len().checked_mul(4).ok_or_else(|| {
                        refusal(
                            "bit-vector-budget",
                            "effective binder size overflow",
                            e.span,
                        )
                    })?,
                )?;
                let mut binders = Vec::new();
                let mut saved = Vec::new();
                for (local, ty) in vars {
                    let ty = self.ty(e, ty)?;
                    let consumes = ty.int_range().is_some_and(Self::pointer);
                    let id = self.next;
                    self.next = self.next.checked_add(1).ok_or_else(|| {
                        refusal(
                            "bit-vector-budget",
                            "effective binder identity exhausted",
                            e.span,
                        )
                    })?;
                    let binder = self.node(e, Kind::Bound(id, ty), consumes, &[])?;
                    saved.push((*local, self.bound.insert(*local, Arc::clone(&binder))));
                    binders.push(binder);
                }
                let body = self.go(body, d);
                for (local, old) in saved.into_iter().rev() {
                    if let Some(old) = old {
                        self.bound.insert(local, old);
                    } else {
                        self.bound.remove(&local);
                    }
                }
                let body = body?;
                if Self::truth(&body).is_some() {
                    return Ok(body);
                }
                let mut children = binders.clone();
                children.push(Arc::clone(&body));
                self.node(e, Kind::Quant(*kind, binders, body), false, &children)
            }
            _ => self.error(e, "unrepresented effective BV source"),
        }
    }

    fn binary(&mut self, e: &Expr, op: BinOp, a: N, b: N) -> R<N> {
        let zero = BigInt::from(0);
        let one = BigInt::from(1);
        if matches!(
            op,
            BinOp::Eq | BinOp::Ne | BinOp::Sub | BinOp::BitXor | BinOp::BitAnd | BinOp::BitOr
        ) && self.equal(e, &a, &b)?
        {
            return match op {
                BinOp::Eq => self.boolean(e, true),
                BinOp::Ne => self.boolean(e, false),
                BinOp::Sub | BinOp::BitXor => self.integer(e, zero),
                _ => Ok(a),
            };
        }
        if let (Some(x), Some(y)) = (Self::truth(&a), Self::truth(&b)) {
            return self.boolean(
                e,
                match op {
                    BinOp::And | BinOp::BitAnd => x && y,
                    BinOp::Or | BinOp::BitOr => x || y,
                    BinOp::Implies => !x || y,
                    BinOp::BitXor => x ^ y,
                    BinOp::Eq => x == y,
                    BinOp::Ne => x != y,
                    _ => return self.error(e, "invalid effective Boolean operator"),
                },
            );
        }
        if op == BinOp::BitXor {
            if let Some(x) = Self::truth(&a) {
                if !x {
                    return Ok(b);
                }
                return self.node(e, Kind::Unary(UnOp::Not, Arc::clone(&b)), false, &[b]);
            }
            if let Some(y) = Self::truth(&b) {
                if !y {
                    return Ok(a);
                }
                return self.node(e, Kind::Unary(UnOp::Not, Arc::clone(&a)), false, &[a]);
            }
        }
        if let Some(y) = Self::truth(&b) {
            match op {
                BinOp::And => return if y { Ok(a) } else { self.boolean(e, false) },
                BinOp::Or => return if y { self.boolean(e, true) } else { Ok(a) },
                BinOp::Implies if y => return self.boolean(e, true),
                BinOp::Implies => {
                    return self.node(e, Kind::Unary(UnOp::Not, Arc::clone(&a)), false, &[a])
                }
                _ => {}
            }
        }
        if let (Some(x), Some(y)) = (Self::int(&a), Self::int(&b)) {
            // Prepay conservative operand/result limb work before BigInt work.
            let bits = x
                .bits()
                .checked_add(y.bits())
                .and_then(|n| n.checked_add(128))
                .ok_or_else(|| {
                    refusal(
                        "bit-vector-budget",
                        "effective integer operation overflow",
                        e.span,
                    )
                })?;
            let limbs_x = x.bits() / 32 + 1;
            let limbs_y = y.bits() / 32 + 1;
            let paid = limbs_x
                .checked_mul(limbs_y)
                .and_then(|n| n.checked_add(bits / 32 + 16))
                .ok_or_else(|| {
                    refusal(
                        "bit-vector-budget",
                        "effective integer operation oversized",
                        e.span,
                    )
                })?;
            self.debit(
                e,
                usize::try_from(paid).map_err(|_| {
                    refusal(
                        "bit-vector-budget",
                        "effective integer operation oversized",
                        e.span,
                    )
                })?,
            )?;
            let value = match op {
                BinOp::Eq => return self.boolean(e, x == y),
                BinOp::Ne => return self.boolean(e, x != y),
                BinOp::Lt => return self.boolean(e, x < y),
                BinOp::Le => return self.boolean(e, x <= y),
                BinOp::Gt => return self.boolean(e, x > y),
                BinOp::Ge => return self.boolean(e, x >= y),
                BinOp::Add => Some(x + y),
                BinOp::Sub => Some(x - y),
                BinOp::Mul => Some(x * y),
                BinOp::Div | BinOp::Rem if y != &zero => {
                    let mut q = x / y;
                    let mut r = x % y;
                    if r < zero {
                        if y > &zero {
                            q -= &one;
                            r += y;
                        } else {
                            q += &one;
                            r -= y;
                        }
                    }
                    Some(if op == BinOp::Div { q } else { r })
                }
                BinOp::BitAnd => Some(x & y),
                BinOp::BitOr => Some(x | y),
                BinOp::BitXor => Some(x ^ y),
                BinOp::Shr => {
                    if let Ok(n) = u128::try_from(y) {
                        if n > 200_000 {
                            Some(if x < &zero { -&one } else { zero.clone() })
                        } else {
                            Some(x >> n as usize)
                        }
                    } else {
                        None
                    }
                }
                // Pinned shl constant evaluation first uses i128/u128 then
                // width truncation, and gives up for default pointer widths.
                BinOp::Shl => {
                    let range = self.ty(e, &e.ty)?.int_range();
                    if let (Some(range), Ok(n)) = (range, u128::try_from(y)) {
                        let raw = if range.is_signed_machine() {
                            i128::try_from(x).ok().map(|v| {
                                BigInt::from(if n >= 128 {
                                    0
                                } else {
                                    v.wrapping_shl(n as u32)
                                })
                            })
                        } else {
                            u128::try_from(x).ok().map(|v| {
                                BigInt::from(if n >= 128 {
                                    0
                                } else {
                                    v.wrapping_shl(n as u32)
                                })
                            })
                        };
                        match raw {
                            Some(value) => self.truncate_integer(e, value, range)?,
                            None => None,
                        }
                    } else {
                        None
                    }
                }
                _ => None,
            };
            if let Some(value) = value {
                return self.integer(e, value);
            }
        }
        if let Some(x) = Self::int(&a) {
            if x == &zero {
                match op {
                    BinOp::Add | BinOp::BitOr => return Ok(b),
                    BinOp::Mul | BinOp::BitAnd => return self.integer(e, zero),
                    _ => {}
                }
            }
            if x == &one && op == BinOp::Mul {
                return Ok(b);
            }
        }
        if let Some(y) = Self::int(&b) {
            if y == &zero {
                match op {
                    BinOp::Add | BinOp::Sub | BinOp::BitOr => return Ok(a),
                    BinOp::Mul | BinOp::BitAnd => return self.integer(e, zero),
                    _ => {}
                }
            }
            if y == &one {
                match op {
                    BinOp::Mul | BinOp::Div => return Ok(a),
                    BinOp::Rem => return self.integer(e, zero),
                    _ => {}
                }
            }
        }
        let intrinsic =
            op == BinOp::Shl && self.ty(e, &e.ty)?.int_range().is_some_and(Self::pointer);
        self.node(
            e,
            Kind::Binary(op, Arc::clone(&a), Arc::clone(&b)),
            intrinsic,
            &[a, b],
        )
    }
}

pub(super) fn consumed(ctx: &Ctx<'_>, requires: &[&Expr], goal: &Expr, pay: &mut usize) -> R<bool> {
    let mut observe = Observe {
        ctx,
        pay,
        bound: HashMap::new(),
        types: vec![],
        stack: vec![],
        next: 0,
    };
    let mut consumed = false;
    for expr in requires.iter().copied().chain(std::iter::once(goal)) {
        let effective = observe.go(expr, 0)?;
        // Source conversion refuses only a RETAINED default MIN/MAX node.
        // Its actual native source span is carried through normalization;
        // folded/unused/absorbed nodes confer neither refusal nor width use.
        if let Some(span) = effective.unsupported {
            return Err(refusal(
                "bit-vector-expression",
                "a retained pointer MIN/MAX bound unsupported by pinned BV conversion",
                span,
            ));
        }
        consumed |= effective.consumed;
    }
    Ok(consumed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{IntLit, SpanId};
    fn lit(n: u128, range: IntRange) -> Expr {
        Expr::new(
            Ty::Int(range),
            SpanId(0),
            ExprKind::Lit(Lit::Int(IntLit {
                negative: false,
                magnitude: n,
            })),
        )
    }
    fn read(n: u32, range: IntRange) -> Expr {
        Expr::read(Place::local(LocalId(n)), Ty::Int(range), SpanId(0))
    }
    fn eq(a: Expr, b: Expr) -> Expr {
        Expr::binary(BinOp::Eq, a, b, Ty::Bool, SpanId(0))
    }
    fn primitive(value: crate::IntegerConstant) -> Expr {
        Expr::new(
            Ty::Int(IntRange::U(32)),
            SpanId(0),
            ExprKind::IntegerConstant(value),
        )
    }
    fn observes(goal: &Expr, requires: &[&Expr]) -> bool {
        let mut krate = crate::VcCrate::new("effective source control");
        krate.architecture = crate::bitvector::Architecture::Either32Or64;
        let ctx = Ctx::new(&krate);
        let mut pay = 200_000;
        consumed(&ctx, requires, goal, &mut pay).unwrap()
    }
    #[test]
    fn unused_pointer_declaration_and_pointer_literals_are_not_consumption() {
        let mut krate = crate::VcCrate::new("unused pointer");
        krate.architecture = crate::bitvector::Architecture::Either32Or64;
        let ctx = Ctx::new(&krate);
        let mut pay = 200_000;
        assert!(!consumed(
            &ctx,
            &[],
            &eq(lit(0, IntRange::USize), lit(1, IntRange::USize)),
            &mut pay
        )
        .unwrap());
        assert!(!observes(
            &eq(read(1, IntRange::U(8)), lit(1, IntRange::U(8))),
            &[]
        ));
    }
    #[test]
    fn actual_pointer_place_consumes_but_tautological_requirement_does_not() {
        let pointer = read(1, IntRange::USize);
        assert!(observes(&eq(pointer.clone(), lit(0, IntRange::USize)), &[]));
        let tautology = eq(pointer.clone(), pointer);
        assert!(!observes(&Expr::bool_lit(false, SpanId(0)), &[&tautology]));
    }
    #[test]
    fn default_literal_cast_folds_only_when_in_range_for_both_widths() {
        let small =
            lit(0, IntRange::U(8)).cast(crate::CastKind::As, Ty::Int(IntRange::USize), SpanId(0));
        let large = lit(1u128 << 32, IntRange::U(64)).cast(
            crate::CastKind::As,
            Ty::Int(IntRange::USize),
            SpanId(0),
        );
        assert!(!observes(&eq(small, lit(1, IntRange::USize)), &[]));
        assert!(observes(&eq(large, lit(0, IntRange::USize)), &[]));
    }
    #[test]
    fn width_constant_with_fixed_result_and_only_requirement_specialize() {
        let bound = eq(
            primitive(crate::IntegerConstant::WordBits),
            lit(0, IntRange::U(32)),
        );
        assert!(observes(&bound, &[]));
        assert!(observes(&Expr::bool_lit(false, SpanId(0)), &[&bound]));
        assert!(!observes(
            &eq(
                primitive(crate::IntegerConstant::Minimum(IntRange::USize)),
                lit(1, IntRange::USize)
            ),
            &[]
        ));
    }
    #[test]
    fn absorbed_and_short_circuited_width_use_is_discarded() {
        let pointer = eq(read(1, IntRange::USize), lit(0, IntRange::USize));
        let dead = Expr::binary(
            BinOp::And,
            Expr::bool_lit(false, SpanId(0)),
            pointer.clone(),
            Ty::Bool,
            SpanId(0),
        );
        let requires = Expr::binary(
            BinOp::Or,
            Expr::bool_lit(true, SpanId(0)),
            pointer,
            Ty::Bool,
            SpanId(0),
        );
        assert!(!observes(&dead, &[]));
        assert!(!observes(&Expr::bool_lit(false, SpanId(0)), &[&requires]));
    }
    #[test]
    fn source_constant_rules_remove_width_before_native_translation() {
        let pointer = read(1, IntRange::USize);
        let xor = Expr::binary(
            BinOp::BitXor,
            pointer.clone(),
            pointer.clone(),
            Ty::Int(IntRange::USize),
            SpanId(0),
        );
        assert!(!observes(&eq(xor, lit(1, IntRange::USize)), &[]));
        let zero = Expr::binary(
            BinOp::Mul,
            lit(0, IntRange::USize),
            pointer,
            Ty::Int(IntRange::USize),
            SpanId(0),
        );
        assert!(!observes(&eq(zero, lit(1, IntRange::USize)), &[]));
    }
    #[test]
    fn pointer_binder_disappears_only_when_its_effective_body_is_literal() {
        let variable = read(2, IntRange::USize);
        let tautology = eq(variable.clone(), variable.clone());
        let quantified = |body| {
            Expr::new(
                Ty::Bool,
                SpanId(0),
                ExprKind::Quant {
                    kind: QuantKind::Forall,
                    vars: vec![(LocalId(2), Ty::Int(IntRange::USize))],
                    triggers: vec![],
                    body: Box::new(body),
                },
            )
        };
        assert!(!observes(&quantified(tautology), &[]));
        assert!(observes(
            &quantified(eq(variable, lit(0, IntRange::USize))),
            &[]
        ));
    }
    #[test]
    fn low_remaining_original_grant_refuses_instead_of_defaulting_diagnostic() {
        let krate = crate::VcCrate::new("held diagnostic grant");
        let ctx = Ctx::new(&krate);
        let mut pay = 0;
        assert!(consumed(&ctx, &[], &Expr::bool_lit(false, SpanId(0)), &mut pay).is_err());
        assert_eq!(pay, 0);
    }
    #[test]
    fn retained_default_pointer_max_is_refused_but_erased_identical_bounds_are_not() {
        let maximum = primitive(crate::IntegerConstant::Maximum(IntRange::USize));
        let mut krate = crate::VcCrate::new("retained pointer bound refusal");
        krate.architecture = crate::bitvector::Architecture::Either32Or64;
        let ctx = Ctx::new(&krate);
        let mut pay = 200_000;
        assert!(consumed(
            &ctx,
            &[],
            &eq(maximum.clone(), lit(0, IntRange::USize)),
            &mut pay
        )
        .is_err());
        let tautology = eq(maximum.clone(), maximum);
        let mut pay = 200_000;
        assert!(!consumed(
            &ctx,
            &[&tautology],
            &Expr::bool_lit(false, SpanId(0)),
            &mut pay
        )
        .unwrap());
    }

    #[test]
    fn constant_pointer_shift_folds_before_width_resolution_when_both_images_agree() {
        let shifted = Expr::binary(
            BinOp::Shl,
            lit(1, IntRange::USize),
            lit(1, IntRange::USize),
            Ty::Int(IntRange::USize),
            SpanId(0),
        );
        assert!(!observes(&eq(shifted, lit(0, IntRange::USize)), &[]));
        let shifted = Expr::binary(
            BinOp::Shl,
            lit(1, IntRange::USize),
            lit(32, IntRange::USize),
            Ty::Int(IntRange::USize),
            SpanId(0),
        );
        assert!(observes(&eq(shifted, lit(0, IntRange::USize)), &[]));
    }
    #[test]
    fn late_integer_work_uses_the_remaining_grant_without_a_fresh_allowance() {
        let krate = crate::VcCrate::new("paid constant payload");
        let ctx = Ctx::new(&krate);
        let expression = Expr::binary(
            BinOp::Mul,
            lit(1u128 << 127, IntRange::U(128)),
            lit(1u128 << 127, IntRange::U(128)),
            Ty::Int(IntRange::Nat),
            SpanId(0),
        );
        let mut enough = 200_000;
        let mut observer = Observe {
            ctx: &ctx,
            pay: &mut enough,
            bound: HashMap::new(),
            types: vec![],
            stack: vec![],
            next: 0,
        };
        let actual = observer.go(&expression, 0).unwrap();
        assert!(matches!(&actual.kind,Kind::Int(i) if i.bits()==255));
        let spent = 200_000 - enough;
        assert!(
            spent > 64,
            "this reaches beyond the initial node/literal census"
        );
        let mut low = spent - 1;
        let mut observer = Observe {
            ctx: &ctx,
            pay: &mut low,
            bound: HashMap::new(),
            types: vec![],
            stack: vec![],
            next: 0,
        };
        assert!(observer.go(&expression, 0).is_err());
        assert!(
            low < 8,
            "late publication must not refill the original grant"
        );
    }

    #[test]
    fn an_empty_crate_retains_fixed64_rules_for_all_four_constant_cases() {
        let krate = crate::VcCrate::new("fixed64 context counter-control");
        assert_eq!(krate.pointer_width, 64);
        assert!(matches!(
            krate.architecture,
            crate::bitvector::Architecture::Exactly(64)
        ));
        let ctx = Ctx::new(&krate);
        assert_eq!(ctx.pointer_width, 64);
        assert!(matches!(
            ctx.architecture,
            crate::bitvector::Architecture::Exactly(64)
        ));
        let large = lit(1u128 << 32, IntRange::U(64)).cast(
            crate::CastKind::As,
            Ty::Int(IntRange::USize),
            SpanId(0),
        );
        let shifted = Expr::binary(
            BinOp::Shl,
            lit(1, IntRange::USize),
            lit(32, IntRange::USize),
            Ty::Int(IntRange::USize),
            SpanId(0),
        );
        let maximum = Expr::new(
            Ty::Int(IntRange::USize),
            SpanId(0),
            ExprKind::IntegerConstant(crate::IntegerConstant::Maximum(IntRange::USize)),
        );
        let goals = [
            eq(large, lit(0, IntRange::USize)),
            eq(
                primitive(crate::IntegerConstant::WordBits),
                lit(0, IntRange::U(32)),
            ),
            eq(maximum, lit(0, IntRange::USize)),
            eq(shifted, lit(0, IntRange::USize)),
        ];
        let mut pay = 200_000;
        for goal in goals {
            assert!(!consumed(&ctx, &[], &goal, &mut pay).unwrap());
        }
    }

    #[test]
    fn explicit_default_and_fixed_contexts_keep_pointer_bound_policies_separate() {
        use crate::bitvector::Architecture;
        for architecture in [
            Architecture::Either32Or64,
            Architecture::Exactly(32),
            Architecture::Exactly(64),
        ] {
            let mut krate = crate::VcCrate::new("explicit bound context counter-control");
            krate.architecture = architecture;
            if let Architecture::Exactly(width) = architecture {
                krate.pointer_width = width;
            }
            let ctx = Ctx::new(&krate);
            let mut pay = 200_000;
            for (constant, range) in [
                (
                    crate::IntegerConstant::Maximum(IntRange::USize),
                    IntRange::USize,
                ),
                (
                    crate::IntegerConstant::Minimum(IntRange::ISize),
                    IntRange::ISize,
                ),
                (
                    crate::IntegerConstant::Maximum(IntRange::ISize),
                    IntRange::ISize,
                ),
            ] {
                let bound = Expr::new(
                    Ty::Int(range),
                    SpanId(0),
                    ExprKind::IntegerConstant(constant),
                );
                let goal = eq(bound, lit(0, range));
                let outcome = consumed(&ctx, &[], &goal, &mut pay);
                if architecture == Architecture::Either32Or64 {
                    assert!(outcome.is_err());
                } else {
                    assert!(!outcome.unwrap());
                }
            }
            let word_bits = eq(
                primitive(crate::IntegerConstant::WordBits),
                lit(0, IntRange::U(32)),
            );
            assert_eq!(
                consumed(&ctx, &[], &word_bits, &mut pay).unwrap(),
                architecture == Architecture::Either32Or64
            );
        }
    }
}
