// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Bounded structural observations. These values have no native authority.

use std::collections::BTreeMap;

use serde_json::{json, Value};
use trust_vc_vcir::{
    BinOp, Block, Body, CastKind, Expr, ExprKind, FnDecl, FnId, FnKind, FnRole, IntRange, Lit,
    Place, Projection, SpanId, Stmt, StmtKind, Ty, UnOp,
};

pub(super) struct Budget {
    nodes: usize,
    bytes: usize,
}

impl Budget {
    pub(super) fn new() -> Self {
        Self {
            nodes: 16_384,
            bytes: 1_048_576,
        }
    }
    pub(super) fn charge(
        &mut self,
        nodes: usize,
        bytes: usize,
        depth: usize,
    ) -> Result<(), String> {
        if depth > 64 {
            return Err("client footprint nesting exceeded its bound".into());
        }
        self.nodes = self
            .nodes
            .checked_sub(nodes)
            .ok_or("client footprint node bound exhausted")?;
        self.bytes = self
            .bytes
            .checked_sub(bytes)
            .ok_or("client footprint byte bound exhausted")?;
        Ok(())
    }
    pub(super) fn text(&mut self, text: &str) -> Result<String, String> {
        self.charge(0, text.len(), 0)?;
        Ok(text.to_owned())
    }
}

pub(super) fn id(id: FnId) -> Value {
    json!({"hi": format!("{:016x}", id.0.hi), "lo": format!("{:016x}", id.0.lo)})
}

pub(super) fn role(role: FnRole) -> &'static str {
    match role {
        FnRole::Item => "Item",
        FnRole::Instance => "Instance",
        FnRole::TraitDecl => "TraitDecl",
        FnRole::Imported => "Imported",
    }
}

fn binary(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "Add",
        BinOp::Sub => "Sub",
        BinOp::Mul => "Mul",
        BinOp::Div => "Div",
        BinOp::Rem => "Rem",
        BinOp::Eq => "Eq",
        BinOp::Ne => "Ne",
        BinOp::Lt => "Lt",
        BinOp::Le => "Le",
        BinOp::Gt => "Gt",
        BinOp::Ge => "Ge",
        BinOp::And => "And",
        BinOp::Or => "Or",
        BinOp::Implies => "Implies",
        BinOp::BitAnd => "BitAnd",
        BinOp::BitOr => "BitOr",
        BinOp::BitXor => "BitXor",
        BinOp::Shl => "Shl",
        BinOp::Shr => "Shr",
    }
}

pub(super) fn ty(ty: &Ty, budget: &mut Budget, depth: usize) -> Result<Value, String> {
    budget.charge(1, 64, depth)?;
    Ok(match ty {
        Ty::Bool => json!({"kind": "Bool"}),
        Ty::Unit => json!({"kind": "Unit"}),
        Ty::Int(range) => json!({"kind": "Integer", "range": match range {
            IntRange::Int => "Int", IntRange::Nat => "Nat", IntRange::U(_) => "Unsigned",
            IntRange::I(_) => "Signed", IntRange::USize => "USize", IntRange::ISize => "ISize",
            IntRange::Char => "Char" }, "bits": match range {
                IntRange::U(bits) | IntRange::I(bits) => Some(*bits), _ => None }}),
        Ty::Param(index) => json!({"kind": "Parameter", "index": index}),
        Ty::Ref { mutable, inner } => json!({"kind": "Reference", "mutable": mutable,
            "inner": self::ty(inner, budget, depth + 1)?}),
        Ty::MutRef(inner) => json!({"kind": "MutableReferenceCarrier",
            "inner": self::ty(inner, budget, depth + 1)?}),
        Ty::Tuple(elements) => {
            json!({"kind": "Tuple", "elements": types(elements, budget, depth + 1)?})
        }
        Ty::Adt(adt, args) => json!({"kind": "Nominal", "id": id(FnId(adt.0)),
            "arguments": types(args, budget, depth + 1)?}),
        Ty::Projection(..) => return Err(
            "client footprint has no live associated-type declaration inventory".into()
        ),
    })
}

pub(super) fn types(
    values: &[Ty],
    budget: &mut Budget,
    depth: usize,
) -> Result<Vec<Value>, String> {
    budget.charge(values.len(), 0, depth)?;
    values
        .iter()
        .map(|value| ty(value, budget, depth))
        .collect()
}

pub(super) fn signature(decl: &FnDecl, budget: &mut Budget) -> Result<Value, String> {
    if decl.attrs.broadcast_triggers.is_some() {
        return Err("client footprint does not represent broadcast contract authority".into());
    }
    if matches!(
        decl.unwind,
        Some(trust_vc_vcir::UnwindSpec::NoUnwindWhen(_))
    ) {
        return Err(
            "client footprint does not yet represent conditional unwind header scopes".into(),
        );
    }
    budget.charge(
        decl.locals.len() + decl.params.len() + decl.type_params.len(),
        0,
        0,
    )?;
    let params = decl
        .params
        .iter()
        .map(|id| {
            let local = decl
                .locals
                .get(id.index())
                .ok_or("footprint parameter is outside its declaration")?;
            Ok(json!({"local": id.0, "mode": local.mode.name(), "type": ty(&local.ty, budget, 0)?}))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let ret = decl
        .locals
        .get(decl.ret.index())
        .ok_or("footprint return is outside its declaration")?;
    Ok(
        json!({"id": id(decl.id), "role": role(decl.role), "mode": decl.mode.name(),
        "kind": match decl.kind { FnKind::Function => "Function", FnKind::ConstFunction => "ConstFunction",
            FnKind::Constant(_) => "Constant", FnKind::Static => "Static" },
        "type_parameter_count": decl.type_params.len(),
        "body": match &decl.body { Body::None => "None", Body::Spec(_) => "Spec", Body::Stmts(_) => "Statements", Body::Constant(_) => "Constant" },
        "headers": {"requires": decl.requires.len(), "ensures": decl.ensures.len(),
            "recommends": decl.recommends.len(), "decreases": decl.decreases.len(),
            "decreases_when": decl.decreases_when.is_some(), "decreases_by": decl.decreases_by.is_some()},
        "instance_metadata": decl.attrs.instance.is_some(),
        "prophetic": decl.attrs.prophetic,
        "unwind": {"declared": decl.unwind.is_some(), "kind": match decl.unwind_spec() {
            trust_vc_vcir::UnwindSpec::NoUnwind => "NoUnwind",
            trust_vc_vcir::UnwindSpec::MayUnwind => "MayUnwind",
            trust_vc_vcir::UnwindSpec::NoUnwindWhen(_) => "NoUnwindWhen"}},
        "parameters": params, "return": {"local": decl.ret.0, "mode": ret.mode.name(),
            "type": ty(&ret.ty, budget, 0)?}}),
    )
}

pub(super) struct Call {
    pub(super) callee: FnId,
    pub(super) span: SpanId,
    pub(super) value: Value,
}

pub(super) struct Walk<'a> {
    declarations: &'a BTreeMap<FnId, &'a FnDecl>,
    function: &'a FnDecl,
    pub(super) calls: Vec<Call>,
    pub(super) assertions: Vec<Value>,
    assertion: Option<usize>,
}

impl<'a> Walk<'a> {
    pub(super) fn new(function: &'a FnDecl, declarations: &'a BTreeMap<FnId, &'a FnDecl>) -> Self {
        Self {
            declarations,
            function,
            calls: Vec::new(),
            assertions: Vec::new(),
            assertion: None,
        }
    }

    fn place(&self, place: &Place, budget: &mut Budget) -> Result<Value, String> {
        budget.charge(place.projections.len() + 1, 64, 0)?;
        if self.function.locals.get(place.local.index()).is_none() {
            return Err("footprint read names an absent local".into());
        }
        let projections = place
            .projections
            .iter()
            .map(|projection| match projection {
                Projection::Deref => json!({"kind": "Deref"}),
                Projection::Field { variant, field } => {
                    json!({"kind": "Field", "variant": variant, "field": field})
                }
                Projection::TupleField(field) => json!({"kind": "TupleField", "field": field}),
            })
            .collect::<Vec<_>>();
        Ok(json!({"local": place.local.0, "projections": projections}))
    }

    fn call(
        &mut self,
        callee: FnId,
        type_args: &[Ty],
        args: &[Expr],
        span: SpanId,
        budget: &mut Budget,
        depth: usize,
    ) -> Result<Value, String> {
        let decl = self
            .declarations
            .get(&callee)
            .copied()
            .ok_or("footprint call has no declaration")?;
        if type_args.len() != decl.type_params.len() || args.len() != decl.params.len() {
            return Err(
                "footprint call does not retain its complete declared argument vectors".into(),
            );
        }
        let arguments = args
            .iter()
            .map(|arg| self.expr(arg, budget, depth + 1))
            .collect::<Result<Vec<_>, _>>()?;
        budget.charge(1, 128, depth)?;
        let index = self.calls.len();
        self.calls.push(Call { callee, span, value: json!({"index": index, "callee": id(callee),
            "declaration_role": role(decl.role), "assertion": self.assertion,
            "signature": signature(decl, budget)?, "type_arguments": types(type_args, budget, depth + 1)?,
            "value_arguments": arguments}) });
        Ok(json!({"kind": "Call", "index": index}))
    }

    fn expr(&mut self, expr: &Expr, budget: &mut Budget, depth: usize) -> Result<Value, String> {
        budget.charge(1, 64, depth)?;
        let value = match &expr.kind {
            ExprKind::Lit(value) => json!({"kind": "Literal", "value": match value {
                Lit::Bool(value) => json!({"kind": "Bool", "value": value}),
                Lit::Unit => json!({"kind": "Unit"}),
                Lit::Int(value) => json!({"kind": "Integer", "negative": value.negative,
                    "magnitude_decimal": value.magnitude.to_string()}),
            }}),
            ExprKind::Read(place) | ExprKind::Old(place) => json!({"kind":
                if matches!(&expr.kind, ExprKind::Old(_)) { "Old" } else { "Read" },
                "place": self.place(place, budget)?}),
            ExprKind::Unary { op, arg, check } => {
                json!({"kind": "Unary", "operator": match op { UnOp::Not => "Not", UnOp::Neg => "Neg" },
                "check": check.map(|id| id.0), "argument": self.expr(arg, budget, depth + 1)?})
            }
            ExprKind::Binary {
                op,
                lhs,
                rhs,
                check,
            } => json!({"kind": "Binary", "operator": binary(*op),
                "check": check.map(|id| id.0), "left": self.expr(lhs, budget, depth + 1)?,
                "right": self.expr(rhs, budget, depth + 1)?}),
            ExprKind::Cast { arg, kind } => {
                json!({"kind": "Cast", "conversion": match kind { CastKind::Exact => "Exact", CastKind::As => "As" },
                "argument": self.expr(arg, budget, depth + 1)?})
            }
            ExprKind::Call {
                callee,
                type_args,
                args,
            } => self.call(*callee, type_args, args, expr.span, budget, depth + 1)?,
            ExprKind::Borrow(arg) => {
                json!({"kind": "Borrow", "argument": self.expr(arg, budget, depth + 1)?})
            }
            ExprKind::MutRefCurrent(arg)
            | ExprKind::MutRefFuture(arg)
            | ExprKind::HasResolved(arg) => {
                let kind = match &expr.kind {
                    ExprKind::MutRefCurrent(_) => "MutRefCurrent",
                    ExprKind::MutRefFuture(_) => "MutRefFuture",
                    _ => "HasResolved",
                };
                json!({"kind": kind, "argument": self.expr(arg, budget, depth + 1)?})
            }
            ExprKind::MutRefUpdate { reference, value } => json!({"kind": "MutRefUpdate",
                "reference": self.expr(reference, budget, depth + 1)?,
                "value": self.expr(value, budget, depth + 1)?}),
            ExprKind::Field {
                base,
                variant,
                field,
            } => json!({"kind": "Field", "variant": variant,
                "field": field, "base": self.expr(base, budget, depth + 1)?}),
            ExprKind::IsVariant { base, variant } => {
                json!({"kind": "IsVariant", "variant": variant,
                "base": self.expr(base, budget, depth + 1)?})
            }
            ExprKind::TupleField { base, index } => json!({"kind": "TupleField", "index": index,
                "base": self.expr(base, budget, depth + 1)?}),
            ExprKind::If {
                cond,
                then_expr,
                else_expr,
            } => json!({"kind": "If",
                "condition": self.expr(cond, budget, depth + 1)?,
                "then": self.expr(then_expr, budget, depth + 1)?, "else": self.expr(else_expr, budget, depth + 1)?}),
            ExprKind::Let { local, value, body } => {
                self.place(&Place::local(*local), budget)?;
                json!({"kind": "Let", "local": local.0, "value": self.expr(value, budget, depth + 1)?,
                    "body": self.expr(body, budget, depth + 1)?})
            }
            ExprKind::Tuple(args) | ExprKind::Ctor { fields: args, .. } => {
                let values = args
                    .iter()
                    .map(|arg| self.expr(arg, budget, depth + 1))
                    .collect::<Result<Vec<_>, _>>()?;
                match &expr.kind {
                    ExprKind::Ctor { adt, variant, .. } => json!({"kind": "Constructor",
                        "nominal": id(FnId(adt.0)), "variant": variant, "fields": values}),
                    _ => json!({"kind": "Tuple", "elements": values}),
                }
            }
            ExprKind::IntegerConstant(_) => {
                return Err("client footprint does not yet represent architecture constants".into())
            }
            ExprKind::UntriggeredQuant { .. } | ExprKind::UntriggeredChoose { .. } => {
                return Err(
                    "client footprint cannot contain incomplete source construction".into(),
                );
            }
            ExprKind::ProofInSpec(_)
            | ExprKind::ProofInSpecTail { .. }
            | ExprKind::Quant { .. }
            | ExprKind::Choose { .. } => {
                return Err("client footprint does not yet represent embedded proof, quantifier or choice scopes".into());
            }
        };
        Ok(
            json!({"span": expr.span.0, "type": ty(&expr.ty, budget, depth + 1)?, "expression": value}),
        )
    }

    fn stmt(&mut self, stmt: &Stmt, budget: &mut Budget, depth: usize) -> Result<Value, String> {
        budget.charge(1, 64, depth)?;
        let value = match &stmt.kind {
            StmtKind::Assert { expr, site, .. } => {
                let index = self.assertions.len();
                self.assertions.push(Value::Null);
                let old = self.assertion.replace(index);
                let expression = self.expr(expr, budget, depth + 1)?;
                self.assertion = old;
                self.assertions[index] = json!({"index": index, "span": stmt.span.0,
                    "site": site.0, "condition": expression});
                json!({"kind": "Assert", "index": index})
            }
            StmtKind::Let { local, init } => json!({"kind": "Let", "local": local.0,
                "initial": init.as_ref().map(|expr| self.expr(expr, budget, depth + 1)).transpose()?}),
            StmtKind::LetChecked { local, init } => json!({"kind": "LetChecked", "local": local.0,
                "initial": self.expr(init, budget, depth + 1)?}),
            StmtKind::Assign { place, value } => {
                json!({"kind": "Assign", "place": self.place(place, budget)?,
                "value": self.expr(value, budget, depth + 1)?})
            }
            StmtKind::AssignSpec { place, value } => {
                json!({"kind": "AssignSpec", "place": self.place(place, budget)?,
                "value": self.expr(value, budget, depth + 1)?})
            }
            StmtKind::BorrowMut { dest, place } => {
                self.place(&Place::local(*dest), budget)?;
                json!({"kind": "BorrowMut", "destination": dest.0,
                    "place": self.place(place, budget)?})
            }
            StmtKind::Assume { expr, .. } => {
                json!({"kind": "Assume", "condition": self.expr(expr, budget, depth + 1)?})
            }
            StmtKind::Return { value, site } => json!({"kind": "Return", "site": site.0,
                "value": value.as_ref().map(|expr| self.expr(expr, budget, depth + 1)).transpose()?}),
            StmtKind::Call {
                callee,
                type_args,
                args,
                dest,
                site,
            } => json!({"kind": "StatementCall",
                "call": self.call(*callee, type_args, args, stmt.span, budget, depth + 1)?,
                "destination": dest.as_ref().map(|place| self.place(place, budget)).transpose()?, "site": site.0}),
            StmtKind::If {
                cond,
                then_block,
                else_block,
            } => json!({"kind": "If",
                "condition": self.expr(cond, budget, depth + 1)?,
                "then": self.block(then_block, budget, depth + 1)?,
                "else": self.block(else_block, budget, depth + 1)?}),
            StmtKind::IfSpec {
                cond,
                then_block,
                else_block,
            } => json!({"kind": "IfSpec",
                "condition": self.expr(cond, budget, depth + 1)?,
                "then": self.block(then_block, budget, depth + 1)?,
                "else": self.block(else_block, budget, depth + 1)?}),
            StmtKind::Block(block) | StmtKind::Ghost(block) => json!({"kind":
                if matches!(&stmt.kind, StmtKind::Ghost(_)) { "Ghost" } else { "Block" },
                "body": self.block(block, budget, depth + 1)?}),
            StmtKind::GhostTail { block, tail } => json!({"kind": "GhostTail",
                "body": self.block(block, budget, depth + 1)?,
                "tail": self.expr(tail, budget, depth + 1)?}),
            StmtKind::Unreachable => json!({"kind": "Unreachable"}),
            StmtKind::BroadcastUse { .. }
            | StmtKind::Reveal { .. }
            | StmtKind::AssertBitVector { .. }
            | StmtKind::Hide { .. }
            | StmtKind::Loop(_)
            | StmtKind::Break { .. }
            | StmtKind::Continue { .. } => {
                return Err(
                    "client footprint does not yet represent reveal, hide or loop scopes".into(),
                )
            }
        };
        Ok(json!({"span": stmt.span.0, "statement": value}))
    }

    fn block(
        &mut self,
        block: &Block,
        budget: &mut Budget,
        depth: usize,
    ) -> Result<Vec<Value>, String> {
        budget.charge(block.stmts.len(), 0, depth)?;
        block
            .stmts
            .iter()
            .map(|stmt| self.stmt(stmt, budget, depth))
            .collect()
    }

    pub(super) fn body(&mut self, budget: &mut Budget) -> Result<Value, String> {
        if !self.function.requires.is_empty()
            || !self.function.ensures.is_empty()
            || !self.function.recommends.is_empty()
            || !self.function.decreases.is_empty()
            || self.function.decreases_when.is_some()
            || self.function.decreases_by.is_some()
            || self.function.unwind.is_some()
        {
            return Err("client footprint does not yet represent function header scopes".into());
        }
        let function = self.function;
        match &function.body {
            Body::None => Ok(json!({"kind": "None"})),
            Body::Spec(expr) => Ok(json!({"kind": "Spec", "value": self.expr(expr, budget, 0)?})),
            Body::Constant(expr) => {
                Ok(json!({"kind": "Constant", "value": self.expr(expr, budget, 0)?}))
            }
            Body::Stmts(block) => {
                Ok(json!({"kind": "Statements", "statements": self.block(block, budget, 0)?}))
            }
        }
    }
}
