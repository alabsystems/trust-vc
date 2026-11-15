//! Expressions to values.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! [`Tr`] turns one VcIR expression into a [`Val`]. Locals are read through
//! a [`Reads`] table the caller fills for the context (a body, a
//! postcondition, a callee's clause at a call site, a spec function's
//! definition), so one translation serves all of them.
//!
//! Exec checks (overflow, division by zero) are not decided here. Each one
//! is returned as a [`PendingCheck`] carrying the condition and the guard
//! under which the operation is evaluated: the right operand of `&&` runs
//! only when the left one holds, the branches of `if` under their
//! condition. The caller checks them in evaluation order, which is the order
//! of the list.
//!
//! Arithmetic follows Verus's encoding. Spec `+ - *` and exact machine
//! results are integer terms; `/` and `%` are Euclidean. A product of two
//! non-constant values, and a quotient or remainder whose divisor is not a
//! non-zero constant, is an uninterpreted function (`nl_mul`, `nl_div`,
//! `nl_mod`) about which only Verus's own prelude axioms are known, because
//! Verus runs Z3 without nonlinear arithmetic. An `as` cast into a machine
//! type is Verus's clip (see `super::spec`).

use std::collections::{BTreeSet, HashMap};
use std::ops::{Neg, Not};

use crate::expr::{BinOp, CastKind, Expr, ExprKind, Lit, Place, Projection, QuantKind, UnOp};
use crate::ids::{FnId, LocalId, SiteId, SpanId};
use crate::item::AdtKind;
use crate::ty::{IntRange, Ty};

use super::quant;
use super::query::{Function, VcRefusal};
use super::spec::{self, SpecSig, NL_DIV, NL_MOD, NL_MUL};
use super::term::{ArithOp, Sort, Term};
use super::type_encoding::TypeEnv;
use super::val::{
    range_bounds, refusal, supported_range, Ctx, FormalPosition, FormalValue, LeafTy, Shape, Val,
};

mod recommendations;

pub(crate) type R<T> = Result<T, VcRefusal>;

/// Values of the locals an expression may read.
#[derive(Debug, Clone, Default)]
pub(crate) struct Reads {
    /// What `Read` of a local yields.
    pub(crate) read: HashMap<LocalId, Val>,
    /// What `Old` of a local yields.
    pub(crate) old: HashMap<LocalId, Val>,
    /// The term standing for each type parameter of the function the code
    /// belongs to. A spec function with type parameters takes one such
    /// term per type parameter before its value arguments, so its
    /// applications at different type arguments are different
    /// applications, as Verus's type arguments make them.
    pub(crate) types: TypeEnv,
}

/// The kind of an exec check found while translating.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PendingKind {
    Overflow,
    DivByZero,
    /// Auxiliary Spec-call domain diagnostic, never a normal obligation/fact.
    Recommendation {
        callee: FnId,
        clause: usize,
    },
    ChoiceRecommendation,
}

/// An exec check the caller must decide.
#[derive(Debug, Clone)]
pub(crate) struct PendingCheck {
    /// Fresh arbitrary typed source binders, local to auxiliary queries.
    pub(crate) diagnostic_symbols: Vec<(String, LeafTy)>,
    /// Conditions under which the operation is evaluated, beyond the path.
    pub(crate) guard: Vec<Term>,
    /// What must hold.
    pub(crate) cond: Term,
    pub(crate) kind: PendingKind,
    pub(crate) site: SiteId,
    pub(crate) span: SpanId,
}

/// A recursive call met while translating a spec function's body for its
/// termination check. Its value is fresh: Verus checks termination before
/// the function's definition exists, and gives the call's result only its
/// type (`recursion.rs`, `check_termination`).
#[derive(Debug, Clone)]
pub(crate) struct RecCall {
    pub(crate) callee: FnId,
    /// Conditions under which the call is evaluated.
    pub(crate) guard: Vec<Term>,
    /// The terms of its type arguments.
    pub(crate) types: TypeEnv,
    /// Its arguments.
    pub(crate) args: Vec<Val>,
    /// The symbols standing for its result, with their types.
    pub(crate) result: Vec<(String, LeafTy)>,
    pub(crate) span: SpanId,
}

/// A `proof { .. }` block met while translating a spec function's body
/// for its termination check: the `ordinal`-th one in evaluation order.
#[derive(Debug, Clone)]
pub(crate) struct ProofEvent {
    pub(crate) diagnostic_symbols: Vec<(String, LeafTy)>,
    pub(crate) ordinal: usize,
    /// Conditions under which it is evaluated.
    pub(crate) guard: Vec<Term>,
    /// The spec `let` bindings in scope there.
    pub(crate) bound: Vec<(LocalId, Val)>,
}

/// What a termination check walks, in evaluation order.
#[derive(Debug, Clone)]
pub(crate) enum RecEvent {
    Call(RecCall),
    Proof(ProofEvent),
    /// Kept in actual expression evaluation order relative to proof blocks.
    Diagnostic(PendingCheck),
}

/// Recursive calls and proof blocks to record rather than translate.
#[derive(Debug, Clone, Default)]
pub(crate) struct RecCalls {
    /// The functions whose calls are recursive.
    pub(crate) members: BTreeSet<FnId>,
    /// The calls and proof blocks met, in evaluation order.
    pub(crate) found: Vec<RecEvent>,
    /// How many proof blocks were met.
    pub(crate) proofs: usize,
}

/// One expression translation.
pub(crate) struct Tr<'a> {
    ctx: &'a Ctx<'a>,
    sigs: &'a HashMap<FnId, SpecSig>,
    functions: &'a [Function],
    reads: &'a Reads,
    /// Spec `let` bindings in scope, innermost last.
    bound: Vec<(LocalId, Val)>,
    /// The local guard of the subexpression being translated.
    guard: Vec<Term>,
    /// Exec checks found, in evaluation order.
    pub(crate) checks: Vec<PendingCheck>,
    /// Spec functions called.
    pub(crate) called: BTreeSet<FnId>,
    /// When set, the calls of these functions are recorded with a fresh
    /// result instead of being applications.
    pub(crate) rec_calls: Option<RecCalls>,
    /// Values standing for subexpressions, by address: the holes of a
    /// choice while its template is translated.
    holes: Vec<(*const Expr, Val)>,
    /// All nested checked-inline bodies share one finite translation grant.
    /// Ordinary non-inline expressions retain their existing admission path.
    inline_work: std::rc::Rc<std::cell::Cell<usize>>,
    inline_stack: Vec<FnId>,
    /// Enabled only by a separate failed-function diagnostic generation pass.
    recommendations: bool,
    /// Keeps the same auxiliary work grant active during skip-checks lowering.
    auxiliary_work: bool,
    recommendation_symbols: Vec<(String, LeafTy)>,
}

impl<'a> Tr<'a> {
    pub(crate) fn new(
        ctx: &'a Ctx<'a>,
        sigs: &'a HashMap<FnId, SpecSig>,
        functions: &'a [Function],
        reads: &'a Reads,
    ) -> Self {
        Self {
            ctx,
            sigs,
            functions,
            reads,
            bound: Vec::new(),
            guard: Vec::new(),
            checks: Vec::new(),
            called: BTreeSet::new(),
            rec_calls: None,
            holes: Vec::new(),
            inline_work: std::rc::Rc::new(std::cell::Cell::new(200_000)),
            inline_stack: Vec::new(),
            recommendations: false,
            auxiliary_work: false,
            recommendation_symbols: Vec::new(),
        }
    }

    pub(crate) fn with_recommendations(mut self, enabled: bool) -> Self {
        self.recommendations = enabled;
        self.auxiliary_work |= enabled;
        self
    }

    pub(crate) fn with_recommendation_work(
        mut self,
        work: std::rc::Rc<std::cell::Cell<usize>>,
    ) -> Self {
        if self.recommendations {
            self.inline_work = work;
        }
        self
    }

    /// Meter pure contract/value lowering in the auxiliary pass without
    /// enabling caller-side traversal of another declaration's domains.
    pub(crate) fn with_auxiliary_work(mut self, work: std::rc::Rc<std::cell::Cell<usize>>) -> Self {
        self.auxiliary_work = true;
        self.inline_work = work;
        self
    }

    /// Instantiate this actual selected Spec declaration's recommends at its
    /// already evaluated/adapted native arguments. This is a diagnostic goal,
    /// never an assumption or a guard for the Spec value definition.
    fn recommendation_checks(
        &mut self,
        call: &Expr,
        callee: FnId,
        reads: &Reads,
        specialized: Option<&[Ty]>,
    ) -> R<()> {
        if !self.recommendations {
            return Ok(());
        }
        let declaration = *self.ctx.fns.get(&callee).ok_or_else(|| {
            refusal(
                "vcgen-internal",
                "a missing recommendation declaration",
                call.span,
            )
        })?;
        if declaration.recommends.is_empty() {
            return Ok(());
        }
        for (index, clause) in declaration.recommends.iter().enumerate() {
            let expression = specialized
                .map(|types| {
                    super::inline_body::expression(self.ctx, &clause.expr, types, &self.inline_work)
                })
                .transpose()?;
            let mut child = Tr::new(self.ctx, self.sigs, self.functions, reads);
            child.inline_work = self.inline_work.clone();
            child.auxiliary_work = true;
            child.inline_stack = self.inline_stack.clone();
            // A caller checks the declared predicate, not the callee's
            // contract traversal. The source declaration owns nested-domain
            // checks (a40 sst_to_air1948, ast_to_sst_func935). No expansion of
            // a contract dependency cycle, and no failed goal becomes a fact.
            super::aux_work::expression(
                &self.inline_work,
                expression.as_ref().unwrap_or(&clause.expr),
                clause.span,
            )?;
            let condition = child.bool(expression.as_ref().unwrap_or(&clause.expr))?;
            if !child.checks.is_empty() {
                return Err(refusal(
                    "recommends-expression",
                    "an execution check inside a recommendation predicate",
                    clause.span,
                ));
            }
            self.called.extend(child.called);
            self.pending(
                PendingKind::Recommendation {
                    callee,
                    clause: index,
                },
                condition,
                SiteId(call.span.0),
                call.span,
            )?;
        }
        Ok(())
    }

    /// Translate a `bool` expression.
    pub(crate) fn bool(&mut self, e: &Expr) -> R<Term> {
        self.expr(e)?
            .into_leaf()
            .ok_or_else(|| refusal("vcgen-internal", "a condition that is not a scalar", e.span))
    }

    fn leaf(&mut self, e: &Expr) -> R<Term> {
        self.expr(e)?
            .into_leaf()
            .ok_or_else(|| refusal("vcgen-internal", "an operand that is not a scalar", e.span))
    }

    /// Translate `e` with `cond` added to the local guard.
    fn guarded<T>(&mut self, cond: Term, f: impl FnOnce(&mut Self) -> R<T>) -> R<T> {
        self.guard.push(cond);
        let out = f(self);
        self.guard.pop();
        out
    }

    fn pending(&mut self, kind: PendingKind, cond: Term, site: SiteId, span: SpanId) -> R<()> {
        if self.auxiliary_work || !self.inline_stack.is_empty() {
            for guard in &self.guard {
                super::inline_work::term(&self.inline_work, guard, 1, span)?;
            }
            for (name, _) in &self.recommendation_symbols {
                super::inline_work::items(&self.inline_work, name.len() + 1, span)?;
            }
        }
        let check = PendingCheck {
            diagnostic_symbols: self.recommendation_symbols.clone(),
            guard: self.guard.clone(),
            cond,
            kind,
            site,
            span,
        };
        if self.recommendations {
            if let Some(events) = &mut self.rec_calls {
                events.found.push(RecEvent::Diagnostic(check));
                return Ok(());
            }
        }
        self.checks.push(check);
        Ok(())
    }

    /// Translate one expression.
    pub(crate) fn expr(&mut self, e: &Expr) -> R<Val> {
        if self.auxiliary_work || !self.inline_stack.is_empty() {
            let remaining = self.inline_work.get().checked_sub(1).ok_or_else(|| {
                refusal(
                    "inline-size",
                    "checked inline-body translation exhausted",
                    e.span,
                )
            })?;
            self.inline_work.set(remaining);
        }
        if let Some((_, val)) = self.holes.iter().find(|(at, _)| std::ptr::eq(*at, e)) {
            if self.auxiliary_work || !self.inline_stack.is_empty() {
                super::inline_work::value(&self.inline_work, val, 1, e.span)?;
            }
            return Ok(val.clone());
        }
        match &e.kind {
            ExprKind::Lit(lit) => lit_val(*lit, e.span),
            ExprKind::IntegerConstant(value) => lit_val(
                Lit::Int(value.value(self.ctx.pointer_width).ok_or_else(|| {
                    refusal("integer-bound", "an unsupported primitive constant", e.span)
                })?),
                e.span,
            ),
            ExprKind::Read(place) => {
                let root = self
                    .bound
                    .iter()
                    .rev()
                    .find(|(local, _)| *local == place.local)
                    .map(|(_, val)| val)
                    .or_else(|| self.reads.read.get(&place.local))
                    .ok_or_else(|| {
                        refusal(
                            "vcgen-internal",
                            format!("a read of local {} that has no value here", place.local.0),
                            e.span,
                        )
                    })?;
                if self.auxiliary_work || !self.inline_stack.is_empty() {
                    super::inline_work::value(&self.inline_work, root, 2, e.span)?;
                }
                project(root, place, e.span)
            }
            ExprKind::Old(place) => {
                let root = self.reads.old.get(&place.local).ok_or_else(|| {
                    refusal(
                        "vcgen-internal",
                        format!(
                            "old() of local {} that has no entry value here",
                            place.local.0
                        ),
                        e.span,
                    )
                })?;
                if self.auxiliary_work || !self.inline_stack.is_empty() {
                    super::inline_work::value(&self.inline_work, root, 2, e.span)?;
                }
                project(root, place, e.span)
            }
            ExprKind::Unary { op, arg, check } => self.unary(e, *op, arg, *check),
            ExprKind::Binary {
                op,
                lhs,
                rhs,
                check,
            } => self.binary(e, *op, lhs, rhs, *check),
            ExprKind::If {
                cond,
                then_expr,
                else_expr,
            } => {
                let c = self.bool(cond)?;
                if self.auxiliary_work || !self.inline_stack.is_empty() {
                    super::inline_work::term(&self.inline_work, &c, 2, e.span)?;
                }
                let a = self.guarded(c.clone(), |tr| tr.expr(then_expr))?;
                let b = self.guarded(c.clone().not(), |tr| tr.expr(else_expr))?;
                if self.auxiliary_work || !self.inline_stack.is_empty() {
                    let leaves = super::inline_work::leaves(&self.inline_work, &a, e.span)?;
                    super::inline_work::term(&self.inline_work, &c, leaves, e.span)?;
                    super::inline_work::value(&self.inline_work, &a, 1, e.span)?;
                    super::inline_work::value(&self.inline_work, &b, 1, e.span)?;
                }
                Val::select(&c, &a, &b).ok_or_else(|| {
                    refusal("vcgen-internal", "if branches of different shapes", e.span)
                })
            }
            ExprKind::Let { local, value, body } => {
                let v = self.expr(value)?;
                self.bound.push((*local, v));
                let out = self.expr(body);
                self.bound.pop();
                out
            }
            ExprKind::Call {
                callee,
                type_args,
                args,
            } => {
                let (origin, type_args) = self.ctx.call_origin(*callee, type_args, e.span)?;
                self.called.insert(origin);
                let types = type_terms(self.ctx, origin, &type_args, &self.reads.types, e.span)?;
                self.spec_call(e, origin, &type_args, types, args)
            }
            ExprKind::Cast { arg, kind } => {
                let v = self.leaf(arg)?;
                let (Some(from), Some(to)) = (arg.ty.int_range(), e.ty.int_range()) else {
                    return Err(refusal("vcgen-internal", "a cast of a non-integer", e.span));
                };
                match kind {
                    CastKind::Exact => Ok(Val::Leaf(v)),
                    CastKind::As => Ok(Val::Leaf(clip(
                        from,
                        to,
                        v,
                        e.span,
                        self.ctx.pointer_width,
                    )?)),
                }
            }
            ExprKind::Ctor {
                adt,
                variant,
                fields,
            } => {
                if self
                    .ctx
                    .adts
                    .get(adt)
                    .is_some_and(|decl| decl.kind == AdtKind::Enum)
                {
                    self.ctx.register_enum(*adt, e.span)?;
                    let values = fields
                        .iter()
                        .map(|field| self.expr(field))
                        .collect::<Result<Vec<_>, _>>()?;
                    return self.ctx.construct_enum(
                        &e.ty,
                        &self.reads.types,
                        *variant,
                        values,
                        e.span,
                    );
                }
                let is_struct = self
                    .ctx
                    .adts
                    .get(adt)
                    .is_some_and(|decl| decl.kind == AdtKind::Struct);
                if !is_struct || *variant != 0 {
                    return Err(refusal("enum", "an enum value", e.span));
                }
                let mut children = Vec::new();
                for field in fields {
                    children.push(self.expr(field)?);
                }
                Ok(Val::Node(children))
            }
            ExprKind::IsVariant { base, variant } => {
                let value = self.expr(base)?;
                self.ctx
                    .test_enum(&base.ty, &self.reads.types, *variant, value, e.span)
            }
            ExprKind::Tuple(elems) => {
                let mut children = Vec::new();
                for elem in elems {
                    children.push(self.expr(elem)?);
                }
                Ok(Val::Node(children))
            }
            ExprKind::Field {
                base,
                variant,
                field,
            } => {
                let mut ty = &base.ty;
                while let Ty::Ref {
                    mutable: false,
                    inner,
                } = ty
                {
                    ty = inner;
                }
                if matches!(ty, Ty::Adt(id, _) if self.ctx.adts.get(id)
                    .is_some_and(|adt| adt.kind == AdtKind::Enum))
                {
                    let value = self.expr(base)?;
                    return self.ctx.project_enum(
                        &base.ty,
                        &self.reads.types,
                        *variant,
                        *field,
                        value,
                        e.span,
                    );
                }
                if *variant != 0 {
                    return Err(refusal("enum", "a field of an unsupported variant", e.span));
                }
                let base = self.expr(base)?;
                if self.auxiliary_work || !self.inline_stack.is_empty() {
                    super::inline_work::value(&self.inline_work, &base, 1, e.span)?;
                }
                base.child(*field)
                    .cloned()
                    .ok_or_else(|| refusal("vcgen-internal", "a field index out of range", e.span))
            }
            ExprKind::TupleField { base, index } => {
                let base = self.expr(base)?;
                if self.auxiliary_work || !self.inline_stack.is_empty() {
                    super::inline_work::value(&self.inline_work, &base, 1, e.span)?;
                }
                base.child(*index)
                    .cloned()
                    .ok_or_else(|| refusal("vcgen-internal", "a tuple index out of range", e.span))
            }
            // A shared reference is its referent.
            ExprKind::Borrow(inner) => self.expr(inner),
            // Proof code does not change a spec value; a termination check
            // walks it where it stands.
            ExprKind::ProofInSpec(_) => {
                if (self.auxiliary_work || !self.inline_stack.is_empty())
                    && self.rec_calls.is_some()
                {
                    for guard in &self.guard {
                        super::inline_work::term(&self.inline_work, guard, 1, e.span)?;
                    }
                    for (_, value) in &self.bound {
                        super::inline_work::value(&self.inline_work, value, 1, e.span)?;
                    }
                }
                if self.recommendations {
                    for (name, _) in &self.recommendation_symbols {
                        super::inline_work::items(&self.inline_work, name.len() + 1, e.span)?;
                    }
                }
                if let Some(rec) = self.rec_calls.as_mut() {
                    rec.found.push(RecEvent::Proof(ProofEvent {
                        diagnostic_symbols: self.recommendation_symbols.clone(),
                        ordinal: rec.proofs,
                        guard: self.guard.clone(),
                        bound: self.bound.clone(),
                    }));
                    rec.proofs += 1;
                }
                Ok(Val::unit())
            }
            ExprKind::Quant {
                kind,
                vars,
                triggers,
                body,
            } => self.quant(e, *kind, vars, triggers, body),
            ExprKind::Choose {
                vars,
                triggers,
                cond,
                result,
            } => self.choose(e, vars, triggers, cond, result),
            ExprKind::UntriggeredQuant { .. } | ExprKind::UntriggeredChoose { .. } => Err(refusal(
                "source-construction",
                "a binder without successfully inferred triggers",
                e.span,
            )),
        }
    }

    /// Refuse a recursive call inside a quantifier or choice of a body
    /// walked for its termination check.
    fn no_recursion_inside(&self, e: &Expr) -> R<()> {
        if let Some(rec) = &self.rec_calls {
            // An auxiliary SourceSpec records proof/diagnostic events but has
            // no recursive abstraction members. No scan can find a member.
            if rec.members.is_empty() {
                return Ok(());
            }
            if self.auxiliary_work || !self.inline_stack.is_empty() {
                super::aux_work::expression(&self.inline_work, e, e.span)?;
            }
            let recursive = e.any(&|sub| {
                let ExprKind::Call {
                    callee, type_args, ..
                } = &sub.kind
                else {
                    return false;
                };
                rec.members.contains(callee)
                    || self
                        .ctx
                        .call_origin(*callee, type_args, sub.span)
                        .is_ok_and(|(origin, _)| rec.members.contains(&origin))
            });
            if recursive {
                return Err(refusal(
                    "quantifier-recursion",
                    "a recursive call inside a quantifier or choice",
                    e.span,
                ));
            }
        }
        Ok(())
    }

    /// Bind `vars` to fresh variables named `qb<n>`; their scalar leaves.
    fn bind(&mut self, vars: &[(LocalId, Ty)], span: SpanId) -> R<Vec<(String, LeafTy)>> {
        let mut leaves = Vec::new();
        for (local, ty) in vars {
            let shape = self.ctx.shape(ty, self.reads.types.owner(), span)?;
            let val = self
                .ctx
                .quants
                .borrow_mut()
                .fresh_val(&shape, "qb", &mut leaves);
            self.bound.push((*local, val));
        }
        Ok(leaves)
    }

    /// The trigger groups as terms: each term an application, each group
    /// binding every leaf of the variables.
    fn trigger_terms(
        &mut self,
        triggers: &[Vec<Expr>],
        leaves: &[(String, LeafTy)],
        span: SpanId,
    ) -> R<Vec<Vec<Term>>> {
        let mut out = Vec::new();
        for group in triggers {
            let mut terms = Vec::new();
            let mut seen = Vec::new();
            for term in group {
                let t = self.leaf(term)?;
                if !matches!(t, Term::Call { .. }) {
                    return Err(refusal(
                        "trigger-term",
                        "a trigger that is not a function application",
                        term.span,
                    ));
                }
                if !quant::vars_in_order(&t, &mut seen) {
                    return Err(refusal(
                        "trigger-term",
                        "a trigger with inconsistent variable sorts",
                        term.span,
                    ));
                }
                terms.push(t);
            }
            let covered = leaves
                .iter()
                .all(|(name, _)| seen.iter().any(|(var, _)| var == name));
            if !covered {
                return Err(refusal(
                    "trigger-leaf",
                    "a trigger group that does not bind every scalar part of the variables",
                    span,
                ));
            }
            out.push(terms);
        }
        Ok(out)
    }

    fn quant_trigger_terms(
        &mut self,
        triggers: &[Vec<Expr>],
        leaves: &[(String, LeafTy)],
        span: SpanId,
    ) -> R<Vec<Vec<super::trigger_pattern::Pattern>>> {
        let mut out = Vec::new();
        for group in triggers {
            let mut terms = Vec::new();
            let mut seen = Vec::new();
            for term in group {
                let pattern = if let ExprKind::Cast {
                    arg,
                    kind: CastKind::As,
                } = &term.kind
                {
                    let value = self.leaf(arg)?;
                    let (Some(from), Some(to)) = (arg.ty.int_range(), term.ty.int_range()) else {
                        return Err(refusal(
                            "vcgen-internal",
                            "a cast of a non-integer",
                            term.span,
                        ));
                    };
                    if let Some(to) = cast_clip_range(from, to, term.span, self.ctx.pointer_width)?
                    {
                        spec::clip_pattern(to, value).map(super::trigger_pattern::Pattern::clipped)
                    } else {
                        match lowered_trigger_clip(arg, self.ctx.pointer_width)? {
                            Some(range) => {
                                super::trigger_pattern::Pattern::lowered_finite_clip(value, range)
                            }
                            None => super::trigger_pattern::Pattern::application(value),
                        }
                    }
                } else {
                    // Retain the actual body lowering, including its boxed
                    // integer operator and full finite clip. A bitwise result
                    // is not an alternate UF or a bare fallback proxy.
                    let value = self.leaf(term)?;
                    match lowered_trigger_clip(term, self.ctx.pointer_width)? {
                        Some(range) => {
                            super::trigger_pattern::Pattern::lowered_finite_clip(value, range)
                        }
                        None => super::trigger_pattern::Pattern::application(value),
                    }
                }
                .ok_or_else(|| {
                    refusal(
                        "trigger-term",
                        "a trigger without a supported typed application",
                        term.span,
                    )
                })?;
                if !quant::vars_in_order(pattern.term(), &mut seen) {
                    return Err(refusal(
                        "trigger-term",
                        "a trigger with inconsistent variable sorts",
                        term.span,
                    ));
                }
                terms.push(pattern);
            }
            let covered = leaves
                .iter()
                .all(|(name, _)| seen.iter().any(|(var, _)| var == name));
            if !covered {
                return Err(refusal(
                    "trigger-leaf",
                    "a trigger group that does not bind every scalar part of the variables",
                    span,
                ));
            }
            out.push(terms);
        }
        Ok(out)
    }

    /// A quantified formula: its atom (see `super::quant`).
    fn quant(
        &mut self,
        e: &Expr,
        kind: QuantKind,
        vars: &[(LocalId, Ty)],
        triggers: &[Vec<Expr>],
        body: &Expr,
    ) -> R<Val> {
        if self.auxiliary_work {
            super::aux_work::expression(&self.inline_work, e, e.span)?;
        }
        self.no_recursion_inside(e)?;
        if (self.reads.types.len() != 0 && self.inline_stack.is_empty())
            || vars.iter().any(|(_, ty)| ty.has_param())
        {
            return Err(refusal(
                "generic-quantifier",
                "a quantified typed Poly domain",
                e.span,
            ));
        }
        let depth = self.bound.len();
        let diagnostic_depth = self.recommendation_symbols.len();
        let translated = self.bind(vars, e.span).and_then(|leaves| {
            if self.recommendations {
                super::inline_work::items(&self.inline_work, leaves.len(), e.span)?;
                self.recommendation_symbols.extend(leaves.iter().cloned());
            }
            let body = self.bool(body)?;
            // Upstream does not check recommends in trigger hints.
            let enabled = self.recommendations;
            self.recommendations = false;
            let triggers = self.quant_trigger_terms(triggers, &leaves, e.span);
            self.recommendations = enabled;
            Ok((leaves, body, triggers?))
        });
        self.recommendation_symbols.truncate(diagnostic_depth);
        self.bound.truncate(depth);
        let (leaves, body, triggers) = translated?;
        if leaves
            .iter()
            .any(|(_, leaf)| matches!(leaf, LeafTy::Poly(_)))
        {
            return Err(refusal(
                "generic-quantifier",
                "a quantified typed Poly domain",
                e.span,
            ));
        }
        {
            // Inline expansion shares its existing grant; ordinary templates
            // retain their original per-template admission.
            let shared = self.auxiliary_work || !self.inline_stack.is_empty();
            let work = self.inline_work.clone();
            let mut left = 200_000usize;
            let mut pay = |cost| match (if shared { work.get() } else { left }).checked_sub(cost) {
                Some(next) => {
                    if shared {
                        work.set(next);
                    } else {
                        left = next;
                    }
                    true
                }
                None => false,
            };
            if !pay(1) {
                return Err(refusal(
                    "generic-quantifier",
                    "typed template work exhausted",
                    e.span,
                ));
            }
            let mut roots = vec![&body];
            for group in &triggers {
                if !pay(group.len().saturating_add(1)) {
                    return Err(refusal(
                        "generic-quantifier",
                        "typed template work exhausted",
                        e.span,
                    ));
                }
                for pattern in group {
                    if !pattern.valid_head(&mut pay) {
                        return Err(refusal(
                            "trigger-term",
                            "a malformed current typed application pattern",
                            e.span,
                        ));
                    }
                    roots.push(pattern.term());
                }
            }
            let vocabulary = super::closed_templates::Vocabulary::new(
                self.ctx,
                self.functions,
                self.sigs,
                &mut pay,
            )
            .ok_or_else(|| {
                refusal(
                    "generic-quantifier",
                    "an unavailable typed template vocabulary",
                    e.span,
                )
            })?;
            if !vocabulary.closed_environment(&self.reads.types, &mut pay) {
                return Err(refusal(
                    "generic-quantifier",
                    "an inline quantifier without a canonical closed type environment",
                    e.span,
                ));
            }
            let registry = self.ctx.quants.borrow();
            if !vocabulary.check(&registry, &roots, &leaves, &mut pay) {
                return Err(refusal(
                    "generic-quantifier",
                    "a boxed expression outside the checked concrete template",
                    e.span,
                ));
            }
        }
        let facts = Term::and(
            leaves
                .iter()
                .map(|(name, leaf)| leaf.fact(&Term::var(name.clone(), leaf.sort()))),
        );
        let body = match kind {
            QuantKind::Forall => Term::implies(facts, body),
            QuantKind::Exists => Term::and([facts, body]),
        };
        // A constant body decides the formula, except that a type
        // parameter may have no values.
        if let Term::Bool(value) = body {
            let inhabited = leaves
                .iter()
                .all(|(_, leaf)| !matches!(leaf, LeafTy::Poly(_)));
            if inhabited || value == (kind == QuantKind::Forall) {
                return Ok(Val::Leaf(Term::Bool(value)));
            }
        }
        let bound: Vec<(String, Sort)> = leaves
            .iter()
            .map(|(name, leaf)| (name.clone(), leaf.sort()))
            .collect();
        if self.auxiliary_work || !self.inline_stack.is_empty() {
            super::inline_work::term(&self.inline_work, &body, 2, e.span)?;
            for group in &triggers {
                for term in group {
                    super::inline_work::term(&self.inline_work, term.term(), 2, e.span)?;
                }
            }
        }
        let atom = self
            .ctx
            .quants
            .borrow_mut()
            .quant(kind, &bound, body, triggers)
            .ok_or_else(|| {
                refusal(
                    "generic-quantifier",
                    "an ill-sorted quantified template",
                    e.span,
                )
            })?;
        Ok(Val::Leaf(atom))
    }

    /// A choice: its functions applied to its holes (see `super::quant`).
    fn choose(
        &mut self,
        e: &Expr,
        vars: &[(LocalId, Ty)],
        triggers: &[Vec<Expr>],
        cond: &Expr,
        result: &Expr,
    ) -> R<Val> {
        if self.recommendations {
            super::aux_work::expression(&self.inline_work, e, e.span)?;
            self.choice_recommendations(e, vars, triggers, cond, result)?;
            // As upstream, produce the actual choice value with checks
            // suppressed after separately traversing its source expressions.
            return self.choice_value_without_events(e, vars, triggers, cond, result);
        }
        self.no_recursion_inside(e)?;
        if (self.reads.types.len() != 0 && self.inline_stack.is_empty())
            || vars.iter().any(|(_, ty)| ty.has_param())
            || result.ty.has_param()
        {
            return Err(refusal(
                "generic-choice",
                "a choice over a typed Poly domain",
                e.span,
            ));
        }
        if self.auxiliary_work {
            // Resource admission accepts/prices proof payloads; it is not
            // the separate checked-inline expression eligibility policy.
            super::aux_work::expression(&self.inline_work, e, e.span)?;
        } else if !self.inline_stack.is_empty() {
            super::inline_work::expression(&self.inline_work, e, e.span)?;
        }
        let (key, holes) = quant::choose_shape(e);
        let mut args = Vec::new();
        for hole in &holes {
            let value = self.expr(hole)?;
            if self.auxiliary_work || !self.inline_stack.is_empty() {
                super::inline_work::value(&self.inline_work, &value, 1, e.span)?;
            }
            value.leaves(&mut args);
        }
        // The template: the holes as parameters.
        let mut hole_leaves = Vec::new();
        let mut overrides = Vec::new();
        for hole in &holes {
            let shape = self
                .ctx
                .shape(&hole.ty, self.reads.types.owner(), hole.span)?;
            let val = self
                .ctx
                .quants
                .borrow_mut()
                .fresh_val(&shape, "qh", &mut hole_leaves);
            overrides.push((std::ptr::from_ref::<Expr>(hole), val));
        }
        let mark = self.holes.len();
        self.holes.extend(overrides);
        let depth = self.bound.len();
        let translated = self.bind(vars, e.span).and_then(|leaves| {
            let cond = self.bool(cond)?;
            let value = self.expr(result)?;
            let triggers = self.trigger_terms(triggers, &leaves, e.span)?;
            Ok((leaves, cond, value, triggers))
        });
        self.bound.truncate(depth);
        self.holes.truncate(mark);
        let (leaves, cond, value, triggers) = translated?;
        let mut value_terms = Vec::new();
        if self.auxiliary_work || !self.inline_stack.is_empty() {
            super::inline_work::value(&self.inline_work, &value, 3, e.span)?;
        }
        value.leaves(&mut value_terms);
        if leaves
            .iter()
            .any(|(_, leaf)| matches!(leaf, LeafTy::Poly(_)))
            || value_terms.iter().any(|term| term.sort() == Sort::Poly)
        {
            return Err(refusal(
                "generic-choice",
                "a boxed choice requiring typed templates",
                e.span,
            ));
        }
        self.check_choice_template(
            &leaves,
            &hole_leaves,
            &cond,
            &value_terms,
            &triggers,
            &args,
            e.span,
        )?;
        let facts = leaves
            .iter()
            .map(|(name, leaf)| leaf.fact(&Term::var(name.clone(), leaf.sort())));
        let cond = Term::and(facts.chain([cond]));
        let shape = self.ctx.shape(&e.ty, self.reads.types.owner(), e.span)?;
        let mut leaf_tys = Vec::new();
        shape.leaves(&mut leaf_tys);
        let mut values = Vec::new();
        value.leaves(&mut values);
        if leaf_tys.len() != values.len() {
            return Err(refusal(
                "vcgen-internal",
                "a choice whose value has another shape than its type",
                e.span,
            ));
        }
        let bound: Vec<(String, Sort)> = leaves
            .iter()
            .map(|(name, leaf)| (name.clone(), leaf.sort()))
            .collect();
        let hole_sorts: Vec<(String, Sort)> = hole_leaves
            .iter()
            .map(|(name, leaf)| (name.clone(), leaf.sort()))
            .collect();
        let output_count = leaf_tys.len();
        if self.auxiliary_work || !self.inline_stack.is_empty() {
            super::inline_work::term(&self.inline_work, &cond, 2, e.span)?;
            for group in &triggers {
                for term in group {
                    super::inline_work::term(&self.inline_work, term, 2, e.span)?;
                }
            }
        }
        let mut registry = self.ctx.quants.borrow_mut();
        let Some((k, names)) = registry.choose(
            key,
            &bound,
            &hole_sorts,
            cond,
            values.into_iter().zip(leaf_tys).collect(),
            triggers,
        ) else {
            return Err(refusal(
                "choose-shape",
                "two choices of one shape with different translations",
                e.span,
            ));
        };
        // Free variables of the template beyond the holes (type terms) are
        // read here as they are.
        let params = registry
            .function(&format!("ch{k}_0"))
            .map(|f| f.params)
            .unwrap_or_default();
        for (name, sort) in names.iter().zip(&params).skip(hole_sorts.len()) {
            args.push(Term::var(name.clone(), *sort));
        }
        let mut i = 0;
        if self.auxiliary_work || !self.inline_stack.is_empty() {
            for argument in &args {
                super::inline_work::term(&self.inline_work, argument, output_count, e.span)?;
            }
        }
        let value = build_val(&shape, &mut |_| {
            let app = registry.choose_app(k, i, args.clone());
            i += 1;
            app
        });
        drop(registry);
        value.ok_or_else(|| refusal("vcgen-internal", "a choice without a value", e.span))
    }

    /// a40's pure-skip phase emits neither diagnostics nor physical proof
    /// events. Preserve the actual first traversal's ordinal stream on both
    /// success and resource/translation refusal; no normal path calls this.
    fn choice_value_without_events(
        &mut self,
        e: &Expr,
        vars: &[(LocalId, Ty)],
        triggers: &[Vec<Expr>],
        cond: &Expr,
        result: &Expr,
    ) -> R<Val> {
        let recommendations = std::mem::replace(&mut self.recommendations, false);
        let events = self.rec_calls.take();
        let value = self.choose(e, vars, triggers, cond, result);
        self.rec_calls = events;
        self.recommendations = recommendations;
        value
    }

    /// Admission only: no membership, witness, seed or definition is emitted.
    /// The complete translated choice, including real hole arguments, shares
    /// one variable-sort table and the existing inline grant with its caller.
    fn check_choice_template(
        &self,
        leaves: &[(String, LeafTy)],
        holes: &[(String, LeafTy)],
        condition: &Term,
        values: &[Term],
        triggers: &[Vec<Term>],
        arguments: &[Term],
        span: SpanId,
    ) -> R<()> {
        let shared = self.auxiliary_work || !self.inline_stack.is_empty();
        let work = self.inline_work.clone();
        let mut left = 200_000usize;
        let mut pay = |cost| match (if shared { work.get() } else { left }).checked_sub(cost) {
            Some(next) => {
                if shared {
                    work.set(next);
                } else {
                    left = next;
                }
                true
            }
            None => false,
        };
        let exhausted = || {
            refusal(
                "generic-choice",
                "typed choice template work exhausted",
                span,
            )
        };
        if !pay(1) {
            return Err(exhausted());
        }
        let mut bound = Vec::new();
        for (name, leaf) in leaves.iter().chain(holes) {
            if !pay(name.len().saturating_add(1).saturating_mul(4)) {
                return Err(exhausted());
            }
            bound.push((name.clone(), leaf.clone()));
        }
        if !pay(values
            .len()
            .saturating_add(arguments.len())
            .saturating_add(1))
        {
            return Err(exhausted());
        }
        let mut roots = vec![condition];
        roots.extend(values);
        roots.extend(arguments);
        for group in triggers {
            if !pay(group.len().saturating_add(1)) {
                return Err(exhausted());
            }
            roots.extend(group);
        }
        // Translation can register canonical concrete recipes/codec functions,
        // so snapshot the current vocabulary only after translating ALL roots.
        let vocabulary =
            super::closed_templates::Vocabulary::new(self.ctx, self.functions, self.sigs, &mut pay)
                .ok_or_else(|| {
                    refusal(
                        "generic-choice",
                        "unavailable typed choice vocabulary",
                        span,
                    )
                })?;
        if !vocabulary.closed_environment(&self.reads.types, &mut pay) {
            return Err(refusal(
                "generic-choice",
                "a choice without a canonical closed type environment",
                span,
            ));
        }
        let registry = self.ctx.quants.borrow();
        if !vocabulary.check(&registry, &roots, &bound, &mut pay) {
            return Err(refusal(
                "generic-choice",
                "a boxed choice outside the checked concrete template",
                span,
            ));
        }
        Ok(())
    }

    fn spec_call(
        &mut self,
        e: &Expr,
        callee: FnId,
        type_args: &[Ty],
        types: TypeEnv,
        args: &[Expr],
    ) -> R<Val> {
        let Some(sig) = self.sigs.get(&callee) else {
            return Err(refusal(
                "vcgen-internal",
                "a call of a function that is not spec",
                e.span,
            ));
        };
        if let Some(problem) = &sig.problem {
            return Err(problem.clone());
        }
        let declaration = *self.ctx.fns.get(&callee).ok_or_else(|| {
            refusal(
                "vcgen-internal",
                "a spec call without its source declaration",
                e.span,
            )
        })?;
        if sig.owner != callee
            || types.owner() != Some(callee)
            || types.len() != sig.n_types
            || type_args.len() != declaration.type_params.len()
            || args.len() != sig.params.len()
            || args.len() != declaration.params.len()
        {
            return Err(refusal(
                "vcgen-internal",
                "a spec call with the wrong number of arguments",
                e.span,
            ));
        }
        for (arg, local) in args.iter().zip(&declaration.params) {
            let formal = declaration
                .local(*local)
                .ok_or_else(|| refusal("vcgen-internal", "a missing source parameter", arg.span))?;
            let actual = if declaration.attrs.inline && declaration.role != crate::FnRole::TraitDecl
            {
                super::inline_body::ty(
                    self.ctx,
                    &formal.ty,
                    type_args,
                    &self.inline_work,
                    arg.span,
                )?
            } else {
                formal.ty.subst(type_args)
            };
            if actual != arg.ty {
                return Err(refusal(
                    "generic-product",
                    "a source parameter substitution differs from its actual argument",
                    arg.span,
                ));
            }
        }
        let result_ty = declaration
            .ret_ty()
            .ok_or_else(|| refusal("vcgen-internal", "a missing source return type", e.span))?;
        let actual_result =
            if declaration.attrs.inline && declaration.role != crate::FnRole::TraitDecl {
                super::inline_body::ty(self.ctx, result_ty, type_args, &self.inline_work, e.span)?
            } else {
                result_ty.subst(type_args)
            };
        if actual_result != e.ty {
            return Err(refusal(
                "generic-product",
                "a source result substitution differs from its actual type",
                e.span,
            ));
        }
        let recursive = self
            .rec_calls
            .as_ref()
            .is_some_and(|rec| rec.members.contains(&callee));
        if recursive {
            return self.rec_call(e, callee, type_args, types, args);
        }
        // A trait declaration's body is a default that may be overridden;
        // the pinned elaborator leaves that dispatch uninlined.
        if declaration.attrs.inline && declaration.role != crate::FnRole::TraitDecl {
            return self.inline_spec_call(e, callee, type_args, types, args);
        }
        if self.auxiliary_work || !self.inline_stack.is_empty() {
            for index in 0..types.len() {
                let argument = types
                    .get(u32::try_from(index).map_err(|_| {
                        refusal(
                            "inline-size",
                            "an inline type-vector index overflow",
                            e.span,
                        )
                    })?)
                    .ok_or_else(|| {
                        refusal("inline-body", "a missing inline type argument", e.span)
                    })?;
                for term in argument.terms_ref() {
                    super::inline_work::term(
                        &self.inline_work,
                        term,
                        1 + usize::from(self.recommendations),
                        e.span,
                    )?;
                }
            }
        }
        let mut recommendation_reads = self.recommendations.then(|| Reads {
            types: types.clone(),
            ..Reads::default()
        });
        let mut leaves = types.terms();
        for (parameter, (arg, shape)) in args.iter().zip(&sig.params).enumerate() {
            let mut terms = Vec::new();
            let value = self.expr(arg)?;
            if self.auxiliary_work || !self.inline_stack.is_empty() {
                super::inline_work::value(&self.inline_work, &value, 2, arg.span)?;
            }
            if let Some(reads) = &mut recommendation_reads {
                let local = declaration.params[parameter];
                let formal = declaration.local(local).ok_or_else(|| {
                    refusal(
                        "vcgen-internal",
                        "a missing recommendation parameter",
                        arg.span,
                    )
                })?;
                let native_shape = self.ctx.shape(&formal.ty, Some(callee), arg.span)?;
                // The predicate is source IR, not the generic UF ABI. Adapt
                // this same evaluated argument to its declared native layout
                // before the separate UF conversion boxes every parameter.
                super::inline_work::value(&self.inline_work, &value, 1, arg.span)?;
                let native = self.ctx.formal_value(
                    FormalValue {
                        position: FormalPosition::NativeParameter(parameter),
                        actual_ty: &arg.ty,
                        type_args,
                        caller: &self.reads.types,
                        callee: &types,
                        span: arg.span,
                    },
                    &native_shape,
                    value.clone(),
                )?;
                super::inline_work::value(&self.inline_work, &native, 1, arg.span)?;
                reads.read.insert(local, native.clone());
                reads.old.insert(local, native);
            }
            let value = self.ctx.formal_value(
                FormalValue {
                    position: FormalPosition::SpecParameter(parameter),
                    actual_ty: &arg.ty,
                    type_args,
                    caller: &self.reads.types,
                    callee: &types,
                    span: arg.span,
                },
                shape,
                value,
            )?;
            if self.auxiliary_work || !self.inline_stack.is_empty() {
                super::inline_work::value(&self.inline_work, &value, 1, arg.span)?;
            }
            value.leaves(&mut terms);
            let mut expected = Vec::new();
            shape.leaves(&mut expected);
            if terms.len() != expected.len()
                || terms
                    .iter()
                    .zip(&expected)
                    .any(|(term, leaf)| term.sort() != leaf.sort())
            {
                return Err(refusal(
                    "spec-fn-layout",
                    "a spec argument requiring an instantiated product layout",
                    arg.span,
                ));
            }
            leaves.extend(terms);
        }
        if let Some(reads) = recommendation_reads {
            self.recommendation_checks(e, callee, &reads, None)?;
        }
        self.called.insert(callee);
        if self.auxiliary_work || !self.inline_stack.is_empty() {
            for term in &leaves {
                super::inline_work::term(&self.inline_work, term, sig.outputs.len(), e.span)?;
            }
        }
        let mut index = 0;
        let result = build_val(&sig.result, &mut |leaf| {
            let output = sig.outputs.get(index)?;
            index += 1;
            (output.leaf.sort() == leaf.sort())
                .then(|| Term::call(output.name.clone(), leaves.clone(), leaf.sort()))
        })
        .ok_or_else(|| {
            refusal(
                "vcgen-internal",
                "a spec result without its declared leaves",
                e.span,
            )
        })?;
        let result = self.ctx.formal_value(
            FormalValue {
                position: FormalPosition::Result,
                actual_ty: &e.ty,
                type_args,
                caller: &self.reads.types,
                callee: &types,
                span: e.span,
            },
            &sig.result,
            result,
        )?;
        if index != sig.outputs.len()
            || !result.matches(&self.ctx.shape(&e.ty, self.reads.types.owner(), e.span)?)
        {
            return Err(refusal(
                "spec-fn-layout",
                "a spec call requiring an instantiated product result layout",
                e.span,
            ));
        }
        Ok(result)
    }

    /// Checked inline bodies are expressions, never UF assumptions. A
    /// separately named concrete instance expands only its own checked body;
    /// it gains no equality with its generic origin. Each child has its own
    /// local/binder scope, actual TypeEnv and the parent's remaining work grant.
    fn inline_spec_call(
        &mut self,
        expression: &Expr,
        callee: FnId,
        type_args: &[Ty],
        types: TypeEnv,
        args: &[Expr],
    ) -> R<Val> {
        let declaration = *self.ctx.fns.get(&callee).ok_or_else(|| {
            refusal(
                "inline-body",
                "a missing original inline declaration",
                expression.span,
            )
        })?;
        let crate::Body::Spec(body) = &declaration.body else {
            return Err(refusal(
                "inline-body",
                "an inline declaration without a spec body",
                expression.span,
            ));
        };
        if declaration.mode != crate::Mode::Spec
            || declaration.attrs.external_body
            || declaration.role == crate::FnRole::Imported
            || !super::inline_body::independent_instance(
                self.ctx,
                declaration,
                type_args,
                &self.inline_work,
                expression.span,
            )?
            || self.ctx.group(callee).is_some()
            || !declaration.decreases.is_empty()
            || self.inline_stack.contains(&callee)
            || self.inline_stack.len() >= 256
        {
            return Err(refusal(
                "inline-body",
                "an unsupported or recursive inline declaration",
                expression.span,
            ));
        }
        let result_ty = declaration.ret_ty().ok_or_else(|| {
            refusal(
                "inline-body",
                "a missing inline result declaration",
                expression.span,
            )
        })?;
        let result_shape = self.ctx.shape(result_ty, Some(callee), expression.span)?;
        // Verus elaborates an explicitly inline body after substituting its
        // actual closed source types. This is a body expression, not an
        // instance definition or a new generic-function ABI. An open caller
        // environment retains the existing source-formal translation path.
        let specialized = if !type_args.is_empty()
            && super::inline_body::closed(type_args, &self.inline_work, expression.span)?
        {
            Some(super::inline_body::expression(
                self.ctx,
                body,
                type_args,
                &self.inline_work,
            )?)
        } else {
            None
        };
        for index in 0..types.len() {
            let argument = types
                .get(u32::try_from(index).map_err(|_| {
                    refusal(
                        "inline-size",
                        "an inline type-vector index overflow",
                        expression.span,
                    )
                })?)
                .ok_or_else(|| {
                    refusal(
                        "inline-body",
                        "a missing inline type argument",
                        expression.span,
                    )
                })?;
            for term in argument.terms_ref() {
                super::inline_work::term(&self.inline_work, term, 1, expression.span)?;
            }
        }
        let mut reads = Reads {
            types: types.clone(),
            ..Reads::default()
        };
        for (index, (arg, local)) in args.iter().zip(&declaration.params).enumerate() {
            let formal = declaration.local(*local).ok_or_else(|| {
                refusal("inline-body", "a missing inline parameter", expression.span)
            })?;
            let shape = self.ctx.shape(&formal.ty, Some(callee), arg.span)?;
            let value = self.expr(arg)?;
            super::inline_work::value(&self.inline_work, &value, 1, arg.span)?;
            let value = if specialized.is_some() {
                let actual = super::inline_body::ty(
                    self.ctx,
                    &formal.ty,
                    type_args,
                    &self.inline_work,
                    arg.span,
                )?;
                if actual != arg.ty
                    || !value.matches(&self.ctx.shape(&actual, Some(callee), arg.span)?)
                {
                    return Err(refusal(
                        "inline-body",
                        "a closed inline parameter differs from its actual native value",
                        arg.span,
                    ));
                }
                value
            } else {
                self.ctx.formal_value(
                    FormalValue {
                        position: FormalPosition::NativeParameter(index),
                        actual_ty: &arg.ty,
                        type_args,
                        caller: &self.reads.types,
                        callee: &types,
                        span: arg.span,
                    },
                    &shape,
                    value,
                )?
            };
            super::inline_work::value(&self.inline_work, &value, 2, arg.span)?;
            let local = *declaration.params.get(index).ok_or_else(|| {
                refusal("inline-body", "a missing inline parameter", expression.span)
            })?;
            reads.read.insert(local, value.clone());
            reads.old.insert(local, value);
        }
        self.recommendation_checks(
            expression,
            callee,
            &reads,
            specialized.as_ref().map(|_| type_args),
        )?;
        let mut child = Tr::new(self.ctx, self.sigs, self.functions, &reads)
            .with_recommendations(self.recommendations);
        for (name, _) in &self.recommendation_symbols {
            super::inline_work::items(&self.inline_work, name.len() + 1, expression.span)?;
        }
        child.recommendation_symbols = self.recommendation_symbols.clone();
        child.inline_work = self.inline_work.clone();
        child.auxiliary_work = self.auxiliary_work;
        child.inline_stack = self.inline_stack.clone();
        child.inline_stack.push(callee);
        for guard in &self.guard {
            super::inline_work::term(&self.inline_work, guard, 1, expression.span)?;
        }
        child.guard = self.guard.clone();
        if let Some(calls) = &self.rec_calls {
            super::inline_work::items(&self.inline_work, calls.members.len(), expression.span)?;
        }
        child.rec_calls = self.rec_calls.as_ref().map(|calls| RecCalls {
            members: calls.members.clone(),
            ..RecCalls::default()
        });
        let value = child.expr(specialized.as_ref().unwrap_or(body))?;
        self.checks.extend(child.checks);
        self.called.extend(child.called);
        if let (Some(parent), Some(mut nested)) = (&mut self.rec_calls, child.rec_calls) {
            parent.proofs += nested.proofs;
            parent.found.append(&mut nested.found);
        }
        super::inline_work::value(&self.inline_work, &value, 1, expression.span)?;
        let value = if specialized.is_some() {
            let actual = super::inline_body::ty(
                self.ctx,
                result_ty,
                type_args,
                &self.inline_work,
                expression.span,
            )?;
            if actual != expression.ty {
                return Err(refusal(
                    "inline-body",
                    "a closed inline result differs from its actual native type",
                    expression.span,
                ));
            }
            value
        } else {
            self.ctx.formal_value(
                FormalValue {
                    position: FormalPosition::Result,
                    actual_ty: &expression.ty,
                    type_args,
                    caller: &self.reads.types,
                    callee: &types,
                    span: expression.span,
                },
                &result_shape,
                value,
            )?
        };
        if !value.matches(&self.ctx.shape(
            &expression.ty,
            self.reads.types.owner(),
            expression.span,
        )?) {
            return Err(refusal(
                "inline-body",
                "an inline result with the wrong instantiated layout",
                expression.span,
            ));
        }
        Ok(value)
    }

    /// Record a recursive call; its value is a fresh symbol per leaf.
    fn rec_call(
        &mut self,
        e: &Expr,
        callee: FnId,
        type_args: &[Ty],
        types: TypeEnv,
        args: &[Expr],
    ) -> R<Val> {
        let declaration = *self.ctx.fns.get(&callee).ok_or_else(|| {
            refusal(
                "vcgen-internal",
                "a recursive call without its source declaration",
                e.span,
            )
        })?;
        let mut values = Vec::new();
        for (parameter, (arg, local)) in args.iter().zip(&declaration.params).enumerate() {
            let value = self.expr(arg)?;
            let formal_ty = &declaration
                .local(*local)
                .ok_or_else(|| {
                    refusal(
                        "vcgen-internal",
                        "a missing recursive source parameter",
                        arg.span,
                    )
                })?
                .ty;
            // The termination reader uses the callee's native source layout,
            // keeping primitive decreases native while adapting a formal A.
            let shape = self.ctx.shape(formal_ty, Some(callee), arg.span)?;
            values.push(self.ctx.formal_value(
                FormalValue {
                    position: FormalPosition::NativeParameter(parameter),
                    actual_ty: &arg.ty,
                    type_args,
                    caller: &self.reads.types,
                    callee: &types,
                    span: arg.span,
                },
                &shape,
                value,
            )?);
        }
        if self.recommendations {
            let reads = Reads {
                read: declaration
                    .params
                    .iter()
                    .copied()
                    .zip(values.iter().cloned())
                    .collect(),
                old: declaration
                    .params
                    .iter()
                    .copied()
                    .zip(values.iter().cloned())
                    .collect(),
                types: types.clone(),
            };
            self.recommendation_checks(e, callee, &reads, None)?;
        }
        self.called.insert(callee);
        let index = self.rec_calls.as_ref().map_or(0, |rec| rec.found.len());
        let shape = self.ctx.shape(&e.ty, self.reads.types.owner(), e.span)?;
        let mut result = Vec::new();
        let value = fresh_val(&shape, &format!("rc{index}"), &mut result);
        if let Some(rec) = self.rec_calls.as_mut() {
            rec.found.push(RecEvent::Call(RecCall {
                callee,
                guard: self.guard.clone(),
                types,
                args: values,
                result,
                span: e.span,
            }));
        }
        Ok(value)
    }

    fn unary(&mut self, e: &Expr, op: UnOp, arg: &Expr, check: Option<SiteId>) -> R<Val> {
        let v = self.leaf(arg)?;
        match op {
            UnOp::Not => {
                if arg.ty == Ty::Bool {
                    Ok(Val::Leaf(v.not()))
                } else {
                    let raw = self.ctx.integer_bitwise(
                        super::bitwise::Operation::Not,
                        vec![v],
                        e.span,
                    )?;
                    Ok(Val::Leaf(
                        if e.ty.int_range().is_some_and(IntRange::is_signed_machine) {
                            raw
                        } else {
                            clip_bitwise(e, raw, self.ctx.pointer_width)?
                        },
                    ))
                }
            }
            UnOp::Neg => {
                let value = v.neg();
                if let Some(site) = check {
                    let range = machine_range(&e.ty, e.span)?;
                    let (lo, hi) =
                        range_bounds(super::val::concrete_range(range, self.ctx.pointer_width));
                    if self.auxiliary_work || !self.inline_stack.is_empty() {
                        super::inline_work::term(&self.inline_work, &value, 2, e.span)?;
                    }
                    self.pending(
                        PendingKind::Overflow,
                        value.within_type_bounds(lo, hi),
                        site,
                        e.span,
                    )?;
                }
                Ok(Val::Leaf(value))
            }
        }
    }

    fn binary(
        &mut self,
        e: &Expr,
        op: BinOp,
        lhs: &Expr,
        rhs: &Expr,
        check: Option<SiteId>,
    ) -> R<Val> {
        match op {
            BinOp::And | BinOp::Or | BinOp::Implies => {
                let a = self.leaf(lhs)?;
                if self.auxiliary_work || !self.inline_stack.is_empty() {
                    super::inline_work::term(&self.inline_work, &a, 1, e.span)?;
                }
                let guard = if op == BinOp::Or {
                    a.clone().not()
                } else {
                    a.clone()
                };
                let b = self.guarded(guard, |tr| tr.leaf(rhs))?;
                Ok(Val::Leaf(match op {
                    BinOp::And => Term::and([a, b]),
                    BinOp::Or => Term::or([a, b]),
                    _ => Term::implies(a, b),
                }))
            }
            BinOp::Eq | BinOp::Ne => {
                let a = self.expr(lhs)?;
                let b = self.expr(rhs)?;
                if self.auxiliary_work || !self.inline_stack.is_empty() {
                    super::inline_work::value(&self.inline_work, &a, 1, e.span)?;
                    super::inline_work::value(&self.inline_work, &b, 1, e.span)?;
                }
                let eq = a.equal(&b).ok_or_else(|| {
                    refusal(
                        "vcgen-internal",
                        "equality of values of different shapes",
                        e.span,
                    )
                })?;
                Ok(Val::Leaf(if op == BinOp::Eq { eq } else { eq.not() }))
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let a = self.leaf(lhs)?;
                let b = self.leaf(rhs)?;
                Ok(Val::Leaf(match op {
                    BinOp::Lt => Term::lt(a, b),
                    BinOp::Le => Term::le(a, b),
                    BinOp::Gt => Term::lt(b, a),
                    _ => Term::le(b, a),
                }))
            }
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => {
                if lhs.ty != Ty::Bool {
                    let a = self.leaf(lhs)?;
                    let b = self.leaf(rhs)?;
                    let op = match op {
                        BinOp::BitAnd => super::bitwise::Operation::And,
                        BinOp::BitOr => super::bitwise::Operation::Or,
                        _ => super::bitwise::Operation::Xor,
                    };
                    let raw = self.ctx.integer_bitwise(op, vec![a, b], e.span)?;
                    return Ok(Val::Leaf(clip_bitwise(e, raw, self.ctx.pointer_width)?));
                }
                let a = self.leaf(lhs)?;
                let b = self.leaf(rhs)?;
                Ok(Val::Leaf(match op {
                    BinOp::BitAnd => Term::and([a, b]),
                    BinOp::BitOr => Term::or([a, b]),
                    _ => Term::eq(a, b).not(),
                }))
            }
            BinOp::Shl | BinOp::Shr => {
                if check.is_some() {
                    return Err(refusal(
                        "shift",
                        "an exec shift requiring its overflow check",
                        e.span,
                    ));
                }
                let a = self.leaf(lhs)?;
                let b = self.leaf(rhs)?;
                let op = if op == BinOp::Shl {
                    super::bitwise::Operation::LeftShift
                } else {
                    super::bitwise::Operation::RightShift
                };
                let raw = self.ctx.integer_bitwise(op, vec![a, b], e.span)?;
                Ok(Val::Leaf(clip_bitwise(e, raw, self.ctx.pointer_width)?))
            }
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem => {
                let a = self.leaf(lhs)?;
                let b = self.leaf(rhs)?;
                match check {
                    None => Ok(Val::Leaf(spec_arith(op, a, b))),
                    Some(site) => self.checked_arith(e, op, a, b, site),
                }
            }
        }
    }

    /// Exec arithmetic on a machine type: the exact result, with its check.
    fn checked_arith(&mut self, e: &Expr, op: BinOp, a: Term, b: Term, site: SiteId) -> R<Val> {
        let range = machine_range(&e.ty, e.span)?;
        match op {
            BinOp::Div | BinOp::Rem => {
                if range.is_signed_machine() {
                    // Verus proves signed division through vstd's
                    // specifications of the operator traits.
                    return Err(refusal(
                        "signed-div",
                        "division or remainder of signed machine integers",
                        e.span,
                    ));
                }
                if self.auxiliary_work || !self.inline_stack.is_empty() {
                    super::inline_work::term(&self.inline_work, &b, 1, e.span)?;
                }
                self.pending(
                    PendingKind::DivByZero,
                    Term::eq(b.clone(), Term::Int(0)).not(),
                    site,
                    e.span,
                )?;
                // Truncating and Euclidean division agree on non-negative
                // operands.
                Ok(Val::Leaf(spec_arith(op, a, b)))
            }
            _ => {
                let value = spec_arith(op, a, b);
                let (lo, hi) =
                    range_bounds(super::val::concrete_range(range, self.ctx.pointer_width));
                if self.auxiliary_work || !self.inline_stack.is_empty() {
                    super::inline_work::term(&self.inline_work, &value, 2, e.span)?;
                }
                self.pending(
                    PendingKind::Overflow,
                    value.within_type_bounds(lo, hi),
                    site,
                    e.span,
                )?;
                Ok(Val::Leaf(value))
            }
        }
    }
}

/// A value of `shape` whose leaves `leaf` makes, in order.
fn build_val(
    shape: &Shape,
    leaf: &mut dyn FnMut(&super::val::LeafTy) -> Option<Term>,
) -> Option<Val> {
    match shape {
        Shape::Leaf(ty) => Some(Val::Leaf(leaf(ty)?)),
        Shape::Node(children) => {
            let mut out = Vec::new();
            for child in children {
                out.push(build_val(child, leaf)?);
            }
            Some(Val::Node(out))
        }
    }
}

/// A value of `shape` made of symbols named `<prefix>_<n>`, listed in `out`
/// with their types.
fn fresh_val(shape: &Shape, prefix: &str, out: &mut Vec<(String, LeafTy)>) -> Val {
    match shape {
        Shape::Leaf(leaf) => {
            let name = format!("{prefix}_{}", out.len());
            out.push((name.clone(), *leaf));
            Val::Leaf(Term::var(name, leaf.sort()))
        }
        Shape::Node(children) => Val::Node(
            children
                .iter()
                .map(|child| fresh_val(child, prefix, out))
                .collect(),
        ),
    }
}

/// The value of a literal.
fn lit_val(lit: Lit, _span: SpanId) -> R<Val> {
    match lit {
        Lit::Bool(value) => Ok(Val::Leaf(Term::Bool(value))),
        Lit::Unit => Ok(Val::unit()),
        Lit::Int(value) => {
            if let Some(small) = value.to_i128() {
                return Ok(Val::Leaf(Term::Int(small)));
            }
            let magnitude = Term::unsigned(value.magnitude);
            Ok(Val::Leaf(if value.negative {
                magnitude.neg()
            } else {
                magnitude
            }))
        }
    }
}

/// Preserve the pinned ordinary bitwise UF result and its mathematical clip.
fn clip_bitwise(e: &Expr, value: Term, pointer_width: u32) -> R<Term> {
    Ok(match bitwise_clip_range(e, pointer_width)? {
        Some(range) => spec::clip(range, value),
        None => value,
    })
}

/// The range used by the EXISTING ordinary bitwise result constructor.
fn bitwise_clip_range(e: &Expr, pointer_width: u32) -> R<Option<IntRange>> {
    match e
        .ty
        .int_range()
        .map(|range| super::val::concrete_range(range, pointer_width))
    {
        Some(IntRange::Int | IntRange::Nat) => Ok(None),
        Some(range) => {
            supported_range(range).map_err(|(tag, detail)| refusal(tag, detail, e.span))?;
            Ok(Some(range))
        }
        None => Err(refusal(
            "bitwise",
            "a bitwise result without integer type",
            e.span,
        )),
    }
}

/// Only source operations whose normal body translation applies that clip,
/// also through exact or range-containing casts that retain the same value.
/// Signed integer not deliberately stays the existing unbounded raw call;
/// Boolean operators and arbitrary conditionals do not acquire Clip metadata.
fn lowered_trigger_clip(e: &Expr, pointer_width: u32) -> R<Option<IntRange>> {
    let clipped = match &e.kind {
        ExprKind::Cast { arg, kind } => {
            if *kind == CastKind::Exact {
                return lowered_trigger_clip(arg, pointer_width);
            }
            let (Some(from), Some(to)) = (arg.ty.int_range(), e.ty.int_range()) else {
                return Err(refusal("vcgen-internal", "a cast of a non-integer", e.span));
            };
            match cast_clip_range(from, to, e.span, pointer_width)? {
                Some(to) => return Ok(Some(to)),
                None => return lowered_trigger_clip(arg, pointer_width),
            }
        }
        ExprKind::Unary {
            op: UnOp::Not, arg, ..
        } => arg.ty != Ty::Bool && !e.ty.int_range().is_some_and(IntRange::is_signed_machine),
        ExprKind::Binary {
            op: BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor,
            lhs,
            ..
        } => lhs.ty != Ty::Bool,
        ExprKind::Binary {
            op: BinOp::Shl | BinOp::Shr,
            ..
        } => true,
        _ => false,
    };
    if clipped {
        bitwise_clip_range(e, pointer_width)
    } else {
        Ok(None)
    }
}

/// Follow a place's projections from its root value. References are
/// transparent.
pub(crate) fn project(root: &Val, place: &Place, span: SpanId) -> R<Val> {
    let mut val = root;
    for projection in &place.projections {
        val = match projection {
            Projection::Deref => val,
            Projection::Field { variant: 0, field } | Projection::TupleField(field) => val
                .child(*field)
                .ok_or_else(|| refusal("vcgen-internal", "a projection out of range", span))?,
            Projection::Field { .. } => {
                return Err(refusal("enum", "a field of an enum variant", span));
            }
        };
    }
    Ok(val.clone())
}

/// The machine integer type of a checked operation.
fn machine_range(ty: &Ty, span: SpanId) -> R<IntRange> {
    let range = ty
        .int_range()
        .filter(|range| range.is_bounded())
        .ok_or_else(|| {
            refusal(
                "vcgen-internal",
                "an exec check on a non-machine type",
                span,
            )
        })?;
    supported_range(range).map_err(|(tag, detail)| refusal(tag, detail, span))?;
    Ok(range)
}

/// Is `t` an integer literal other than zero?
fn nonzero_literal(t: &Term) -> bool {
    t.as_int().is_some_and(|value| value != 0)
}

/// Spec (exact) arithmetic, with Verus's treatment of nonlinear operations.
/// `op` is one of `+ - * / %`; anything else is read as `%`.
pub(crate) fn spec_arith(op: BinOp, a: Term, b: Term) -> Term {
    match op {
        BinOp::Add => Term::arith(ArithOp::Add, a, b),
        BinOp::Sub => Term::arith(ArithOp::Sub, a, b),
        BinOp::Mul if a.as_int().is_some() || b.as_int().is_some() => {
            Term::arith(ArithOp::Mul, a, b)
        }
        BinOp::Mul => Term::call(NL_MUL, vec![a, b], Sort::Int),
        BinOp::Div if nonzero_literal(&b) => Term::arith(ArithOp::Div, a, b),
        BinOp::Div => Term::call(NL_DIV, vec![a, b], Sort::Int),
        BinOp::Rem if nonzero_literal(&b) => Term::arith(ArithOp::Mod, a, b),
        _ => Term::call(NL_MOD, vec![a, b], Sort::Int),
    }
}

/// `v as to`, for a value of type `from`: unchanged when it always fits,
/// Verus's clip otherwise.
fn clip(from: IntRange, to: IntRange, v: Term, span: SpanId, pointer_width: u32) -> R<Term> {
    Ok(match cast_clip_range(from, to, span, pointer_width)? {
        Some(to) => spec::clip(to, v),
        None => v,
    })
}

/// Shared by ordinary body casts and typed trigger provenance. `None` is
/// exactly the existing identity/range-containment case, never a new premise.
fn cast_clip_range(
    from: IntRange,
    to: IntRange,
    span: SpanId,
    pointer_width: u32,
) -> R<Option<IntRange>> {
    let from = super::val::concrete_range(from, pointer_width);
    let to = super::val::concrete_range(to, pointer_width);
    supported_range(to).map_err(|(tag, detail)| refusal(tag, detail, span))?;
    // 64 is only used for pointer-sized types, which are refused above.
    if to == IntRange::Int || (to.contains(from, pointer_width) && supported_range(from).is_ok()) {
        return Ok(None);
    }
    Ok(Some(to))
}

/// Instantiate complete native type arguments in the caller's binder scope.
pub(crate) fn type_terms(
    ctx: &Ctx<'_>,
    callee: FnId,
    type_args: &[Ty],
    types: &TypeEnv,
    span: SpanId,
) -> R<TypeEnv> {
    let arguments = type_args
        .iter()
        .map(|ty| ctx.type_argument(ty, types, span))
        .collect::<R<_>>()?;
    Ok(TypeEnv::new(callee, arguments))
}

#[cfg(test)]
#[path = "choice_typed_tests.rs"]
mod choice_typed_tests;

#[cfg(test)]
#[path = "expr/auxiliary_tests.rs"]
mod auxiliary_tests;

#[cfg(test)]
#[path = "expr/choice_recommendation_tests.rs"]
mod choice_recommendation_tests;
