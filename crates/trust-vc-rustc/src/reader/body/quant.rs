//! Quantifiers, choices and `assert forall .. by`.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! `verus!` writes `forall|x: T| body` as `forall(|x: T| body)`, `choose`
//! and `choose_tuple` likewise, `#![trigger a, b]` as `with_triggers(((a,
//! b),), body)`, `#![auto]` and `#![all_triggers]` as attributes on the
//! body, and `#[trigger] e` as an attribute on `e` (`fn_call_to_vir.rs`,
//! `extract_quant`, `extract_choose`; `rust_to_vir_expr.rs`, `expr_to_vir`).
//! The reader binds the closure's parameters to bound locals, reads the
//! body as spec code, and chooses the triggers the way Verus does
//! (`trust_vc_vcir::triggers`). Verus chooses them when it turns a module
//! into SST, so its trigger errors belong to that phase.
//!
//! `assert forall|x| r implies e by { proof }` is `assert_forall_by(|x| {
//! requires(r); ensures(e); proof })`, which Verus checks in a dead end
//! (`ast_to_sst.rs`, `ExprX::AssertBy`): fresh values of the variables'
//! types, `r` assumed, the proof, `e` asserted; and then assumes `forall|x|
//! r ==> e`.

use std::collections::HashMap;

use rustc_ast::{BindingMode, ByRef};
use rustc_hir::{self as hir, def::DefKind, PatKind};
use rustc_span::Span;

use trust_vc_vcir::triggers::{self, AutoMode, Mark, Quantifier};
use trust_vc_vcir::{
    BinOp, Block, ClauseAttrs, Expr, ExprKind, LocalId, LocalKind, Mode, QuantKind, Stmt, StmtKind,
    Ty,
};

use super::super::attrs::{self, VerusAttr};
use super::super::UserError;
use super::{refuse, Ctx, FnProblem, FnReader, R};
use crate::messages::Phase;
use crate::verus_items::VerusItem;

/// `fn_call_to_vir.rs`, `extract_quant`: the body is not a `bool`.
const MSG_QUANT_BOOL: &str = "forall/ensures needs a bool expression";
/// `fn_call_to_vir.rs`, `extract_choose`: `choose` with more than one
/// variable.
const MSG_CHOOSE_ONE: &str =
    "choose expects exactly one parameter (use choose_tuple for multiple parameters)";
/// `fn_call_to_vir.rs`, `extract_assert_forall_by`.
const MSG_AFB_REQUIRES: &str = "assert_forall_by can have at most one requires";
/// `fn_call_to_vir.rs`, `extract_assert_forall_by`.
const MSG_AFB_ENSURES: &str = "assert_forall_by must have exactly one ensures";
/// `vir::headers::read_header_block`: marker calls are unique, even when an
/// array argument contains no clauses.
const MSG_HEADER_REQUIRES: &str =
    "only one call to requires allowed (use requires([e1, ..., en]) for multiple expressions";
const MSG_HEADER_ENSURES: &str =
    "only one call to ensures allowed (use ensures([e1, ..., en]) for multiple expressions";
/// `well_formed.rs`, `check_expr`: `==>` as the conclusion of `assert
/// forall`.
const MSG_AFB_IMPLIES: &str = "using ==> in `assert forall` does not currently assume the antecedent in the body; consider using `implies` instead of `==>`";

/// A quantifier whose body is being read: the `#![trigger ..]` groups and
/// the `#![auto]` / `#![all_triggers]` annotation found in it.
#[derive(Debug, Default)]
pub(super) struct QuantFrame {
    with_triggers: Vec<Vec<Expr>>,
    auto: AutoMode,
}

/// Preserve all explicit, already typed source candidates after inference
/// fails. They are diagnostic children, never replacement trigger groups.
fn failed_candidates(marks: Vec<Mark>, frame: QuantFrame) -> Vec<Expr> {
    marks
        .into_iter()
        .map(|mark| mark.term)
        .chain(frame.with_triggers.into_iter().flatten())
        .collect()
}

impl<'tcx> FnReader<'_, 'tcx> {
    pub(super) fn broadcast_rules(&mut self, span: Span) -> R<()> {
        if self.mode != Mode::Proof {
            self.errors.push(UserError::new(
                Phase::WellFormed,
                self.sig_span,
                "broadcast function must be declared as proof",
            ));
        } else if self.locals[self.ret.index()].ty != Ty::Unit || self.ensures_ret_ty.is_some() {
            self.errors.push(UserError::new(
                Phase::WellFormed,
                self.sig_span,
                "broadcast function cannot have return type",
            ));
        } else if self
            .params
            .iter()
            .any(|id| self.locals[id.index()].mode != Mode::Spec)
        {
            self.errors.push(UserError::new(
                Phase::WellFormed,
                self.sig_span,
                "broadcast function must have spec parameters",
            ));
        } else if self.params.iter().any(|id| {
            matches!(
                self.locals[id.index()].ty,
                Ty::MutRef(_) | Ty::Ref { mutable: true, .. }
            )
        }) {
            self.errors.push(UserError::new(
                Phase::WellFormed,
                self.sig_span,
                "broadcast function cannot have &mut parameters",
            ));
        }
        if !self.type_params.is_empty()
            || self.tcx.def_kind(self.tcx.local_parent(self.def_id)) != DefKind::Mod
        {
            return refuse(
                "broadcast-contract",
                "a broadcast outside the local monomorphic free-function fragment",
                span,
            );
        }
        if self.params.iter().any(|id| self.locals[id.index()].mutable) {
            return refuse(
                "broadcast-contract",
                "a broadcast with a mutable by-value parameter binding",
                span,
            );
        }
        Ok(())
    }

    /// Capture only the declaration's outer header hints. Nested quantifier
    /// frames still own their binders and hints, exactly as ordinary quantifiers.
    pub(super) fn broadcast_header(
        &mut self,
        block: &'tcx hir::Block<'tcx>,
        requires: &mut Vec<trust_vc_vcir::Clause>,
        ensures: &mut Vec<trust_vc_vcir::Clause>,
        recommends: &mut Vec<trust_vc_vcir::Clause>,
        broadcast: bool,
    ) -> R<usize> {
        if !broadcast {
            return self.header(block, requires, ensures, recommends);
        }
        let start = self.trigger_marks.len();
        self.quant_frames.push(QuantFrame::default());
        self.broadcast_header_active = true;
        let result = self.header(block, requires, ensures, recommends);
        self.broadcast_header_active = false;
        let frame = self.quant_frames.pop().unwrap_or_default();
        let marks = self.trigger_marks.split_off(start);
        let length = result?;
        let at = self.sp(block.span);
        let conjunction = |clauses: &[trust_vc_vcir::Clause]| {
            clauses
                .iter()
                .fold(Expr::bool_lit(true, at), |body, clause| {
                    Expr::binary(BinOp::And, body, clause.expr.clone(), Ty::Bool, at)
                })
        };
        let body = Expr::binary(
            BinOp::Implies,
            conjunction(requires),
            conjunction(ensures),
            Ty::Bool,
            at,
        );
        let vars = self.params.clone();
        self.broadcast_triggers = if vars.is_empty() {
            Some(Vec::new())
        } else {
            self.triggers_for(&vars, &body, &marks, &frame, block.span)
        };
        Ok(length)
    }

    /// Record the trigger attributes of `e`, whose value is `value`: a
    /// `#[trigger]` mark, or the annotation of the quantifier being read.
    pub(super) fn trigger_attrs(&mut self, e: &hir::Expr<'_>, value: &Expr) {
        for (attr, _) in attrs::verus_attrs(self.tcx.hir_attrs(e.hir_id)) {
            match attr {
                VerusAttr::Trigger(None) => self.trigger_marks.push(Mark {
                    group: None,
                    term: value.clone(),
                }),
                VerusAttr::Trigger(Some(groups)) => {
                    for group in groups {
                        self.trigger_marks.push(Mark {
                            group: Some(group),
                            term: value.clone(),
                        });
                    }
                }
                VerusAttr::AutoTrigger | VerusAttr::AllTriggers => {
                    if let Some(frame) = self.quant_frames.last_mut() {
                        frame.auto = if attr == VerusAttr::AutoTrigger {
                            AutoMode::Auto
                        } else {
                            AutoMode::All
                        };
                    }
                }
                _ => {}
            }
        }
    }

    /// The closure a quantifier, choice or `assert forall` takes, through
    /// `closure_to_fn_spec`.
    fn closure_arg(&self, arg: &'tcx hir::Expr<'tcx>) -> R<&'tcx hir::Closure<'tcx>> {
        let mut arg = arg;
        if let hir::ExprKind::Call(func, [inner]) = arg.kind {
            let item = self.callee_def_id(func).and_then(|d| self.cx.verus_item(d));
            if item == Some(VerusItem::ClosureToFnSpec) {
                arg = inner;
            }
        }
        match arg.kind {
            hir::ExprKind::Closure(closure) => Ok(closure),
            _ => refuse(
                "quantifier",
                "the argument of a quantifier that is not a closure",
                arg.span,
            ),
        }
    }

    /// Bind the closure's parameters to new spec locals of `kind`.
    fn bind_params(
        &mut self,
        body: &'tcx hir::Body<'tcx>,
        kind: LocalKind,
    ) -> R<Vec<(LocalId, Ty, Span)>> {
        let mut out = Vec::new();
        for param in body.params {
            let PatKind::Binding(BindingMode(ByRef::No, _), pat_hir, ident, None) = param.pat.kind
            else {
                return refuse(
                    "quantifier",
                    "a quantifier variable that is not a plain name",
                    param.pat.span,
                );
            };
            let rustc_ty = self.pat_rty(param.pat);
            let Some(ty) = self.vc_ty(rustc_ty)? else {
                return refuse(
                    "type",
                    format!("`{ident}` has type `{rustc_ty}`"),
                    param.pat.span,
                );
            };
            let id = self.add_local(
                self.local_decl(
                    ident.name.as_str(),
                    ty.clone(),
                    Mode::Spec,
                    false,
                    kind,
                    param.pat.span,
                ),
                true,
            );
            self.local_ids.insert(pat_hir, id);
            out.push((id, ty, param.pat.span));
        }
        Ok(out)
    }

    /// Read `e` as the body of a quantifier: spec code, with the trigger
    /// annotations it holds.
    fn binder_body(&mut self, e: &'tcx hir::Expr<'tcx>) -> R<(Expr, Vec<Mark>, QuantFrame)> {
        let start = self.trigger_marks.len();
        self.quant_frames.push(QuantFrame::default());
        let read = self.spec(e);
        let frame = self.quant_frames.pop().unwrap_or_default();
        let marks = self.trigger_marks[start..].to_vec();
        if self.quant_frames.is_empty() {
            self.trigger_marks.truncate(start);
        }
        Ok((read?, marks, frame))
    }

    /// Verus's triggers for the variables `vars` of a quantifier with body
    /// `body`; `None` after recording Verus's error, which rejects the crate
    /// before anything is verified.
    fn triggers_for(
        &mut self,
        vars: &[LocalId],
        body: &Expr,
        marks: &[Mark],
        frame: &QuantFrame,
        span: Span,
    ) -> Option<Vec<Vec<Expr>>> {
        let locals = &self.locals;
        let local_ty = |id: LocalId| locals.get(id.index()).map(|l| l.ty.clone());
        let name = |id: LocalId| {
            locals
                .get(id.index())
                .map_or_else(String::new, |l| l.name.clone())
        };
        let q = Quantifier {
            vars,
            body,
            marks,
            with_triggers: &frame.with_triggers,
            auto: frame.auto,
            span: self.sp(span),
            local_ty: &local_ty,
            no_auto_trigger: &|_| false,
        };
        match triggers::build_triggers(&q, &name) {
            Ok(found) => Some(found),
            Err(error) => {
                let at = self.cx.span_of(error.span).unwrap_or(span);
                self.errors
                    .push(UserError::new(Phase::SstElaboration, at, error.message));
                None
            }
        }
    }

    /// `forall(|x| body)` or `exists(|x| body)`.
    pub(super) fn quant_expr(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        kind: QuantKind,
        arg: &'tcx hir::Expr<'tcx>,
        ctx: Ctx,
    ) -> R<Expr> {
        let span = e.span;
        if ctx == Ctx::Exec && !self.mode_rejected {
            return refuse("quantifier", "a quantifier in exec code", span);
        }
        let closure = self.closure_arg(arg)?;
        let body = self.tcx.hir_body(closure.body);
        let vars = self.bind_params(body, LocalKind::Bound)?;
        let (value, marks, frame) = self.binder_body(body.value)?;
        if value.ty != Ty::Bool {
            return Err(FnProblem::Rejected(UserError::new(
                Phase::RustToVir,
                body.value.span,
                MSG_QUANT_BOOL,
            )));
        }
        let ids: Vec<LocalId> = vars.iter().map(|(id, _, _)| *id).collect();
        let found = self.triggers_for(&ids, &value, &marks, &frame, span);
        let vars = vars.into_iter().map(|(id, ty, _)| (id, ty)).collect();
        let kind = match found {
            Some(triggers) => ExprKind::Quant {
                kind,
                vars,
                triggers,
                body: Box::new(value),
            },
            None => ExprKind::UntriggeredQuant {
                kind,
                vars,
                trigger_candidates: failed_candidates(marks, frame),
                body: Box::new(value),
            },
        };
        Ok(Expr::new(Ty::Bool, self.sp(span), kind))
    }

    /// `choose(|x| cond)`, or `choose_tuple(|x, y| cond)` when `tuple`.
    pub(super) fn choose_expr(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        arg: &'tcx hir::Expr<'tcx>,
        tuple: bool,
        ctx: Ctx,
    ) -> R<Expr> {
        let span = e.span;
        if ctx == Ctx::Exec && !self.mode_rejected {
            return refuse("quantifier", "a choice in exec code", span);
        }
        let ty = self.expr_ty(e)?;
        let closure = self.closure_arg(arg)?;
        let body = self.tcx.hir_body(closure.body);
        let vars = self.bind_params(body, LocalKind::Bound)?;
        let (cond, marks, frame) = self.binder_body(body.value)?;
        let reads: Vec<Expr> = vars
            .iter()
            .map(|(id, var_ty, at)| {
                Expr::read(
                    trust_vc_vcir::Place::local(*id),
                    var_ty.clone(),
                    self.sp(*at),
                )
            })
            .collect();
        let result = if tuple {
            let tuple_ty = Ty::Tuple(vars.iter().map(|(_, t, _)| t.clone()).collect());
            if tuple_ty != ty {
                return Err(FnProblem::Rejected(UserError::new(
                    Phase::RustToVir,
                    arg.span,
                    format!("expected choose_tuple to have type {tuple_ty:?}, found type {ty:?}"),
                )));
            }
            Expr::new(tuple_ty, self.sp(span), ExprKind::Tuple(reads))
        } else {
            let [read] = <[Expr; 1]>::try_from(reads).map_err(|_| {
                FnProblem::Rejected(UserError::new(Phase::RustToVir, arg.span, MSG_CHOOSE_ONE))
            })?;
            read
        };
        if cond.ty != Ty::Bool {
            return refuse("quantifier", "a choice whose condition is not a bool", span);
        }
        let ids: Vec<LocalId> = vars.iter().map(|(id, _, _)| *id).collect();
        let found = self.triggers_for(&ids, &cond, &marks, &frame, span);
        if result.ty != ty {
            return refuse(
                "quantifier",
                "a choice of another type than its value",
                span,
            );
        }
        let vars = vars.into_iter().map(|(id, ty, _)| (id, ty)).collect();
        let kind = match found {
            Some(triggers) => ExprKind::Choose {
                vars,
                triggers,
                cond: Box::new(cond),
                result: Box::new(result),
            },
            None => ExprKind::UntriggeredChoose {
                vars,
                trigger_candidates: failed_candidates(marks, frame),
                cond: Box::new(cond),
                result: Box::new(result),
            },
        };
        Ok(Expr::new(ty, self.sp(span), kind))
    }

    /// `with_triggers(((t1, t2), (t3,)), body)`: the groups belong to the
    /// quantifier being read; the value is the body's.
    pub(super) fn with_triggers(
        &mut self,
        groups: &'tcx hir::Expr<'tcx>,
        body: &'tcx hir::Expr<'tcx>,
    ) -> R<Expr> {
        let hir::ExprKind::Tup(groups) = groups.kind else {
            return refuse("trigger", "triggers that are not a tuple", groups.span);
        };
        let mut out = Vec::new();
        for group in groups {
            let hir::ExprKind::Tup(terms) = group.kind else {
                return refuse("trigger", "a trigger group that is not a tuple", group.span);
            };
            let mut read = Vec::new();
            for term in terms {
                read.push(self.spec(term)?);
            }
            out.push(read);
        }
        if let Some(frame) = self.quant_frames.last_mut() {
            frame.with_triggers = out;
        }
        self.spec(body)
    }

    /// `assert_forall_by(|x| { requires(r); ensures(e); proof })`.
    pub(super) fn assert_forall_by(
        &mut self,
        e: &'tcx hir::Expr<'tcx>,
        arg: &'tcx hir::Expr<'tcx>,
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<()> {
        let span = e.span;
        if ctx == Ctx::Exec && !self.mode_rejected {
            return refuse("assert-by", "assert forall in exec code", span);
        }
        let closure = self.closure_arg(arg)?;
        let body = self.tcx.hir_body(closure.body);
        let hir::ExprKind::Block(block, None) = body.value.kind else {
            return refuse(
                "assert-by",
                "an assert forall whose body is not a block",
                span,
            );
        };
        // The header: at most one `requires`, exactly one `ensures`.
        let mut requires = Vec::new();
        let mut ensures: Vec<&'tcx hir::Expr<'tcx>> = Vec::new();
        let mut requires_seen = false;
        let mut ensures_seen = false;
        let mut header_len = 0;
        for stmt in block.stmts {
            let (hir::StmtKind::Semi(call) | hir::StmtKind::Expr(call)) = stmt.kind else {
                break;
            };
            let hir::ExprKind::Call(func, [clause]) = call.kind else {
                break;
            };
            match self.callee_def_id(func).and_then(|d| self.cx.verus_item(d)) {
                Some(VerusItem::Requires) => {
                    if requires_seen {
                        return Err(FnProblem::Rejected(UserError::new(
                            Phase::RustToVir,
                            call.span,
                            MSG_HEADER_REQUIRES,
                        )));
                    }
                    requires_seen = true;
                    requires.extend(self.clause_elements(clause, VerusItem::Requires));
                }
                Some(VerusItem::Ensures) => {
                    if ensures_seen {
                        return Err(FnProblem::Rejected(UserError::new(
                            Phase::RustToVir,
                            call.span,
                            MSG_HEADER_ENSURES,
                        )));
                    }
                    ensures_seen = true;
                    ensures.extend(self.clause_elements(clause, VerusItem::Ensures));
                }
                Some(item) if item.is_header() => {
                    return refuse(
                        "assert-by",
                        "a header of assert forall the reader does not read",
                        call.span,
                    )
                }
                _ => break,
            }
            header_len += 1;
        }
        if requires.len() > 1 {
            return Err(FnProblem::Rejected(UserError::new(
                Phase::RustToVir,
                body.value.span,
                MSG_AFB_REQUIRES,
            )));
        }
        let &[ensure] = ensures.as_slice() else {
            return Err(FnProblem::Rejected(UserError::new(
                Phase::RustToVir,
                body.value.span,
                MSG_AFB_ENSURES,
            )));
        };
        if matches!(ensure.kind, hir::ExprKind::Closure(_)) {
            return refuse(
                "assert-by",
                "an assert forall ensures that names a value",
                ensure.span,
            );
        }

        // The dead end, with the variables as fresh locals of their types.
        let vars = self.bind_params(body, LocalKind::Let)?;
        let start = self.trigger_marks.len();
        self.quant_frames.push(QuantFrame::default());
        let read = (|| -> R<(Option<Expr>, Expr)> {
            let require = match requires.first().copied() {
                Some(r) => Some(self.spec(r)?),
                None => None,
            };
            Ok((require, self.spec(ensure)?))
        })();
        let frame = self.quant_frames.pop().unwrap_or_default();
        let marks = self.trigger_marks[start..].to_vec();
        if self.quant_frames.is_empty() {
            self.trigger_marks.truncate(start);
        }
        let (require, ensure_e) = read?;
        if ensure_e.ty != Ty::Bool || require.as_ref().is_some_and(|r| r.ty != Ty::Bool) {
            return refuse(
                "assert-by",
                "an assert forall clause that is not a bool",
                span,
            );
        }
        if self.is_plain_implies(ensure) && !vars.is_empty() {
            self.warnings
                .push(UserError::new(Phase::WellFormed, span, MSG_AFB_IMPLIES));
        }
        let mut inner = Vec::new();
        for (id, _, at) in &vars {
            inner.push(Stmt::new(
                self.sp(*at),
                StmtKind::Let {
                    local: *id,
                    init: None,
                },
            ));
        }
        if let Some(require) = &require {
            inner.push(Stmt::new(
                require.span,
                StmtKind::Assume {
                    expr: require.clone(),
                    attrs: ClauseAttrs::default(),
                },
            ));
        }
        let proof = &block.stmts[header_len..];
        let mut proof_out = Vec::new();
        for stmt in proof {
            self.stmt(stmt, Ctx::Proof, &mut proof_out)?;
        }
        if let Some(tail) = block.expr {
            self.stmt_expr(tail, Ctx::Proof, &mut proof_out)?;
        }
        inner.append(&mut proof_out);
        let site = self.site();
        inner.push(Stmt::new(
            self.sp(ensure.span),
            StmtKind::Assert {
                expr: ensure_e.clone(),
                site,
                attrs: self.clause_attrs_in(ensure.hir_id, true)?,
            },
        ));
        inner.push(Stmt::new(self.sp(span), StmtKind::Unreachable));
        let choice = self.temp(Ty::Bool, Ctx::Proof, span);
        let at = self.sp(span);
        out.push(Stmt::new(
            at,
            StmtKind::Let {
                local: choice,
                init: None,
            },
        ));
        out.push(Stmt::new(
            at,
            StmtKind::If {
                cond: self.read_local(choice, span),
                then_block: Block::new(inner),
                else_block: Block::default(),
            },
        ));

        // `forall|x| r ==> e`, over bound copies of the variables.
        let mut renamed: HashMap<LocalId, LocalId> = HashMap::new();
        let mut bound = Vec::new();
        for (id, ty, at) in &vars {
            let decl = self.locals[id.index()].clone();
            let copy = self.add_local(
                self.local_decl(
                    &decl.name,
                    ty.clone(),
                    Mode::Spec,
                    false,
                    LocalKind::Bound,
                    *at,
                ),
                true,
            );
            renamed.insert(*id, copy);
            bound.push((copy, ty.clone()));
        }
        let ensure_b = ensure_e.rename_locals(&renamed);
        let imply = match &require {
            Some(require) => Expr::binary(
                BinOp::Implies,
                require.rename_locals(&renamed),
                ensure_b,
                Ty::Bool,
                ensure_e.span,
            ),
            None => Expr::binary(
                BinOp::Implies,
                Expr::bool_lit(true, ensure_e.span),
                ensure_b,
                Ty::Bool,
                ensure_e.span,
            ),
        };
        let marks: Vec<Mark> = marks
            .into_iter()
            .map(|mark| Mark {
                group: mark.group,
                term: mark.term.rename_locals(&renamed),
            })
            .collect();
        let frame = QuantFrame {
            with_triggers: frame
                .with_triggers
                .iter()
                .map(|group| group.iter().map(|t| t.rename_locals(&renamed)).collect())
                .collect(),
            auto: frame.auto,
        };
        let ids: Vec<LocalId> = bound.iter().map(|(id, _)| *id).collect();
        let assumed = if ids.is_empty() {
            imply
        } else {
            let ensure_span = self.cx.span_of(ensure_e.span).unwrap_or(span);
            let Some(found) = self.triggers_for(&ids, &imply, &marks, &frame, ensure_span) else {
                return Ok(());
            };
            Expr::new(
                Ty::Bool,
                ensure_e.span,
                ExprKind::Quant {
                    kind: QuantKind::Forall,
                    vars: bound,
                    triggers: found,
                    body: Box::new(imply),
                },
            )
        };
        out.push(Stmt::new(
            ensure_e.span,
            StmtKind::Assume {
                expr: assumed,
                attrs: ClauseAttrs::default(),
            },
        ));
        Ok(())
    }

    /// Is `e` a `==>` (Verus's `imply`) with no trigger attribute and not
    /// wrapped in `with_triggers` (`well_formed.rs` sees a
    /// `BinaryOp::Implies` there)?
    fn is_plain_implies(&self, e: &hir::Expr<'_>) -> bool {
        let wrapped = attrs::verus_attrs(self.tcx.hir_attrs(e.hir_id))
            .iter()
            .any(|(attr, _)| {
                matches!(
                    attr,
                    VerusAttr::Trigger(_) | VerusAttr::AutoTrigger | VerusAttr::AllTriggers
                )
            });
        if wrapped {
            return false;
        }
        match e.kind {
            hir::ExprKind::Call(func, [_, _]) => {
                self.callee_def_id(func).and_then(|d| self.cx.verus_item(d))
                    == Some(VerusItem::Imply)
            }
            _ => false,
        }
    }
}
