//! Verus's checks of the attributes on the expressions of a function body,
//! in the order Verus meets them while it builds VIR.
//!
//! Verus reads the attributes of every expression it converts
//! (`rust_to_vir_expr.rs`). Before the expression's operands,
//! `expr_to_vir_innermost` parses them (`get_verifier_attrs`: the first
//! attribute it cannot parse is the function's error, and so is a `rustc_*`
//! attribute it does not ignore) and rejects `verifier::truncate` on
//! anything but a cast. After the operands, `expr_to_vir` parses them again
//! (`get_trigger`) and rejects a second proof note or custom error
//! (`get_proof_note_annotation`). An attribute written before `r == 5`
//! belongs to `r`, so these checks reach every operand, not only clauses
//! and statements.
//!
//! A `DropTemps` (the wrapper of an `if` or `while` condition) is
//! transparent: its operand's attributes are checked, before and after.
//!
//! In a function marked `external_body`, Verus converts only what the
//! header needs: the body's blocks and the calls and closures among its
//! statements get the first checks (a call's arguments are read only for a
//! header call or a tuple constructor), and every other statement
//! expression only the second ones; `let`s and items are skipped.
//!
//! [`first_problem`] walks a function the same way and returns the first
//! problem with the expression at which Verus raises it. The reader raises
//! it when it reaches that expression, or at the end of the function if it
//! never does.

use rustc_hir::def::{CtorKind, DefKind, Res};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::{self as hir, HirId};
use rustc_middle::ty::{TyCtxt, TypeckResults};

use super::attrs::{self, AttrProblem};
use super::Cx;
use crate::messages::attr as msg;
use crate::verus_items::VerusItem;

/// The first attribute problem Verus finds in a function.
#[derive(Debug, Clone)]
pub(crate) struct AttrFinding {
    /// The expression whose conversion raises it.
    pub at: HirId,
    /// Raised after the expression's operands were converted (the second
    /// parse), not before them.
    pub after: bool,
    /// What Verus reports.
    pub problem: AttrProblem,
}

type W = Result<(), AttrFinding>;

/// The first attribute problem in the body and header of `def_id`, in
/// Verus's order; `None` when there is none or the function has no body.
pub(crate) fn first_problem(cx: &Cx<'_>, def_id: LocalDefId) -> Option<AttrFinding> {
    let tcx = cx.tcx;
    let body = tcx.hir_maybe_body_owned_by(def_id)?;
    let hir_id = tcx.local_def_id_to_hir_id(def_id);
    let external_body = attrs::item_attrs(tcx.hir_attrs(hir_id)).external_body;
    let walk = Walk {
        cx,
        tcx,
        typeck: tcx.typeck(def_id),
    };
    walk.expr(body.value, external_body).err()
}

struct Walk<'a, 'tcx> {
    cx: &'a Cx<'tcx>,
    tcx: TyCtxt<'tcx>,
    typeck: &'tcx TypeckResults<'tcx>,
}

impl<'tcx> Walk<'_, 'tcx> {
    /// `expr_to_vir` on `e`; `eb` is Verus's `external_body` reading.
    fn expr(&self, e: &'tcx hir::Expr<'tcx>, eb: bool) -> W {
        let inner = e.peel_drop_temps();
        let converted = !eb
            || matches!(
                inner.kind,
                hir::ExprKind::Block(..) | hir::ExprKind::Call(..) | hir::ExprKind::Closure(..)
            );
        if converted {
            self.before(inner)?;
            self.operands(inner, eb)?;
        }
        self.after(inner)
    }

    /// The checks of `expr_to_vir_innermost`, before the operands.
    fn before(&self, e: &hir::Expr<'_>) -> W {
        let found = |problem| {
            Err(AttrFinding {
                at: e.hir_id,
                after: false,
                problem,
            })
        };
        let parse = match attrs::verus_parse(self.tcx.hir_attrs(e.hir_id)) {
            Ok(parse) => parse,
            Err(problem) => return found(problem),
        };
        if let Some(span) = parse.deprecated {
            return found(AttrProblem::Unmodelled(
                span,
                "a deprecated attribute on an expression, which Verus warns about".to_string(),
            ));
        }
        if let Some((name, span)) = parse.rustc {
            return found(AttrProblem::Unmodelled(
                span,
                format!("`{name}` on an expression"),
            ));
        }
        if parse.truncate && !self.is_cast(e) {
            return found(AttrProblem::Error(
                e.span,
                msg::TRUNCATE_NOT_CAST.to_string(),
            ));
        }
        Ok(())
    }

    /// The checks of `expr_to_vir` after the operands: the attributes
    /// parsed again, and at most one proof note.
    fn after(&self, e: &hir::Expr<'_>) -> W {
        let found = |problem| {
            Err(AttrFinding {
                at: e.hir_id,
                after: true,
                problem,
            })
        };
        let parse = match attrs::verus_parse(self.tcx.hir_attrs(e.hir_id)) {
            Ok(parse) => parse,
            Err(problem) => return found(problem),
        };
        if let Some(second) = parse.notes.get(1) {
            return found(AttrProblem::Error(*second, msg::DUPLICATE_NOTE.to_string()));
        }
        Ok(())
    }

    /// The operands of `e` Verus converts, in its order.
    fn operands(&self, e: &'tcx hir::Expr<'tcx>, eb: bool) -> W {
        use hir::ExprKind as K;
        match e.kind {
            K::Block(block, _) | K::Loop(block, ..) => self.block(block, eb),
            K::Closure(closure) => self.expr(self.tcx.hir_body(closure.body).value, eb),
            K::Call(func, args) => {
                let callee = self.callee(func);
                // A reveal's arguments are read by Verus's reveal handling,
                // not converted.
                if callee.and_then(|d| self.cx.verus_item(d)) == Some(VerusItem::RevealHide) {
                    return Ok(());
                }
                if eb {
                    if callee.is_some_and(|d| self.external_body_header(d)) {
                        return args.iter().try_for_each(|a| self.expr(a, false));
                    }
                    // A tuple constructor's arguments are converted
                    // (`expr_tuple_datatype_ctor_to_vir`), still in the
                    // `external_body` reading.
                    if self.is_tuple_ctor(func) {
                        return args.iter().try_for_each(|a| self.expr(a, eb));
                    }
                    return Ok(());
                }
                if !matches!(func.kind, K::Path(_)) {
                    self.expr(func, eb)?;
                }
                args.iter().try_for_each(|a| self.expr(a, eb))
            }
            K::MethodCall(_, receiver, args, _) => {
                self.expr(receiver, eb)?;
                args.iter().try_for_each(|a| self.expr(a, eb))
            }
            K::Array(elems) | K::Tup(elems) => elems.iter().try_for_each(|x| self.expr(x, eb)),
            K::Assign(lhs, rhs, _) | K::AssignOp(_, lhs, rhs) => self.assign(e, lhs, rhs, eb),
            K::Binary(_, a, b) | K::Index(a, b, _) => {
                self.expr(a, eb)?;
                self.expr(b, eb)
            }
            K::Unary(_, x)
            | K::Cast(x, _)
            | K::Type(x, _)
            | K::AddrOf(_, _, x)
            | K::Field(x, _)
            | K::DropTemps(x)
            | K::Use(x, _)
            | K::Become(x)
            | K::Repeat(x, _)
            | K::Yield(x, _)
            | K::UnsafeBinderCast(_, x, _) => self.expr(x, eb),
            K::Let(let_expr) => self.expr(let_expr.init, eb),
            K::If(cond, then_expr, else_expr) => {
                self.expr(cond, eb)?;
                self.expr(then_expr, eb)?;
                else_expr.map_or(Ok(()), |x| self.expr(x, eb))
            }
            K::Match(scrutinee, arms, _) => {
                self.expr(scrutinee, eb)?;
                for arm in arms {
                    if let Some(guard) = arm.guard {
                        self.expr(guard, eb)?;
                    }
                    self.expr(arm.body, eb)?;
                }
                Ok(())
            }
            K::Break(_, value) | K::Ret(value) => value.map_or(Ok(()), |x| self.expr(x, eb)),
            K::Struct(_, fields, tail) => {
                for field in fields {
                    self.expr(field.expr, eb)?;
                }
                match tail {
                    hir::StructTailExpr::Base(base) => self.expr(base, eb),
                    _ => Ok(()),
                }
            }
            _ => Ok(()),
        }
    }

    /// An assignment (`expr_assign_to_vir_innermost`). Verus converts the
    /// target as a place and then takes its location (`place_to_loc`); a
    /// trigger or proof note on the target, or on a place it is projected
    /// from, has turned that place into a temporary, whose location is
    /// Verus's error. An indexed target is a call of `index_set`: only the
    /// indexed place is located, after the right-hand side.
    fn assign(
        &self,
        e: &hir::Expr<'_>,
        lhs: &'tcx hir::Expr<'tcx>,
        rhs: &'tcx hir::Expr<'tcx>,
        eb: bool,
    ) -> W {
        let found = |at: HirId, span| {
            let problem = if self.cx.opts.new_mut_ref {
                AttrProblem::Unmodelled(
                    span,
                    "a trigger or proof note on an assignment target with new-mut-ref".to_string(),
                )
            } else {
                AttrProblem::Error(span, msg::COMPLEX_MUT_ARG.to_string())
            };
            Err(AttrFinding {
                at,
                after: true,
                problem,
            })
        };
        self.expr(lhs, eb)?;
        if let hir::ExprKind::Index(target, ..) = lhs.kind {
            self.expr(rhs, eb)?;
            return match self.wrapped_place(target, true) {
                Some(span) => found(e.hir_id, span),
                None => Ok(()),
            };
        }
        if let Some(span) = self.wrapped_place(lhs, true) {
            return found(lhs.hir_id, span);
        }
        self.expr(rhs, eb)
    }

    /// The span of an expression on the place chain of `e` that
    /// `expr_to_vir` wraps in a trigger or proof note. `wrapped` says `e`
    /// itself goes through `expr_to_vir`: a field's base does, the operand
    /// of a `*` does not (`deref_expr_to_vir` converts it with
    /// `expr_to_vir_inner`).
    fn wrapped_place(&self, e: &hir::Expr<'_>, wrapped: bool) -> Option<rustc_span::Span> {
        if wrapped
            && attrs::verus_parse(self.tcx.hir_attrs(e.hir_id)).is_ok_and(|parse| parse.wraps)
        {
            return Some(e.span);
        }
        match e.kind {
            hir::ExprKind::Field(base, _) => self.wrapped_place(base, true),
            hir::ExprKind::Unary(hir::UnOp::Deref, operand) => self.wrapped_place(operand, false),
            _ => None,
        }
    }

    /// A block's statements and tail (`block_to_vir`, `stmt_to_vir`).
    fn block(&self, block: &'tcx hir::Block<'tcx>, eb: bool) -> W {
        for stmt in block.stmts {
            match stmt.kind {
                hir::StmtKind::Expr(e) | hir::StmtKind::Semi(e) => {
                    if !self.is_dummy_capture(e) {
                        self.expr(e, eb)?;
                    }
                }
                hir::StmtKind::Let(local) if !eb => {
                    if let Some(init) = local.init {
                        if self.is_dummy_capture(init) {
                            continue;
                        }
                        self.expr(init, eb)?;
                    }
                    if let Some(els) = local.els {
                        self.block(els, eb)?;
                    }
                }
                hir::StmtKind::Item(item) if !eb => {
                    // `stmt_to_vir` parses a nested item's attributes before
                    // anything else about it.
                    let hir_id = item.hir_id();
                    let found = |problem| {
                        Err(AttrFinding {
                            at: hir_id,
                            after: false,
                            problem,
                        })
                    };
                    match attrs::verus_parse(self.tcx.hir_attrs(hir_id)) {
                        Err(problem) => return found(problem),
                        Ok(parse) => {
                            if let Some((name, span)) = parse.rustc {
                                return found(AttrProblem::Unmodelled(
                                    span,
                                    format!("`{name}` on an item in a body"),
                                ));
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        block.expr.map_or(Ok(()), |tail| self.expr(tail, eb))
    }

    /// The function a callee expression names.
    fn callee(&self, func: &hir::Expr<'_>) -> Option<DefId> {
        let hir::ExprKind::Path(qpath) = &func.kind else {
            return None;
        };
        match self.typeck.qpath_res(qpath, func.hir_id) {
            Res::Def(DefKind::Fn | DefKind::AssocFn, def_id) => Some(def_id),
            _ => None,
        }
    }

    /// A tuple struct or variant constructor, or `Self` as one.
    fn is_tuple_ctor(&self, func: &hir::Expr<'_>) -> bool {
        let hir::ExprKind::Path(qpath) = &func.kind else {
            return false;
        };
        matches!(
            self.typeck.qpath_res(qpath, func.hir_id),
            Res::Def(DefKind::Ctor(_, CtorKind::Fn), _) | Res::SelfCtor(_)
        )
    }

    /// The header calls whose arguments Verus reads in an `external_body`
    /// function (`fn_call_to_vir.rs`, the `bctx.external_body` test).
    fn external_body_header(&self, callee: DefId) -> bool {
        match self.cx.verus_item(callee) {
            Some(VerusItem::Requires | VerusItem::Ensures | VerusItem::Recommends) => true,
            Some(VerusItem::OtherHeader) => matches!(
                self.tcx.item_name(callee).as_str(),
                "returns"
                    | "opens_invariants"
                    | "opens_invariants_none"
                    | "opens_invariants_any"
                    | "opens_invariants_except"
                    | "no_unwind"
                    | "no_unwind_when"
                    | "extra_dependency"
            ),
            _ => false,
        }
    }

    /// Part of the closure encoding, skipped by Verus
    /// (`is_ignorable_dummy_capture_operation`).
    fn is_dummy_capture(&self, e: &hir::Expr<'_>) -> bool {
        let hir::ExprKind::Call(func, _) = e.kind else {
            return false;
        };
        matches!(
            self.callee(func).and_then(|d| self.cx.verus_item(d)),
            Some(VerusItem::DummyCaptureNew | VerusItem::DummyCaptureConsume)
        )
    }

    /// A cast: `x as T`, or a call of `spec_cast_integer`.
    fn is_cast(&self, e: &hir::Expr<'_>) -> bool {
        match e.kind {
            hir::ExprKind::Cast(..) => true,
            hir::ExprKind::Call(func, _) => {
                let hir::ExprKind::Path(qpath) = &func.kind else {
                    return false;
                };
                match self.typeck.qpath_res(qpath, func.hir_id) {
                    Res::Def(_, def_id) => {
                        self.cx.verus_item(def_id) == Some(VerusItem::SpecCastInteger)
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }
}
