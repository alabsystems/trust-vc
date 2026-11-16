//! Formal field modes for source-ordered native constructor operands.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_hir as hir;
use trust_vc_vcir::{DeclProphecy, Expr, ExprKind, Mode, Stmt, StmtKind};

use super::{refuse, Ctx, FnReader, R};

pub(super) fn transport_mode(ctx: Ctx, formal: Mode) -> Mode {
    match (ctx.local_mode(), formal) {
        (Mode::Spec, _) | (_, Mode::Spec) => Mode::Spec,
        (Mode::Proof, _) | (_, Mode::Proof) => Mode::Proof,
        _ => Mode::Exec,
    }
}

impl<'tcx> FnReader<'_, 'tcx> {
    /// Freeze each earlier operand before later effects using its formal
    /// field mode. A Spec field observes storage without consuming it.
    pub(super) fn constructor_operands(
        &mut self,
        sources: &[&'tcx hir::Expr<'tcx>],
        modes: &[Mode],
        ctx: Ctx,
        out: &mut Vec<Stmt>,
    ) -> R<Vec<Expr>> {
        if sources.len() != modes.len() {
            return refuse(
                "field-mode",
                "constructor operands lost their formal field modes",
                self.tcx.def_span(self.def_id),
            );
        }
        let mut values: Vec<Expr> = Vec::new();
        for (source, formal) in sources.iter().zip(modes) {
            let argument_ctx = match formal {
                Mode::Spec => Ctx::Spec,
                Mode::Proof if ctx == Ctx::Exec => Ctx::Proof,
                _ => ctx,
            };
            let mark = out.len();
            let value = self.expr_adjusted(source, argument_ctx, out)?;
            if out.len() > mark {
                let mut saves = Vec::new();
                for ((previous, original), formal) in values.iter_mut().zip(sources).zip(modes) {
                    if matches!(previous.kind, ExprKind::Lit(_)) {
                        continue;
                    }
                    let local = self.temp_with_mode(
                        previous.ty.clone(),
                        transport_mode(ctx, *formal),
                        original.span,
                    );
                    if self.locals[local.index()].mode == Mode::Spec {
                        self.locals[local.index()].prophecy = DeclProphecy::DelayedInfer;
                    }
                    saves.push(Stmt::new(
                        self.sp(original.span),
                        StmtKind::Let {
                            local,
                            init: Some(previous.clone()),
                        },
                    ));
                    *previous = self.read_local(local, original.span);
                }
                out.splice(mark..mark, saves);
            }
            values.push(value);
        }
        Ok(values)
    }
}
