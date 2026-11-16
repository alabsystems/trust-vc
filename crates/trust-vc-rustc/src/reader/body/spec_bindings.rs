//! Pure Spec patterns lowered as expression bindings.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use rustc_ast::{BindingMode, ByRef};
use rustc_hir::{self as hir, PatKind};
use rustc_span::Span;
use trust_vc_vcir::{Expr, LocalId, LocalKind, Mode, StmtKind};

use super::{refuse, Ctx, FnReader, R};

impl<'tcx> FnReader<'_, 'tcx> {
    /// Pure patterns become nested expression lets; even a wildcard retains
    /// evaluation of the initializer and its checks.
    pub(super) fn spec_value_bindings(
        &mut self,
        pat: &'tcx hir::Pat<'tcx>,
        value: Expr,
        span: Span,
    ) -> R<Vec<(LocalId, Expr, Span)>> {
        if let PatKind::Binding(BindingMode(ByRef::No, _), pat_hir, ident, None) = pat.kind {
            // Keep the existing plain Spec-let path: a rejected proof block
            // can translate to Unit while its binding retains the compiler
            // type. The recorded source error must reach its proper phase.
            let rustc_ty = self.pat_rty(pat);
            let Some(ty) = self.vc_ty(rustc_ty)? else {
                return refuse("type", format!("`{ident}` has type `{rustc_ty}`"), pat.span);
            };
            let id = self.add_local(
                self.local_decl(
                    ident.name.as_str(),
                    ty,
                    self.checked_binding_mode(pat, Ctx::Spec)?,
                    false,
                    LocalKind::Bound,
                    pat.span,
                ),
                true,
            );
            self.local_ids.insert(pat_hir, id);
            return Ok(vec![(id, value, span)]);
        }
        let id = self.add_local(
            self.local_decl(
                "_pattern",
                value.ty.clone(),
                Mode::Spec,
                false,
                LocalKind::Bound,
                span,
            ),
            true,
        );
        let mut bindings = vec![(id, value, span)];
        let value = self.read_local(id, span);
        let mut stmts = Vec::new();
        self.value_let_bindings(pat, Some(value), Ctx::Spec, LocalKind::Bound, &mut stmts)?;
        for stmt in stmts {
            let StmtKind::Let {
                local,
                init: Some(value),
            } = stmt.kind
            else {
                return refuse("let-pattern", "a non-binding in a pure value pattern", span);
            };
            bindings.push((local, value, span));
        }
        Ok(bindings)
    }
}
