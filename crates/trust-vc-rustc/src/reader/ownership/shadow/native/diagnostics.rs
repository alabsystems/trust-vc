//! Refusal diagnostics only. Native IDs/spans below are rendered to data and
//! never become selection, saved owners or source correspondence authority.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use super::*;
use rustc_ast::{
    self as ast,
    visit::{self, Visitor},
};

pub(super) fn ast_calls<'tcx>(
    tcx: TyCtxt<'tcx>,
    resolver: &ResolverAstLowering<'tcx>,
    krate: &ast::Crate,
) -> Vec<String> {
    let mut visitor = AstCalls {
        tcx,
        resolver,
        parents: Vec::new(),
        owners: Vec::new(),
        rows: Vec::new(),
        remaining: 262_144,
    };
    visitor.visit_crate(krate);
    visitor.rows
}
struct AstCalls<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    resolver: &'a ResolverAstLowering<'tcx>,
    parents: Vec<String>,
    owners: Vec<String>,
    rows: Vec<String>,
    remaining: usize,
}
impl<'ast> Visitor<'ast> for AstCalls<'_, '_> {
    fn visit_item(&mut self, item: &'ast ast::Item) {
        self.owners.push(format!(
            "ASTitem={:?} native_owner={:?}",
            item.id,
            self.resolver.owners.get(&item.id).map(|row| row.def_id)
        ));
        visit::walk_item(self, item);
        self.owners.pop();
    }
    fn visit_expr(&mut self, expression: &'ast ast::Expr) {
        if self.remaining == 0 || self.rows.len() >= 1024 {
            return;
        }
        self.remaining -= 1;
        let file = self
            .tcx
            .sess
            .source_map()
            .lookup_source_file(expression.span.lo());
        let range = (
            expression.span.lo().0 - file.start_pos.0,
            expression.span.hi().0 - file.start_pos.0,
        );
        if let ast::ExprKind::Call(callee, _) = &expression.kind {
            self.rows.push(format!("ASTcall={:?} range={range:?} owner={:?} parent_chain={:?} callee_node={:?} native_resolution={:?} file={:?}",
                expression.id, self.owners.last(), self.parents, callee.id, self.resolver.partial_res_map.get(&callee.id), file.name));
        }
        self.parents.push(format!(
            "node={:?} kind={} range={range:?}",
            expression.id,
            if matches!(expression.kind, ast::ExprKind::Paren(_)) {
                "Paren"
            } else {
                "Other"
            }
        ));
        visit::walk_expr(self, expression);
        self.parents.pop();
    }
}

pub(super) fn hir_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    typeck: &'tcx ty::TypeckResults<'tcx>,
    expression: &'tcx rustc_hir::Expr<'tcx>,
    expected: &Expected,
) -> String {
    let file = tcx
        .sess
        .source_map()
        .lookup_source_file(expression.span.lo());
    let range = (
        expression.span.lo().0 - file.start_pos.0,
        expression.span.hi().0 - file.start_pos.0,
    );
    let parent = tcx.parent_hir_id(expression.hir_id);
    let callee = match expression.kind {
        rustc_hir::ExprKind::Call(function, _) => match function.kind {
            rustc_hir::ExprKind::Path(ref path) => format!(
                "HIR={:?} res={:?} native_ty={:?}",
                function.hir_id,
                typeck.qpath_res(path, function.hir_id),
                typeck.expr_ty(function)
            ),
            _ => format!("HIR={:?} nonpath", function.hir_id),
        },
        _ => "not-call".into(),
    };
    let ast = tcx
        .sess
        .with_trust_compiler_state::<State, _>(|state| state.ast_calls.clone());
    let planned = expected
        .emitted
        .auxiliary_calls
        .iter()
        .map(|(role, call)| (*role, call.kind, expected.emitted.roles.get(role)))
        .collect::<Vec<_>>();
    format!("actual HIR={:?} owner={owner:?} parent={parent:?} parent_span={:?} range={range:?} callee={callee} planned={planned:?} actual_AST={ast:?}", expression.hir_id,tcx.hir_span(parent))
}
