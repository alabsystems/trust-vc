//! Fresh parser allocations bridging issued calls to canonical HIR spans.
//!
//! Only a direct, allocated Paren chain is followed, under the exact current
//! resolver/native owner and byte input. Rendered diagnostics are not inputs.
//! This map is private to this compiler session, not a saved owner or result.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0

use super::super::program::Site;
use super::*;
use rustc_ast::{
    self as ast,
    visit::{self, Visitor},
    NodeId,
};
use rustc_hir::def::{DefKind, Res};
use rustc_span::Span;
use std::collections::HashSet;

#[derive(Clone, Debug)]
pub(super) struct Parent {
    pub(super) node: NodeId,
    pub(super) child: NodeId,
    pub(super) span: Span,
}
#[derive(Clone, Debug)]
pub(super) struct Call {
    pub(super) role: (Site, Role),
    pub(super) kind: AuxiliaryKind,
    pub(super) node: NodeId,
    pub(super) callee_node: NodeId,
    pub(super) owner: LocalDefId,
    pub(super) callee: LocalDefId,
    pub(super) inner: Span,
    pub(super) canonical: Span,
    pub(super) parents: Vec<Parent>,
}
pub(super) struct Captured {
    pub(super) calls: BTreeMap<(Site, Role), Call>,
    pub(super) remaining: usize,
}
fn charge(remaining: &mut usize) -> Result<(), String> {
    *remaining = remaining
        .checked_sub(1)
        .ok_or("the shared native call allocation budget is exhausted")?;
    Ok(())
}

pub(super) fn capture<'tcx>(
    tcx: TyCtxt<'tcx>,
    resolver: &ResolverAstLowering<'tcx>,
    krate: &ast::Crate,
    expected: &Expected,
    functions: &BTreeMap<FunctionId, LocalDefId>,
    auxiliaries: &BTreeMap<AuxiliaryKind, LocalDefId>,
    parsed_source: &source_file::ParsedSource<'_>,
) -> Result<Captured, String> {
    let mut remaining = 262_144;
    let mut roles = BTreeMap::new();
    for (role, call) in &expected.emitted.auxiliary_calls {
        charge(&mut remaining)?;
        let range = expected
            .emitted
            .roles
            .get(role)
            .ok_or("the issued auxiliary call has no actual emitted range")?;
        if roles
            .insert((range.start, range.end), (*role, call.kind))
            .is_some()
        {
            return Err("issued auxiliary calls share an inner source range".into());
        }
    }
    let mut owners = HashSet::new();
    for owner in functions.values() {
        charge(&mut remaining)?;
        owners.insert(*owner);
    }
    let mut auxiliary_owners = HashSet::new();
    for owner in auxiliaries.values() {
        charge(&mut remaining)?;
        auxiliary_owners.insert(*owner);
    }
    let mut visitor = Capture {
        tcx,
        resolver,
        parsed_source,
        owners,
        auxiliary_owners,
        auxiliaries,
        roles,
        owner: None,
        parents: Vec::new(),
        calls: BTreeMap::new(),
        nodes: HashSet::new(),
        remaining,
        error: None,
    };
    visitor.visit_crate(krate);
    if let Some(error) = visitor.error {
        return Err(error);
    }
    // Every insertion came from roles and duplicates were rejected above.
    if visitor.calls.len() != expected.emitted.auxiliary_calls.len() {
        return Err("the native parser omitted an issued auxiliary call allocation".into());
    }
    Ok(Captured {
        calls: visitor.calls,
        remaining: visitor.remaining,
    })
}

struct Ancestor {
    node: NodeId,
    span: Span,
    /// Only an actual AST Paren is eligible, not a containing ancestor.
    child: Option<NodeId>,
    has_attributes: bool,
}
struct Capture<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    resolver: &'a ResolverAstLowering<'tcx>,
    parsed_source: &'a source_file::ParsedSource<'a>,
    owners: HashSet<LocalDefId>,
    auxiliary_owners: HashSet<LocalDefId>,
    auxiliaries: &'a BTreeMap<AuxiliaryKind, LocalDefId>,
    roles: BTreeMap<(usize, usize), ((Site, Role), AuxiliaryKind)>,
    owner: Option<LocalDefId>,
    parents: Vec<Ancestor>,
    calls: BTreeMap<(Site, Role), Call>,
    nodes: HashSet<NodeId>,
    remaining: usize,
    error: Option<String>,
}
impl<'ast> Visitor<'ast> for Capture<'_, '_> {
    fn visit_item(&mut self, item: &'ast ast::Item) {
        let old = self.owner;
        self.owner = self.resolver.owners.get(&item.id).map(|row| row.def_id);
        visit::walk_item(self, item);
        self.owner = old;
    }
    fn visit_expr(&mut self, expression: &'ast ast::Expr) {
        if self.error.is_some() {
            return;
        }
        if self.remaining == 0 || self.parents.len() >= 128 {
            self.error =
                Some("the whole parser call allocation walk exceeds its shared bound".into());
            return;
        }
        self.remaining -= 1;
        if let ast::ExprKind::Call(callee, _) = &expression.kind {
            if let Err(error) = self.call(expression, callee) {
                self.error = Some(error);
                return;
            }
        }
        self.parents.push(Ancestor {
            node: expression.id,
            span: expression.span,
            child: match &expression.kind {
                ast::ExprKind::Paren(child) => Some(child.id),
                _ => None,
            },
            has_attributes: !expression.attrs.is_empty(),
        });
        visit::walk_expr(self, expression);
        self.parents.pop();
    }
}
impl Capture<'_, '_> {
    fn call(&mut self, expression: &ast::Expr, callee: &ast::Expr) -> Result<(), String> {
        let range = self
            .parsed_source
            .range(self.tcx.sess.source_map(), expression.span)?;
        let resolved = self
            .resolver
            .partial_res_map
            .get(&callee.id)
            .and_then(|row| row.full_res());
        let target = match resolved {
            Some(Res::Def(DefKind::Fn, target)) => target.as_local(),
            _ => None,
        };
        let Some((role, kind)) = self.roles.get(&range).copied() else {
            if target.is_some_and(|target| self.auxiliary_owners.contains(&target)) {
                return Err("an actual auxiliary AST call has no issued inner range".into());
            }
            return Ok(());
        };
        let actual_callee = self
            .auxiliaries
            .get(&kind)
            .copied()
            .ok_or("an issued AST call has no allocated auxiliary declaration")?;
        if target != Some(actual_callee) {
            return Err("a planned auxiliary call changed its actual native allocation/relationship at the parser target".into());
        }
        let owner = self
            .owner
            .filter(|owner| self.owners.contains(owner))
            .ok_or("the issued AST call is outside its actual generated function allocation")?;
        if !expression.attrs.is_empty()
            || !callee.attrs.is_empty()
            || !matches!(&callee.kind, ast::ExprKind::Path(..))
            || expression.id == callee.id
            || !self.nodes.insert(expression.id)
            || !self.nodes.insert(callee.id)
        {
            return Err(
                "an auxiliary AST call changed its exact bytes, allocation or supported syntax"
                    .into(),
            );
        }
        let mut canonical = expression.span;
        let mut current = expression.id;
        let mut parents = Vec::new();
        for parent in self.parents.iter().rev() {
            if parent.child != Some(current) {
                break;
            }
            charge(&mut self.remaining)?;
            self.parsed_source
                .range(self.tcx.sess.source_map(), parent.span)?;
            if parent.has_attributes
                || parent.span.ctxt() != canonical.ctxt()
                || !parent.span.contains(canonical)
                || !self.nodes.insert(parent.node)
            {
                return Err(
                    "an auxiliary call has an unrepresented or reused direct Paren allocation"
                        .into(),
                );
            }
            parents.push(Parent {
                node: parent.node,
                child: current,
                span: parent.span,
            });
            canonical = parent.span;
            current = parent.node;
        }
        charge(&mut self.remaining)?;
        if self
            .calls
            .insert(
                role,
                Call {
                    role,
                    kind,
                    node: expression.id,
                    callee_node: callee.id,
                    owner,
                    callee: actual_callee,
                    inner: expression.span,
                    canonical,
                    parents,
                },
            )
            .is_some()
        {
            return Err("the native parser published an issued auxiliary call twice".into());
        }
        Ok(())
    }
}
