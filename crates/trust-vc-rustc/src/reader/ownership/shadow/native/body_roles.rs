//! Transaction-local parser allocations for ordinary body correspondence.
//!
//! Ranges locate actual parser nodes. They never replace node identity, native
//! owner/resolution/type checks, or the original-source correspondence. A
//! struct's implicit non-enum variant is a layout role of its actual item;
//! there is no invented second parser NodeId for that variant.

use super::*;
use rustc_ast::{
    self as ast,
    visit::{self, Visitor},
    NodeId,
};
use rustc_hir::{self as hir, def::Res};
use std::collections::HashMap;

mod check;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Family {
    Function,
    Adt,
    StructLayout,
    FieldType,
    Binding,
    Expression,
}

#[derive(Clone, Debug)]
struct Allocation {
    node: NodeId,
    owner: LocalDefId,
    family: Family,
    inner: rustc_span::Span,
    canonical: rustc_span::Span,
    parent: Option<NodeId>,
}

pub(super) struct Captured {
    nodes: BTreeMap<(Site, Role), Allocation>,
    pub(super) remaining: usize,
}

fn charge(remaining: &mut usize) -> Result<(), String> {
    *remaining = remaining
        .checked_sub(1)
        .ok_or("the existing whole native allocation/body budget is exhausted")?;
    Ok(())
}

/// Extends the SAME allocation account already consumed by auxiliary capture.
pub(super) fn capture<'tcx>(
    tcx: TyCtxt<'tcx>,
    resolver: &ResolverAstLowering<'tcx>,
    krate: &ast::Crate,
    expected: &Expected,
    functions: &BTreeMap<FunctionId, LocalDefId>,
    adts: &BTreeMap<AdtId, LocalDefId>,
    parsed: &source_file::ParsedSource<'_>,
    remaining: usize,
) -> Result<Captured, String> {
    let mut walk = Capture {
        tcx,
        resolver,
        expected,
        parsed,
        owner: None,
        nodes: BTreeMap::new(),
        parents: Vec::new(),
        remaining,
        error: None,
        locators: BTreeMap::new(),
        declarations: HashMap::new(),
        node_families: HashMap::new(),
        current_role: None,
    };
    for function in &expected.program.functions {
        charge(&mut walk.remaining)?;
        let owner = *functions
            .get(&function.id)
            .ok_or("missing actual native function allocation")?;
        if walk
            .declarations
            .insert(owner, (function.site, Role::Function, None))
            .is_some()
        {
            return Err("an ordinary function allocation has multiple issued owners".into());
        }
    }
    for adt in &expected.program.adts {
        charge(&mut walk.remaining)?;
        if adt.kind != AdtKind::Struct || adt.variants.len() != 1 {
            return Err(
                "ordinary body correspondence currently requires genuine struct declarations"
                    .into(),
            );
        }
        let owner = *adts
            .get(&adt.id)
            .ok_or("missing actual native struct allocation")?;
        if walk
            .declarations
            .insert(owner, (adt.site, Role::Adt, Some(adt.variants[0].site)))
            .is_some()
        {
            return Err("an ordinary ADT allocation has multiple issued owners".into());
        }
    }
    for (role, range) in &expected.emitted.roles {
        charge(&mut walk.remaining)?;
        if matches!(role.1, Role::Expression | Role::Binding | Role::Field) {
            if walk
                .locators
                .insert((range.start, range.end), *role)
                .is_some()
            {
                return Err("distinct ordinary roles share one parser locator".into());
            }
        } else if !matches!(role.1, Role::Function | Role::Adt | Role::Variant) {
            return Err(
                "this ordinary-body transaction still lacks pattern/arm/auxiliary role capture"
                    .into(),
            );
        }
    }
    walk.visit_crate(krate);
    if let Some(error) = walk.error {
        return Err(error);
    }
    if walk.nodes.len() != expected.emitted.roles.len()
        || walk.nodes.keys().ne(expected.emitted.roles.keys())
    {
        return Err(
            "the actual parser did not publish every issued ordinary role exactly once".into(),
        );
    }
    Ok(Captured {
        nodes: walk.nodes,
        remaining: walk.remaining,
    })
}

struct Parent {
    node: NodeId,
    span: rustc_span::Span,
    paren_child: Option<NodeId>,
    attributed: bool,
}
struct Capture<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    resolver: &'a ResolverAstLowering<'tcx>,
    expected: &'a Expected,
    parsed: &'a source_file::ParsedSource<'a>,
    owner: Option<LocalDefId>,
    nodes: BTreeMap<(Site, Role), Allocation>,
    parents: Vec<Parent>,
    remaining: usize,
    error: Option<String>,
    locators: BTreeMap<(usize, usize), (Site, Role)>,
    declarations: HashMap<LocalDefId, (Site, Role, Option<Site>)>,
    node_families: HashMap<NodeId, Family>,
    current_role: Option<NodeId>,
}
impl Capture<'_, '_> {
    fn record(
        &mut self,
        role: (Site, Role),
        node: NodeId,
        family: Family,
        inner: rustc_span::Span,
        canonical: rustc_span::Span,
        parent: Option<NodeId>,
    ) -> Result<(), String> {
        charge(&mut self.remaining)?;
        let owner = self
            .owner
            .ok_or("an ordinary parser role has no actual native owner")?;
        if !self.expected.emitted.roles.contains_key(&role) {
            return Err("an actual parser allocation has no issued ordinary role".into());
        }
        if let Some(old) = self.node_families.get(&node) {
            if !(*old == Family::Adt && family == Family::StructLayout) {
                return Err("one actual parser node was reused for distinct ordinary roles".into());
            }
        } else {
            self.node_families.insert(node, family);
        }
        if self
            .nodes
            .insert(
                role,
                Allocation {
                    node,
                    owner,
                    family,
                    inner,
                    canonical,
                    parent,
                },
            )
            .is_some()
        {
            return Err("the parser published an ordinary role more than once".into());
        }
        Ok(())
    }
    fn declaration(&mut self, item: &ast::Item) -> Result<(), String> {
        let Some(owner) = self.owner else {
            return Ok(());
        };
        let Some((site, role, variant)) = self.declarations.get(&owner).copied() else {
            return Ok(());
        };
        let family = match role {
            Role::Function if matches!(item.kind, ast::ItemKind::Fn(..)) => Family::Function,
            Role::Adt if matches!(item.kind, ast::ItemKind::Struct(..)) => Family::Adt,
            _ => return Err("the actual declaration allocation changed its parser kind".into()),
        };
        let range = self
            .expected
            .emitted
            .roles
            .get(&(site, role))
            .ok_or("missing declaration range")?;
        if self.parsed.range(self.tcx.sess.source_map(), item.span)? != (range.start, range.end) {
            return Err("an actual declaration changed its issued parser locator".into());
        }
        self.record((site, role), item.id, family, item.span, item.span, None)?;
        if let Some(variant) = variant {
            self.record(
                (variant, Role::Variant),
                item.id,
                Family::StructLayout,
                item.span,
                item.span,
                None,
            )?;
        }
        Ok(())
    }
    fn located(
        &mut self,
        node: NodeId,
        family: Family,
        span: rustc_span::Span,
    ) -> Result<(), String> {
        if self.owner.is_none() {
            return Ok(());
        }
        let range = self.parsed.range(self.tcx.sess.source_map(), span)?;
        let Some(role) = self.locators.get(&range).copied() else {
            return Ok(());
        };
        if !matches!(
            (role.1, family),
            (Role::Expression, Family::Expression)
                | (Role::Binding, Family::Binding)
                | (Role::Field, Family::FieldType)
        ) {
            return Err(
                "an issued ordinary role resolved to a different actual parser node kind".into(),
            );
        }
        let mut canonical = span;
        let mut current = node;
        if family == Family::Expression {
            for parent in self.parents.iter().rev() {
                if parent.paren_child != Some(current) {
                    break;
                }
                charge(&mut self.remaining)?;
                if parent.attributed
                    || parent.span.ctxt() != canonical.ctxt()
                    || !parent.span.contains(canonical)
                {
                    return Err(
                        "an ordinary expression changed its direct parser Paren chain".into(),
                    );
                }
                canonical = parent.span;
                current = parent.node;
            }
        }
        let parent = self.current_role;
        self.record(role, node, family, span, canonical, parent)
    }
}
impl<'ast> Visitor<'ast> for Capture<'_, '_> {
    fn visit_item(&mut self, item: &'ast ast::Item) {
        if self.error.is_some() {
            return;
        }
        let old = self.owner;
        self.owner = self
            .resolver
            .owners
            .get(&item.id)
            .map(|owner| owner.def_id)
            .filter(|owner| self.declarations.contains_key(owner));
        if let Err(error) = self.declaration(item) {
            self.error = Some(error);
        }
        if self.error.is_none() && self.owner.is_some() {
            visit::walk_item(self, item);
        }
        self.owner = old;
    }
    fn visit_expr(&mut self, expression: &'ast ast::Expr) {
        if self.error.is_some() {
            return;
        }
        if !expression.attrs.is_empty() {
            self.error = Some("an ordinary expression has unissued native attributes".into());
            return;
        }
        if self.parents.len() >= 128 {
            self.error = Some("ordinary parser body exceeds its depth bound".into());
            return;
        }
        if let Err(error) = charge(&mut self.remaining)
            .and_then(|_| self.located(expression.id, Family::Expression, expression.span))
        {
            self.error = Some(error);
            return;
        }
        let old_role = self.current_role;
        if self.node_families.get(&expression.id) == Some(&Family::Expression) {
            self.current_role = Some(expression.id);
        }
        self.parents.push(Parent {
            node: expression.id,
            span: expression.span,
            paren_child: match &expression.kind {
                ast::ExprKind::Paren(child) => Some(child.id),
                _ => None,
            },
            attributed: !expression.attrs.is_empty(),
        });
        visit::walk_expr(self, expression);
        self.parents.pop();
        self.current_role = old_role;
    }
    fn visit_pat(&mut self, pattern: &'ast ast::Pat) {
        if self.error.is_some() {
            return;
        }
        if let Err(error) = charge(&mut self.remaining)
            .and_then(|_| self.located(pattern.id, Family::Binding, pattern.span))
        {
            self.error = Some(error);
            return;
        }
        visit::walk_pat(self, pattern);
    }
    fn visit_ty(&mut self, ty: &'ast ast::Ty) {
        if self.error.is_some() {
            return;
        }
        if let Err(error) = charge(&mut self.remaining)
            .and_then(|_| self.located(ty.id, Family::FieldType, ty.span))
        {
            self.error = Some(error);
            return;
        }
        visit::walk_ty(self, ty);
    }
}

pub(super) fn check<'tcx>(
    tcx: TyCtxt<'tcx>,
    expected: &Expected,
    functions: &BTreeMap<FunctionId, LocalDefId>,
    adts: &BTreeMap<AdtId, LocalDefId>,
    allocations: Captured,
) -> Result<BTreeSet<(Site, Role)>, String> {
    check::check(tcx, expected, functions, adts, allocations)
}
