// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Publish typed shadows for plain parameters and nested plain let bindings.
use super::super::rustc_data_structures::steal::Steal;
use super::*;
use rustc_ast::mut_visit::{self, MutVisitor};
use rustc_middle::middle::resolve::{PartialRes, ResolverAstLowering, ResolverGlobalCtxt};

struct Names(HashSet<Symbol>);
impl MutVisitor for Names {
    fn visit_pat(&mut self, pattern: &mut ast::Pat) {
        if let ast::PatKind::Ident(_, ident, _) = pattern.kind {
            self.0.insert(ident.name);
        }
        mut_visit::walk_pat(self, pattern);
    }
}

struct Insert<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    resolver: &'a mut ResolverAstLowering<'tcx>,
    names: HashSet<Symbol>,
    shadows: Vec<Symbol>,
}
impl Insert<'_, '_> {
    fn fresh(&mut self) -> ast::NodeId {
        let id = self.resolver.next_node_id;
        let next = id.as_u32().checked_add(1).expect("AST id overflow");
        assert!(next < ast::DUMMY_NODE_ID.as_u32());
        assert!(
            !self.resolver.partial_res_map.contains_key(&id)
                && !self.resolver.owners.contains_key(&id)
        );
        self.resolver.next_node_id = ast::NodeId::from_u32(next);
        id
    }
    fn seed(&mut self, original: &ast::Pat, attrs: ast::AttrVec) -> ast::Stmt {
        let ast::PatKind::Ident(mode, ident, None) = original.kind else {
            self.tcx
                .dcx()
                .fatal("shadow component requires plain bindings");
        };
        if mode.0 != ast::ByRef::No {
            self.tcx
                .dcx()
                .fatal("shadow component does not allocate by-reference patterns");
        }
        if self
            .resolver
            .partial_res_map
            .get(&original.id)
            .and_then(|resolution| resolution.full_res())
            != Some(Res::Local(original.id))
        {
            self.tcx
                .dcx()
                .fatal("shadow seed source is not an actual resolved local binding");
        }
        let name = Symbol::intern(&format!("__trust_vc_shadow_{}", self.shadows.len()));
        if !self.names.insert(name) {
            self.tcx
                .dcx()
                .fatal("shadow component generated-name collision");
        }
        self.shadows.push(name);
        let statement = self.fresh();
        let local = self.fresh();
        let pattern = self.fresh();
        let expression = self.fresh();
        let segment = self.fresh();
        for (id, binding) in [
            (pattern, pattern),
            (expression, original.id),
            (segment, original.id),
        ] {
            assert!(self
                .resolver
                .partial_res_map
                .insert(id, PartialRes::new(Res::Local(binding)))
                .is_none());
        }
        let span = original.span;
        let init = Box::new(ast::Expr {
            id: expression,
            span,
            attrs: Default::default(),
            tokens: None,
            kind: ast::ExprKind::Path(
                None,
                ast::Path {
                    span,
                    segments: vec![ast::PathSegment {
                        ident,
                        id: segment,
                        args: None,
                    }]
                    .into(),
                },
            ),
        });
        ast::Stmt {
            id: statement,
            span,
            kind: ast::StmtKind::Let(Box::new(ast::Local {
                id: local,
                super_: None,
                pat: Box::new(ast::Pat {
                    id: pattern,
                    span,
                    kind: ast::PatKind::Ident(ast::BindingMode::MUT, Ident::new(name, span), None),
                }),
                ty: None,
                kind: ast::LocalKind::Init(init),
                span,
                colon_sp: None,
                attrs,
                tokens: None,
            })),
        }
    }
}
impl MutVisitor for Insert<'_, '_> {
    fn visit_block(&mut self, block: &mut ast::Block) {
        mut_visit::walk_block(self, block);
        let statements = std::mem::take(&mut block.stmts);
        for statement in statements {
            let seed = match &statement.kind {
                ast::StmtKind::Let(local) => Some(self.seed(&local.pat, local.attrs.clone())),
                ast::StmtKind::Item(_) => self
                    .tcx
                    .dcx()
                    .fatal("shadow component does not add nested owners"),
                _ => None,
            };
            block.stmts.push(statement);
            if let Some(seed) = seed {
                block.stmts.push(seed);
            }
        }
    }
    fn visit_expr(&mut self, expression: &mut ast::Expr) {
        if matches!(
            expression.kind,
            ast::ExprKind::Closure(..) | ast::ExprKind::ConstBlock(..)
        ) {
            self.tcx
                .dcx()
                .fatal("shadow component does not transform captures or anonymous owners");
        }
        mut_visit::walk_expr(self, expression);
    }
}

pub(super) fn expanded<'tcx>(
    tcx: TyCtxt<'tcx>,
    (): (),
) -> (
    &'tcx Steal<ResolverAstLowering<'tcx>>,
    &'tcx Steal<ast::Crate>,
    &'tcx ResolverGlobalCtxt,
) {
    let original = tcx
        .sess
        .with_trust_compiler_state::<hooks::State, _>(|state| state.raw.unwrap());
    let (resolver, krate, global) = original(tcx, ());
    let mut resolver = resolver.steal();
    let mut krate = krate.steal();
    let mut targets = krate
        .items
        .iter_mut()
        .filter_map(|item| match &mut item.kind {
            ast::ItemKind::Fn(function) if function.ident.name.as_str() == "target" => {
                Some((item.id, function.as_mut()))
            }
            _ => None,
        });
    let (id, function) = targets.next().expect("macro-expanded target");
    assert!(targets.next().is_none());
    assert!(function.ident.span.from_expansion());
    let owner = resolver.owners[&id].def_id;
    let mut names = Names(HashSet::new());
    for parameter in &mut function.sig.decl.inputs {
        names.visit_pat(&mut parameter.pat);
    }
    names.visit_block(function.body.as_mut().unwrap());
    let mut insert = Insert {
        tcx,
        resolver: &mut resolver,
        names: names.0,
        shadows: Vec::new(),
    };
    let mut parameters = Vec::new();
    for parameter in &function.sig.decl.inputs {
        parameters.push(insert.seed(&parameter.pat, parameter.attrs.clone()));
    }
    let block = function.body.as_mut().unwrap();
    insert.visit_block(block);
    for seed in parameters.into_iter().rev() {
        block.stmts.insert(0, seed);
    }
    let shadows = insert.shadows;
    tcx.sess
        .with_trust_compiler_state::<hooks::State, _>(|state| {
            assert!(state.owner.replace(owner).is_none() && state.shadow_names.is_empty());
            state.shadow_names = shadows;
            state.expansions += 1;
        });
    (
        tcx.arena.alloc(Steal::new(resolver)),
        tcx.arena.alloc(Steal::new(krate)),
        global,
    )
}
