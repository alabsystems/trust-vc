// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

pub(super) fn span() -> SpanId {
    SpanId(0)
}
pub(super) fn scalar() -> Ty {
    Ty::uint(32)
}
pub(super) fn function(number: u64, result: Ty) -> FnDecl {
    FnDecl {
        id: FnId(DefHash::new(149, number)),
        name: format!("classification_{number}"),
        span: span(),
        mode: Mode::Exec,
        role: FnRole::Item,
        kind: FnKind::Function,
        copy_premises: Vec::new(),
        type_params: vec![],
        locals: vec![LocalDecl {
            name: "result".into(),
            ty: result,
            mode: Mode::Exec,
            kind: LocalKind::Return,
            prophecy: DeclProphecy::Default,
            mutable: false,
            span: span(),
        }],
        params: vec![],
        ret: LocalId(0),
        requires: vec![],
        ensures: vec![],
        recommends: vec![],
        decreases: vec![],
        decreases_when: None,
        decreases_by: None,
        unwind: None,
        attrs: FnAttrs::default(),
        body: Body::Stmts(Block::default()),
    }
}
pub(super) fn add(f: &mut FnDecl, ty: Ty, mode: Mode, kind: LocalKind) -> LocalId {
    let id = LocalId(f.locals.len() as u32);
    f.locals.push(LocalDecl {
        name: format!("local{}", id.0),
        ty,
        mode,
        kind,
        prophecy: DeclProphecy::Default,
        mutable: kind == LocalKind::Let,
        span: span(),
    });
    if kind == LocalKind::Param {
        f.params.push(id);
    }
    id
}
pub(super) fn stmt(kind: StmtKind) -> Stmt {
    Stmt::new(span(), kind)
}
pub(super) fn read(local: LocalId, ty: Ty) -> Expr {
    Expr::read(Place::local(local), ty, span())
}
pub(super) fn ret(value: Option<Expr>) -> Stmt {
    stmt(StmtKind::Return {
        value,
        site: SiteId(9),
    })
}
#[cfg(feature = "solve")]
pub(super) fn source(f: FnDecl, adts: Vec<AdtDecl>) -> VcCrate {
    let mut source = VcCrate::new("ownership classifier semantics");
    source.fns.push(f);
    source.adts = adts;
    source
}
pub(super) fn generate(source: &VcCrate) -> vcgen::CrateVcs {
    let errors = check_crate(source);
    assert!(errors.is_empty(), "{errors:?}");
    let generated = vcgen::generate(source);
    assert_eq!(generated.fns.len(), source.fns.len());
    for function in &source.fns {
        assert_eq!(function.role, FnRole::Item);
        assert!(!function.attrs.external_body && function.attrs.instance.is_none());
    }
    generated
}
