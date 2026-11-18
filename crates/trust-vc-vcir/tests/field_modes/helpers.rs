// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

pub(super) fn id(n: u64) -> FnId {
    FnId(DefHash::new(191, n))
}
pub(super) fn adt_id() -> AdtId {
    AdtId(DefHash::new(191, 100))
}
pub(super) fn span() -> SpanId {
    SpanId(8)
}
pub(super) fn scalar() -> Ty {
    Ty::uint(32)
}
pub(super) fn reference() -> Ty {
    Ty::MutRef(Box::new(scalar()))
}
pub(super) fn record_type() -> Ty {
    Ty::Adt(adt_id(), vec![])
}
pub(super) fn integer(value: i128) -> Expr {
    Expr::int_lit(value, scalar(), span())
}
pub(super) fn read(local: LocalId, ty: Ty) -> Expr {
    Expr::read(Place::local(local), ty, span())
}
pub(super) fn statement(kind: StmtKind) -> Stmt {
    Stmt::new(span(), kind)
}
pub(super) fn returned(value: Option<Expr>) -> Stmt {
    statement(StmtKind::Return {
        value,
        site: SiteId(9),
    })
}
pub(super) fn project(base: Expr, field: u32) -> Expr {
    Expr::new(
        scalar(),
        span(),
        ExprKind::Field {
            base: Box::new(base),
            variant: 0,
            field,
        },
    )
}
pub(super) fn equality(a: Expr, b: Expr) -> Expr {
    Expr::binary(BinOp::Eq, a, b, Ty::Bool, span())
}

pub(super) fn function(number: u64, mode: Mode, ty: Ty, result_mode: Mode) -> FnDecl {
    FnDecl {
        id: id(number),
        name: format!("field_context_{number}"),
        span: span(),
        mode,
        role: FnRole::Item,
        kind: FnKind::Function,
        copy_premises: Vec::new(),
        type_params: vec![],
        locals: vec![LocalDecl {
            name: "result".into(),
            ty,
            mode: result_mode,
            prophecy: DeclProphecy::Default,
            kind: LocalKind::Return,
            mutable: false,
            span: span(),
        }],
        params: vec![],
        ret: LocalId(0),
        requires: vec![],
        ensures: vec![],
        recommends: vec![],
        unwind: None,
        decreases: vec![],
        decreases_when: None,
        decreases_by: None,
        attrs: FnAttrs::default(),
        body: Body::Stmts(Block::new(vec![returned(None)])),
    }
}
pub(super) fn add(f: &mut FnDecl, ty: Ty, mode: Mode, kind: LocalKind) -> LocalId {
    let id = LocalId(f.locals.len() as u32);
    f.locals.push(LocalDecl {
        name: format!("local{}", id.0),
        ty,
        mode,
        prophecy: DeclProphecy::Default,
        kind,
        mutable: true,
        span: span(),
    });
    if kind == LocalKind::Param {
        f.params.push(id);
    }
    id
}
pub(super) fn source(f: FnDecl) -> VcCrate {
    let mut krate = VcCrate::new("typed field authority");
    krate.fns.push(f);
    krate
}
pub(super) fn record_decl(mode: Mode) -> AdtDecl {
    AdtDecl {
        id: adt_id(),
        name: "Fields".into(),
        type_params: vec![],
        span: span(),
        kind: AdtKind::Struct,
        variants: vec![VariantDecl {
            name: "Fields".into(),
            fields: vec![
                FieldDecl {
                    name: "selected".into(),
                    ty: scalar(),
                    mode,
                },
                FieldDecl {
                    name: "sibling".into(),
                    ty: scalar(),
                    mode: Mode::Exec,
                },
            ],
        }],
    }
}
pub(super) fn clean(krate: &VcCrate) {
    let errors = check_crate(krate);
    assert!(errors.is_empty(), "{errors:?}");
}
pub(super) fn user_error(krate: &VcCrate, message: &str) {
    let errors = check_crate(krate);
    assert!(
        errors.iter().any(|error| error.class == WfClass::User
            && error.span == span()
            && error.message == message),
        "{errors:?}"
    );
    assert!(
        errors.iter().all(|error| error.class == WfClass::User),
        "{errors:?}"
    );
}
pub(super) fn proof_seven() -> FnDecl {
    let mut target = function(2, Mode::Proof, scalar(), Mode::Proof);
    target.ensures.push(Clause {
        span: span(),
        expr: equality(read(target.ret, scalar()), integer(7)),
        attrs: ClauseAttrs::default(),
    });
    target.body = Body::Stmts(Block::new(vec![returned(Some(integer(7)))]));
    target
}
