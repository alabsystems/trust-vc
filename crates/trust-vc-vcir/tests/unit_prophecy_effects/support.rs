//! Shared VcIR builders and oracles for the Unit prophecy regressions.

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_vcir::vcgen::{self, FnVcs};
use trust_vc_vcir::*;

pub(super) fn at() -> SpanId {
    SpanId(0)
}

pub(super) fn id(n: u64) -> FnId {
    FnId(DefHash::new(93, n))
}

pub(super) fn unit() -> Expr {
    Expr::new(Ty::Unit, at(), ExprKind::Lit(Lit::Unit))
}

pub(super) fn boolean(value: bool) -> Expr {
    Expr::bool_lit(value, at())
}

pub(super) fn local(ty: Ty, mode: Mode, kind: LocalKind, prophecy: DeclProphecy) -> LocalDecl {
    LocalDecl {
        name: "value".into(),
        ty,
        mode,
        prophecy,
        mutable: matches!(kind, LocalKind::Let | LocalKind::Temp),
        kind,
        span: at(),
    }
}

pub(super) fn function(n: u64, mode: Mode, result: Ty) -> FnDecl {
    FnDecl {
        id: id(n),
        name: format!("f{n}"),
        span: at(),
        mode,
        role: FnRole::Item,
        kind: FnKind::Function,
        copy_premises: Vec::new(),
        type_params: vec![],
        locals: vec![local(
            result,
            if mode == Mode::Exec {
                Mode::Exec
            } else {
                Mode::Spec
            },
            LocalKind::Return,
            DeclProphecy::Default,
        )],
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
        body: if mode == Mode::Spec {
            Body::None
        } else {
            Body::Stmts(Block::default())
        },
    }
}

pub(super) fn add(
    decl: &mut FnDecl,
    ty: Ty,
    mode: Mode,
    kind: LocalKind,
    prophecy: DeclProphecy,
) -> LocalId {
    let result = LocalId(decl.locals.len() as u32);
    decl.locals.push(local(ty, mode, kind, prophecy));
    if kind == LocalKind::Param {
        decl.params.push(result);
    }
    result
}

pub(super) fn read(local: LocalId, ty: Ty) -> Expr {
    Expr::read(Place::local(local), ty, at())
}

pub(super) fn call(n: u64, ty: Ty, args: Vec<Expr>) -> Expr {
    Expr::new(
        ty,
        at(),
        ExprKind::Call {
            callee: id(n),
            type_args: vec![],
            args,
        },
    )
}

pub(super) fn equal(lhs: Expr, rhs: Expr) -> Expr {
    Expr::binary(BinOp::Eq, lhs, rhs, Ty::Bool, at())
}

pub(super) fn stmt(kind: StmtKind) -> Stmt {
    Stmt::new(at(), kind)
}

pub(super) fn declare(local: LocalId, init: Option<Expr>) -> Stmt {
    stmt(StmtKind::Let { local, init })
}

pub(super) fn assign(local: LocalId, value: Expr) -> Stmt {
    stmt(StmtKind::Assign {
        place: Place::local(local),
        value,
    })
}

pub(super) fn invoke(n: u64, args: Vec<Expr>, dest: Option<LocalId>) -> Stmt {
    stmt(StmtKind::Call {
        callee: id(n),
        type_args: vec![],
        args,
        dest: dest.map(Place::local),
        site: SiteId(1),
    })
}

pub(super) fn conditional(cond: Expr, yes: Vec<Stmt>, no: Vec<Stmt>) -> Stmt {
    stmt(StmtKind::If {
        cond,
        then_block: Block::new(yes),
        else_block: Block::new(no),
    })
}

pub(super) fn proof_tail(block: Vec<Stmt>, tail: Expr) -> Expr {
    Expr::new(
        Ty::Unit,
        at(),
        ExprKind::ProofInSpecTail {
            block: Block::new(block),
            tail: Box::new(tail),
        },
    )
}

pub(super) fn with_proof_body(n: u64, result: Ty) -> FnDecl {
    let mut result = function(n, Mode::Spec, result);
    result.decreases.push(Expr::int_lit(0, Ty::int(), at()));
    result
}

pub(super) fn source(functions: Vec<FnDecl>) -> VcCrate {
    let mut bool_prophecy = function(1, Mode::Spec, Ty::Bool);
    bool_prophecy.attrs.prophetic = true;
    bool_prophecy.body = Body::Spec(boolean(true));
    let mut unit_prophecy = function(2, Mode::Spec, Ty::Unit);
    unit_prophecy.attrs.prophetic = true;
    unit_prophecy.body = Body::Spec(unit());
    let mut lemma = function(3, Mode::Proof, Ty::Unit);
    add(
        &mut lemma,
        Ty::Bool,
        Mode::Spec,
        LocalKind::Param,
        DeclProphecy::Default,
    );
    let mut tracked_sink = function(4, Mode::Proof, Ty::Unit);
    add(
        &mut tracked_sink,
        Ty::Bool,
        Mode::Proof,
        LocalKind::Param,
        DeclProphecy::Default,
    );
    let mut krate = VcCrate::new("unit prophecy consumers");
    krate.fns = vec![bool_prophecy, unit_prophecy, lemma, tracked_sink];
    krate.fns.extend(functions);
    krate
}

pub(super) fn accepted(krate: &VcCrate) {
    let errors = check_crate(krate);
    assert!(errors.is_empty(), "{errors:?}");
    assert!(check_crate_for_diagnostics(krate).errors.is_empty());
}

pub(super) fn rejected(krate: &VcCrate, owner: u64, message: &str) {
    let errors = check_crate(krate);
    assert!(
        errors.iter().all(|error| error.class == WfClass::User),
        "{errors:?}"
    );
    assert!(
        errors
            .iter()
            .any(|error| error.function == Some(id(owner)) && error.message.contains(message)),
        "{errors:?}"
    );
    assert_eq!(check_crate_for_diagnostics(krate).errors, errors);
    let generated = vcgen::generate(krate);
    assert!(matches!(generated.get(id(owner)), Some(FnVcs::Refused(_))));
}
