// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Public IR contracts must be pure Boolean predicates over entry state.

use super::*;

fn condition_span() -> SpanId {
    SpanId(77)
}

fn read(local: LocalId, ty: Ty) -> Expr {
    Expr::read(Place::local(local), ty, condition_span())
}

fn allowed_parameter() -> Expr {
    read(LocalId(1), Ty::Bool)
}

fn source(function: FnDecl) -> VcCrate {
    let mut source = VcCrate::new("unwind condition validation");
    source.fns.push(function);
    source
}

fn clean(source: &VcCrate) {
    assert!(check_crate(source).is_empty(), "{:?}", check_crate(source));
}

fn rejects(source: &VcCrate, class: WfClass, at: SpanId, message: &str) {
    let message = if class == WfClass::Malformed {
        format!("in `function1`: {message}")
    } else {
        message.into()
    };
    assert_eq!(
        check_crate(source),
        vec![WfError {
            class,
            function: Some(id(1)),
            span: at,
            message
        }]
    );
}

#[test]
fn an_unwind_condition_must_have_boolean_type() {
    let mut declaration = function(1);
    declaration
        .locals
        .push(local(Ty::uint(32), LocalKind::Param));
    declaration.params.push(LocalId(2));
    declaration.unwind = Some(UnwindSpec::NoUnwindWhen(allowed_parameter()));
    let mut source = source(declaration);
    clean(&source);
    source.fns[0].unwind = Some(UnwindSpec::NoUnwindWhen(read(LocalId(2), Ty::uint(32))));
    rejects(
        &source,
        WfClass::Malformed,
        condition_span(),
        "condition is not a bool",
    );
}

#[test]
fn an_unwind_condition_cannot_read_the_return_local() {
    let mut declaration = function(1);
    declaration.locals[0].ty = Ty::Bool;
    declaration.body = Body::Stmts(Block::new(vec![statement(StmtKind::Return {
        value: Some(parameter()),
        site: SiteId(9),
    })]));
    declaration.unwind = Some(UnwindSpec::NoUnwindWhen(allowed_parameter()));
    let mut source = source(declaration);
    clean(&source);
    source.fns[0].unwind = Some(UnwindSpec::NoUnwindWhen(read(LocalId(0), Ty::Bool)));
    rejects(
        &source,
        WfClass::Malformed,
        condition_span(),
        "an unwind condition reads a local outside its entry-state parameters and binders",
    );
}

#[test]
fn a_body_temporary_is_not_an_entry_state_parameter() {
    let mut declaration = function(1);
    declaration.locals.push(local(Ty::Bool, LocalKind::Temp));
    declaration.body = Body::Stmts(Block::new(vec![
        statement(StmtKind::Let {
            local: LocalId(2),
            init: Some(parameter()),
        }),
        statement(StmtKind::Return {
            value: None,
            site: SiteId(9),
        }),
    ]));
    declaration.unwind = Some(UnwindSpec::NoUnwindWhen(allowed_parameter()));
    let mut source = source(declaration);
    clean(&source);
    source.fns[0].unwind = Some(UnwindSpec::NoUnwindWhen(read(LocalId(2), Ty::Bool)));
    rejects(
        &source,
        WfClass::Malformed,
        condition_span(),
        "an unwind condition reads a local outside its entry-state parameters and binders",
    );
}

#[test]
fn an_unwind_condition_cannot_call_an_exec_function() {
    let mut caller = function(1);
    caller.unwind = Some(UnwindSpec::NoUnwindWhen(allowed_parameter()));
    let mut callee = function(2);
    callee.locals[0].ty = Ty::Bool;
    callee.body = Body::Stmts(Block::new(vec![statement(StmtKind::Return {
        value: Some(parameter()),
        site: SiteId(9),
    })]));
    let mut source = source(caller);
    source.fns.push(callee);
    clean(&source);
    source.fns[0].unwind = Some(UnwindSpec::NoUnwindWhen(Expr::new(
        Ty::Bool,
        condition_span(),
        ExprKind::Call {
            callee: id(2),
            type_args: vec![],
            args: vec![parameter()],
        },
    )));
    rejects(
        &source,
        WfClass::Malformed,
        condition_span(),
        "`function2` is called in an expression but is not a spec function",
    );
}

#[test]
fn explicit_unwind_contracts_are_exec_only_while_ghost_defaults_remain_valid() {
    for mode in [Mode::Proof, Mode::Spec] {
        let mut declaration = function(1);
        declaration.mode = mode;
        for local in &mut declaration.locals {
            local.mode = mode;
            local.mutable = false;
        }
        if mode == Mode::Spec {
            declaration.body = Body::Spec(Expr::new(Ty::Unit, span(), ExprKind::Lit(Lit::Unit)));
        }
        let mut source = source(declaration);
        clean(&source);
        for contract in [
            UnwindSpec::NoUnwind,
            UnwindSpec::NoUnwindWhen(allowed_parameter()),
            UnwindSpec::MayUnwind,
        ] {
            source.fns[0].unwind = Some(contract);
            rejects(
                &source,
                WfClass::User,
                span(),
                "an 'unwind' specification can only be given on exec functions",
            );
        }
    }
}

#[test]
fn unwind_let_binders_restore_shadowed_scope_without_leaking_outside() {
    let bound = LocalId(2);
    let bound_read = || read(bound, Ty::Bool);
    let inner = Expr::new(
        Ty::Bool,
        condition_span(),
        ExprKind::Let {
            local: bound,
            value: Box::new(not(bound_read())),
            body: Box::new(bound_read()),
        },
    );
    let condition = Expr::new(
        Ty::Bool,
        condition_span(),
        ExprKind::Let {
            local: bound,
            value: Box::new(allowed_parameter()),
            body: Box::new(Expr::binary(
                BinOp::And,
                inner,
                bound_read(),
                Ty::Bool,
                condition_span(),
            )),
        },
    );
    let mut declaration = function(1);
    let mut binder = local(Ty::Bool, LocalKind::Bound);
    binder.mode = Mode::Spec;
    declaration.locals.push(binder);
    declaration.unwind = Some(UnwindSpec::NoUnwindWhen(condition.clone()));
    let mut source = source(declaration);
    clean(&source);

    let outside = SpanId(78);
    source.fns[0].unwind = Some(UnwindSpec::NoUnwindWhen(Expr::binary(
        BinOp::And,
        condition,
        Expr::read(Place::local(bound), Ty::Bool, outside),
        Ty::Bool,
        condition_span(),
    )));
    rejects(
        &source,
        WfClass::Malformed,
        outside,
        "an unwind condition reads a local outside its entry-state parameters and binders",
    );
}
