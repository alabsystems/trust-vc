// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

fn calls(return_mode: Mode, argument_mode: Mode) -> VcCrate {
    let mut producer = function(2, Mode::Exec, Ty::Bool, return_mode);
    producer.body = Body::Stmts(Block::new(vec![returned(Some(Expr::bool_lit(
        true,
        span(),
    )))]));
    let mut consumer = function(3, Mode::Exec, Ty::Unit, Mode::Exec);
    add(&mut consumer, Ty::Bool, argument_mode, LocalKind::Param);
    let mut caller = function(1, Mode::Exec, Ty::Unit, Mode::Exec);
    let result = add(&mut caller, Ty::Bool, Mode::Spec, LocalKind::Temp);
    caller.locals[result.index()].prophecy = DeclProphecy::DelayedInfer;
    caller.body = Body::Stmts(Block::new(vec![
        statement(StmtKind::Let {
            local: result,
            init: None,
        }),
        statement(StmtKind::Call {
            callee: producer.id,
            type_args: vec![],
            args: vec![],
            dest: Some(Place::local(result)),
            site: SiteId(1),
        }),
        statement(StmtKind::Call {
            callee: consumer.id,
            type_args: vec![],
            args: vec![read(result, Ty::Bool)],
            dest: None,
            site: SiteId(2),
        }),
        returned(None),
    ]));
    let mut krate = source(caller);
    krate.fns.extend([producer, consumer]);
    krate
}

#[test]
fn executable_statement_call_results_keep_their_executable_value_mode() {
    clean(&calls(Mode::Exec, Mode::Exec));
}

#[test]
fn spec_statement_call_results_do_not_gain_executable_value_mode() {
    // An executable function with a body may return a written Spec value.
    // Its generated destination can hold it, and a Spec argument can use it.
    clean(&calls(Mode::Spec, Mode::Spec));
    let errors = check_crate(&calls(Mode::Spec, Mode::Exec));
    assert_eq!(
        errors,
        vec![WfError {
            class: WfClass::User,
            function: Some(id(1)),
            span: span(),
            message: "expression has mode spec, expected mode exec".into(),
        }]
    );
}
