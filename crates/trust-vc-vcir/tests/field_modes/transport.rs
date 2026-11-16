// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Generated scalar results retain producer modes, not Spec storage modes.
use super::*;

#[path = "transport_boundaries.rs"]
mod boundaries;

const RESULT: LocalId = LocalId(1);
fn boolean(value: bool) -> Expr {
    Expr::bool_lit(value, span())
}
fn assign(value: Expr) -> Stmt {
    statement(StmtKind::Assign {
        place: Place::local(RESULT),
        value,
    })
}
fn branch(cond: Expr, yes: Vec<Stmt>, no: Vec<Stmt>) -> Stmt {
    statement(StmtKind::If {
        cond,
        then_block: Block::new(yes),
        else_block: Block::new(no),
    })
}
fn call_result(callee: FnId) -> Stmt {
    statement(StmtKind::Call {
        callee,
        type_args: vec![],
        args: vec![],
        dest: Some(Place::local(RESULT)),
        site: SiteId(2),
    })
}
fn expression_call(callee: FnId) -> Expr {
    Expr::new(
        Ty::Bool,
        span(),
        ExprKind::Call {
            callee,
            type_args: vec![],
            args: vec![],
        },
    )
}
fn producer(mode: Mode, result: Mode, prophetic: bool) -> FnDecl {
    let mut f = function(3, mode, Ty::Bool, result);
    f.attrs.prophetic = prophetic;
    f.body = if mode == Mode::Spec {
        Body::Spec(boolean(false))
    } else {
        Body::Stmts(Block::new(vec![returned(Some(boolean(false)))]))
    };
    f
}
fn fixture(ty: Ty, steps: Vec<Stmt>, formal_mode: Mode) -> VcCrate {
    let mut target = function(2, Mode::Proof, Ty::Unit, Mode::Proof);
    add(&mut target, ty.clone(), formal_mode, LocalKind::Param);
    let mut caller = function(1, Mode::Proof, Ty::Unit, Mode::Proof);
    assert_eq!(
        add(&mut caller, ty.clone(), Mode::Spec, LocalKind::Temp),
        RESULT
    );
    caller.locals[RESULT.index()].prophecy = DeclProphecy::DelayedInfer;
    let mut body = vec![statement(StmtKind::Let {
        local: RESULT,
        init: None,
    })];
    body.extend(steps);
    body.push(statement(StmtKind::Call {
        callee: target.id,
        type_args: vec![],
        args: vec![read(RESULT, ty)],
        dest: None,
        site: SiteId(1),
    }));
    body.push(returned(None));
    caller.body = Body::Stmts(Block::new(body));
    let mut krate = source(caller);
    krate.fns.push(target);
    krate
}
fn mode_error(krate: &VcCrate) {
    user_error(krate, "expression has mode spec, expected mode proof");
}

#[test]
fn generated_bool_results_join_both_actual_arm_modes() {
    clean(&fixture(
        Ty::Bool,
        vec![branch(
            boolean(false),
            vec![assign(boolean(false))],
            vec![assign(boolean(true))],
        )],
        Mode::Proof,
    ));
}

#[test]
fn generated_integer_and_scalar_tuple_results_retain_producer_modes() {
    for value in [
        integer(7),
        Expr::new(
            Ty::Tuple(vec![Ty::Bool, scalar()]),
            span(),
            ExprKind::Tuple(vec![boolean(false), integer(7)]),
        ),
    ] {
        let ty = value.ty.clone();
        clean(&fixture(
            ty,
            vec![branch(
                boolean(false),
                vec![assign(value.clone())],
                vec![assign(value)],
            )],
            Mode::Proof,
        ));
    }
}

#[test]
fn guard_prophecy_remains_separate_from_returned_mode() {
    let mut krate = fixture(
        Ty::Bool,
        vec![branch(
            expression_call(id(3)),
            vec![assign(boolean(false))],
            vec![assign(boolean(true))],
        )],
        Mode::Proof,
    );
    krate.fns.push(producer(Mode::Spec, Mode::Spec, true));
    let errors = check_crate(&krate);
    assert!(
        errors.iter().any(|error| error.function == Some(id(1))
            && error
                .message
                .contains("argument to proof-mode function with tracked parameters")),
        "{errors:?}"
    );
    assert!(
        !errors
            .iter()
            .any(|error| error.message == "expression has mode spec, expected mode proof"),
        "{errors:?}"
    );
}

#[test]
fn a_spec_arm_remains_spec_even_when_it_is_nonprophetic() {
    let mut krate = fixture(
        Ty::Bool,
        vec![branch(
            boolean(false),
            vec![assign(expression_call(id(3)))],
            vec![assign(boolean(true))],
        )],
        Mode::Spec,
    );
    krate.fns.push(producer(Mode::Spec, Mode::Spec, false));
    clean(&krate);
    krate.fns[1].locals[1].mode = Mode::Proof;
    mode_error(&krate);
}

#[test]
fn copied_authored_spec_storage_is_not_an_anf_mode_waiver() {
    for kind in [LocalKind::Let, LocalKind::Temp] {
        let original = LocalId(2);
        let mut krate = fixture(
            Ty::Bool,
            vec![
                statement(StmtKind::Let {
                    local: original,
                    init: Some(boolean(false)),
                }),
                assign(read(original, Ty::Bool)),
            ],
            Mode::Proof,
        );
        assert_eq!(add(&mut krate.fns[0], Ty::Bool, Mode::Spec, kind), original);
        mode_error(&krate);
    }
}

#[test]
fn an_unmarked_spec_temp_does_not_become_a_generated_result() {
    let mut krate = fixture(Ty::Bool, vec![assign(boolean(false))], Mode::Proof);
    krate.fns[0].locals[RESULT.index()].prophecy = DeclProphecy::Default;
    mode_error(&krate);
}

#[test]
fn a_missing_arm_initializer_does_not_grant_a_producer_mode() {
    mode_error(&fixture(
        Ty::Bool,
        vec![branch(boolean(true), vec![assign(boolean(false))], vec![])],
        Mode::Proof,
    ));
}

#[test]
fn duplicate_declarations_and_sequential_producers_are_not_transport() {
    for steps in [
        vec![
            statement(StmtKind::Let {
                local: RESULT,
                init: None,
            }),
            assign(boolean(false)),
        ],
        vec![assign(boolean(false)), assign(boolean(true))],
    ] {
        mode_error(&fixture(Ty::Bool, steps, Mode::Proof));
    }
}

#[test]
fn a_scoped_producer_cannot_escape_its_declaration() {
    let mut krate = fixture(Ty::Bool, vec![], Mode::Proof);
    let Body::Stmts(block) = &mut krate.fns[0].body else {
        panic!("statement body");
    };
    let declaration = block.stmts.remove(0);
    block.stmts.insert(
        0,
        statement(StmtKind::Block(Block::new(vec![
            declaration,
            assign(boolean(false)),
        ]))),
    );
    mode_error(&krate);
}

#[test]
fn call_results_use_the_actual_return_mode() {
    for returned in [Mode::Proof, Mode::Spec] {
        let mut krate = fixture(
            Ty::Bool,
            vec![branch(
                boolean(false),
                vec![assign(boolean(false))],
                vec![call_result(id(3))],
            )],
            Mode::Proof,
        );
        krate.fns.push(producer(Mode::Proof, returned, false));
        if returned == Mode::Proof {
            clean(&krate);
        } else {
            mode_error(&krate);
        }
    }
}
