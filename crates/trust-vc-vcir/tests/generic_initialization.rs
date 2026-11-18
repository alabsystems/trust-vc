//! Declared abstract storage gains a value only from an actual initialization.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_vcir::vcgen::{self, FnVcs};
use trust_vc_vcir::*;

fn id(value: u64) -> FnId {
    FnId(DefHash::new(23, value))
}
fn stmt(kind: StmtKind) -> Stmt {
    Stmt::new(SpanId(0), kind)
}
fn read(local: u32, ty: Ty) -> Expr {
    Expr::read(Place::local(LocalId(local)), ty, SpanId(0))
}
fn local(name: &str, ty: Ty, kind: LocalKind) -> LocalDecl {
    LocalDecl {
        name: name.into(),
        ty,
        mode: Mode::Spec,
        prophecy: trust_vc_vcir::DeclProphecy::Default,
        mutable: matches!(kind, LocalKind::Let | LocalKind::Temp),
        kind,
        span: SpanId(0),
    }
}
fn function(number: u64, parameters: Vec<Ty>, result: Ty) -> FnDecl {
    let mut locals = vec![local("result", result, LocalKind::Return)];
    locals.extend(
        parameters
            .iter()
            .enumerate()
            .map(|(n, ty)| local(&format!("p{n}"), ty.clone(), LocalKind::Param)),
    );
    FnDecl {
        id: id(number),
        name: format!("f{number}"),
        span: SpanId(0),
        mode: Mode::Proof,
        role: FnRole::Item,
        kind: FnKind::Function,
        copy_premises: Vec::new(),
        type_params: vec!["A".into()],
        locals,
        params: (1..=parameters.len()).map(|n| LocalId(n as u32)).collect(),
        ret: LocalId(0),
        requires: vec![],
        ensures: vec![],
        recommends: vec![],
        decreases: vec![],
        decreases_when: None,
        decreases_by: None,
        unwind: None,
        attrs: FnAttrs::default(),
        body: Body::None,
    }
}
fn caller(ty: Ty) -> FnDecl {
    let mut caller = function(2, vec![Ty::Param(0), Ty::Bool], Ty::Unit);
    caller.locals.push(local("stored", ty, LocalKind::Temp));
    caller
}
fn exec_caller(ty: Ty) -> FnDecl {
    let mut caller = caller(ty);
    caller.mode = Mode::Exec;
    for local in &mut caller.locals {
        local.mode = Mode::Exec;
    }
    caller
}
fn declare() -> Stmt {
    stmt(StmtKind::Let {
        local: LocalId(3),
        init: None,
    })
}
fn assign() -> Stmt {
    stmt(StmtKind::Assign {
        place: Place::local(LocalId(3)),
        value: read(1, Ty::Param(0)),
    })
}
fn assertion(value: Expr) -> Stmt {
    stmt(StmtKind::Assert {
        expr: Expr::binary(BinOp::Eq, value.clone(), value, Ty::Bool, SpanId(0)),
        site: SiteId(0),
        attrs: ClauseAttrs::default(),
    })
}
fn exit() -> Stmt {
    stmt(StmtKind::Return {
        value: None,
        site: SiteId(1),
    })
}
fn crate_with(mut caller: FnDecl, statements: Vec<Stmt>) -> VcCrate {
    caller.body = Body::Stmts(Block::new(statements));
    let mut krate = VcCrate::new("abstract initialization paths");
    krate.fns.push(caller);
    krate
}
fn status(krate: &VcCrate) -> FnVcs {
    assert!(check_crate(krate).is_empty(), "{:?}", check_crate(krate));
    vcgen::generate(krate)
        .fns
        .into_iter()
        .find(|(function, _)| *function == id(2))
        .unwrap()
        .1
}
fn checked(krate: &VcCrate) {
    let FnVcs::Checks(checks) = status(krate) else {
        panic!("a definitely initialized value was refused");
    };
    assert_eq!(
        checks.len(),
        1,
        "the actual post-initialization assertion must survive"
    );
}
fn refused(krate: &VcCrate) {
    assert!(matches!(status(krate), FnVcs::Refused(_)));
}
fn no_value(krate: &VcCrate) {
    let FnVcs::Refused(problem) = status(krate) else {
        panic!("abstract storage supplied a value");
    };
    assert!(problem.detail.contains("no value"), "{problem:?}");
}

#[test]
fn a_real_generic_call_initializes_a_declared_destination() {
    let caller = caller(Ty::Param(0));
    let mut krate = crate_with(
        caller,
        vec![
            declare(),
            stmt(StmtKind::Call {
                callee: id(1),
                type_args: vec![Ty::Param(0)],
                args: vec![read(1, Ty::Param(0))],
                dest: Some(Place::local(LocalId(3))),
                site: SiteId(2),
            }),
            assertion(read(3, Ty::Param(0))),
            exit(),
        ],
    );
    let mut pass = function(1, vec![Ty::Param(0)], Ty::Param(0));
    pass.body = Body::Stmts(Block::new(vec![stmt(StmtKind::Return {
        value: Some(read(1, Ty::Param(0))),
        site: SiteId(0),
    })]));
    krate.fns.push(pass);
    checked(&krate);
}

#[test]
fn declared_storage_requires_initialization_on_every_live_branch() {
    for both in [false, true] {
        let branch = stmt(StmtKind::If {
            cond: read(2, Ty::Bool),
            then_block: Block::new(vec![assign()]),
            else_block: Block::new(if both { vec![assign()] } else { vec![] }),
        });
        let krate = crate_with(
            caller(Ty::Param(0)),
            vec![declare(), branch, assertion(read(3, Ty::Param(0))), exit()],
        );
        if both {
            checked(&krate);
        } else {
            no_value(&krate);
            let mut initialized_later = krate.clone();
            let Body::Stmts(body) = &mut initialized_later.fns[0].body else {
                unreachable!()
            };
            body.stmts.insert(2, assign());
            checked(&initialized_later);
        }
    }
}

#[test]
fn different_initialized_values_are_joined_after_both_branches() {
    let mut caller = function(2, vec![Ty::Param(0), Ty::Param(0), Ty::Bool], Ty::Unit);
    caller
        .locals
        .push(local("stored", Ty::Param(0), LocalKind::Temp));
    let branch_value = |source| {
        Block::new(vec![stmt(StmtKind::Assign {
            place: Place::local(LocalId(4)),
            value: read(source, Ty::Param(0)),
        })])
    };
    let krate = crate_with(
        caller,
        vec![
            stmt(StmtKind::Let {
                local: LocalId(4),
                init: None,
            }),
            stmt(StmtKind::If {
                cond: read(3, Ty::Bool),
                then_block: branch_value(1),
                else_block: branch_value(2),
            }),
            assertion(read(4, Ty::Param(0))),
            exit(),
        ],
    );
    checked(&krate);
}

#[test]
fn a_live_initializing_branch_does_not_require_a_value_on_a_returned_branch() {
    let branch = stmt(StmtKind::If {
        cond: read(2, Ty::Bool),
        then_block: Block::new(vec![assign()]),
        else_block: Block::new(vec![stmt(StmtKind::Return {
            value: None,
            site: SiteId(7),
        })]),
    });
    checked(&crate_with(
        caller(Ty::Param(0)),
        vec![declare(), branch, assertion(read(3, Ty::Param(0))), exit()],
    ));
}

#[test]
fn a_declaration_does_not_authorize_reads_or_projection_updates() {
    no_value(&crate_with(
        caller(Ty::Param(0)),
        vec![declare(), assertion(read(3, Ty::Param(0))), exit()],
    ));
    let product = Ty::Tuple(vec![Ty::Param(0), Ty::Bool]);
    let field = Expr::read(
        Place {
            local: LocalId(3),
            projections: vec![Projection::TupleField(0)],
        },
        Ty::Param(0),
        SpanId(0),
    );
    no_value(&crate_with(
        caller(product.clone()),
        vec![declare(), assertion(field), exit()],
    ));
    no_value(&crate_with(
        caller(product),
        vec![
            declare(),
            stmt(StmtKind::Assign {
                place: Place {
                    local: LocalId(3),
                    projections: vec![Projection::TupleField(0)],
                },
                value: read(1, Ty::Param(0)),
            }),
            exit(),
        ],
    ));
}

#[test]
fn represented_uninitialized_storage_keeps_its_existing_arbitrary_value() {
    checked(&crate_with(
        caller(Ty::Bool),
        vec![declare(), assertion(read(3, Ty::Bool)), exit()],
    ));
}

#[test]
fn whole_assignment_requires_a_declaration_and_the_exact_type() {
    refused(&crate_with(caller(Ty::Param(0)), vec![assign(), exit()]));
    let mut wrong = caller(Ty::Param(1));
    wrong.type_params.push("B".into());
    let krate = crate_with(wrong, vec![declare(), assign(), exit()]);
    assert!(
        !check_crate(&krate).is_empty(),
        "a mismatched typed destination must never reach generation"
    );
}

fn lp(body: Vec<Stmt>, isolation: bool, condition: Option<Expr>) -> Stmt {
    stmt(StmtKind::Loop(Box::new(Loop {
        id: LoopId(0),
        isolation,
        allow_complex_invariants: false,
        cond: condition.map(|expr| LoopCond {
            block: Block::default(),
            expr,
        }),
        invariants: vec![],
        decreases: vec![],
        body: Block::new(body),
        sites: LoopSites {
            entry: SiteId(3),
            end: SiteId(4),
            exit: SiteId(5),
        },
    })))
}
fn leave(site: u32) -> Stmt {
    stmt(StmtKind::Break {
        target: LoopId(0),
        site: SiteId(site),
    })
}

#[test]
fn nonisolated_breaks_initialize_only_when_every_exit_has_a_value() {
    for both in [false, true] {
        let branch = stmt(StmtKind::If {
            cond: read(2, Ty::Bool),
            then_block: Block::new(vec![assign(), leave(6)]),
            else_block: Block::new(if both {
                vec![assign(), leave(7)]
            } else {
                vec![leave(7)]
            }),
        });
        let krate = crate_with(
            exec_caller(Ty::Param(0)),
            vec![
                declare(),
                lp(vec![branch], false, None),
                assertion(read(3, Ty::Param(0))),
                exit(),
            ],
        );
        if both {
            checked(&krate);
        } else {
            no_value(&krate);
        }
    }
}

#[test]
fn a_loop_write_set_does_not_initialize_absent_storage() {
    for isolation in [false, true] {
        no_value(&crate_with(
            exec_caller(Ty::Param(0)),
            vec![
                declare(),
                lp(
                    vec![assign()],
                    isolation,
                    Some(Expr::bool_lit(false, SpanId(0))),
                ),
                assertion(read(3, Ty::Param(0))),
                exit(),
            ],
        ));
    }
}

#[test]
fn isolation_does_not_freshen_an_abstract_declaration_into_a_value() {
    no_value(&crate_with(
        exec_caller(Ty::Param(0)),
        vec![
            declare(),
            lp(
                vec![assertion(read(3, Ty::Param(0))), assign()],
                true,
                Some(read(2, Ty::Bool)),
            ),
            exit(),
        ],
    ));
}

#[test]
fn whole_initialization_does_not_change_the_parameter_entry_snapshot() {
    let mut caller = function(2, vec![Ty::Param(0), Ty::Param(0)], Ty::Unit);
    caller.locals[1].mutable = true;
    caller
        .locals
        .push(local("stored", Ty::Param(0), LocalKind::Temp));
    let old_parameter = Expr::new(
        Ty::Param(0),
        SpanId(0),
        ExprKind::Old(Place::local(LocalId(1))),
    );
    let goal = Expr::binary(
        BinOp::Eq,
        read(3, Ty::Param(0)),
        old_parameter,
        Ty::Bool,
        SpanId(0),
    );
    let krate = crate_with(
        caller,
        vec![
            declare(),
            assign(),
            stmt(StmtKind::Assign {
                place: Place::local(LocalId(1)),
                value: read(2, Ty::Param(0)),
            }),
            stmt(StmtKind::Assert {
                expr: goal,
                site: SiteId(0),
                attrs: ClauseAttrs::default(),
            }),
            exit(),
        ],
    );
    checked(&krate);
}

#[test]
fn a_declared_local_is_not_a_parameter_entry_snapshot() {
    let old_storage = Expr::new(
        Ty::Param(0),
        SpanId(0),
        ExprKind::Old(Place::local(LocalId(3))),
    );
    let krate = crate_with(
        caller(Ty::Param(0)),
        vec![declare(), assertion(old_storage), exit()],
    );
    let problems = check_crate(&krate);
    assert!(
        problems.iter().any(|problem| problem
            .message
            .contains("old() of something other than a parameter")),
        "{problems:?}"
    );
}
