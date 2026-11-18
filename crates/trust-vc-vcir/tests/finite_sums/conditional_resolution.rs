//! Owned abstract values require active variant provenance; selectors alone
//! remain total logical observations. No native ownership claim is made here.
use super::*;

fn resolved(value: Expr) -> Expr {
    Expr::new(Ty::Bool, SpanId(0), ExprKind::HasResolved(Box::new(value)))
}

fn control(active: bool, transfer: bool, false_goal: bool) -> VcCrate {
    let input = sum(1, Ty::Param(0));
    let selected = project(read(1, input.clone()), Ty::Param(0));
    let mut krate = source(Expr::bool_lit(true, SpanId(0)), vec![input.clone()], 1);
    let function = &mut krate.fns[0];
    function.mode = Mode::Exec;
    for local in &mut function.locals {
        local.mode = Mode::Exec;
    }
    function
        .requires
        .push(clause(test(read(1, input), u32::from(active))));
    let observed = if transfer {
        function.locals.push(LocalDecl {
            name: "owned_payload".into(),
            ty: Ty::Param(0),
            mode: Mode::Exec,
            prophecy: DeclProphecy::Default,
            mutable: false,
            kind: LocalKind::Let,
            span: SpanId(0),
        });
        read(2, Ty::Param(0))
    } else {
        selected.clone()
    };
    let mut statements = Vec::new();
    if transfer {
        statements.push(Stmt::new(
            SpanId(0),
            StmtKind::Let {
                local: LocalId(2),
                init: Some(selected),
            },
        ));
    }
    statements.push(Stmt::new(
        SpanId(0),
        StmtKind::Assert {
            expr: if false_goal {
                Expr::bool_lit(false, SpanId(0))
            } else {
                resolved(observed)
            },
            site: SiteId(0),
            attrs: ClauseAttrs::default(),
        },
    ));
    statements.push(Stmt::new(
        SpanId(0),
        StmtKind::Return {
            value: None,
            site: SiteId(1),
        },
    ));
    function.body = Body::Stmts(if active && transfer {
        // The transfer is licensed by the actual current branch predicate,
        // rather than by a new assumption or by the selector's type alone.
        Block::new(vec![Stmt::new(
            SpanId(0),
            StmtKind::If {
                cond: test(read(1, sum(1, Ty::Param(0))), 1),
                then_block: Block::new(statements),
                else_block: Block::new(vec![Stmt::new(
                    SpanId(0),
                    StmtKind::Return {
                        value: None,
                        site: SiteId(2),
                    },
                )]),
            },
        )])
    } else {
        Block::new(statements)
    });
    krate
}

fn check(krate: &VcCrate, proved: bool) {
    assert!(check_crate(krate).is_empty(), "{:?}", check_crate(krate));
    let generated = vcgen::generate(krate);
    let Some(FnVcs::Checks(checks)) = generated.get(fid()) else {
        panic!("{generated:?}")
    };
    assert_eq!(checks.len(), 1, "the real source assertion must survive");
    let result = solve::check(
        &checks[0].query,
        "conditional owned abstract value",
        &Limits::default(),
    );
    assert!(
        if proved {
            matches!(result, Verdict::Proved { .. })
        } else {
            matches!(result, Verdict::Refuted { .. })
        },
        "{result:?}"
    );
}

#[test]
fn an_inactive_total_selector_cannot_be_laundered_through_an_owned_local() {
    let krate = control(false, true, false);
    assert!(check_crate(&krate).is_empty());
    let generated = vcgen::generate(&krate);
    let Some(FnVcs::Refused(problem)) = generated.get(fid()) else {
        panic!("an inactive selector acquired owned resolution facts: {generated:?}")
    };
    assert_eq!(problem.tag, "abstract-owned-origin");
}

#[test]
fn guarded_owned_transfer_proves_resolution_without_proving_its_false_twin() {
    check(&control(true, true, false), true);
    check(&control(true, true, true), false);
}

#[test]
fn logical_selector_observations_require_the_actual_parent_guard() {
    check(&control(true, false, false), true);
    check(&control(false, false, false), false);
}

#[test]
fn ordinary_verified_callee_owned_result_keeps_the_existing_call_abi() {
    for false_goal in [false, true] {
        let mut krate = source(Expr::bool_lit(true, SpanId(0)), vec![Ty::Param(0)], 1);
        let function = &mut krate.fns[0];
        function.mode = Mode::Exec;
        for local in &mut function.locals {
            local.mode = Mode::Exec;
        }
        let mut output = function.locals[1].clone();
        output.kind = LocalKind::Let;
        function.locals.push(output);
        let callee_id = FnId(DefHash::new(73, 100));
        function.body = Body::Stmts(Block::new(vec![
            Stmt::new(
                SpanId(0),
                StmtKind::Let {
                    local: LocalId(2),
                    init: None,
                },
            ),
            Stmt::new(
                SpanId(0),
                StmtKind::Call {
                    callee: callee_id,
                    type_args: vec![Ty::Param(0)],
                    args: vec![read(1, Ty::Param(0))],
                    dest: Some(Place::local(LocalId(2))),
                    site: SiteId(2),
                },
            ),
            Stmt::new(
                SpanId(0),
                StmtKind::Assert {
                    expr: if false_goal {
                        Expr::bool_lit(false, SpanId(0))
                    } else {
                        resolved(read(2, Ty::Param(0)))
                    },
                    site: SiteId(0),
                    attrs: ClauseAttrs::default(),
                },
            ),
            Stmt::new(
                SpanId(0),
                StmtKind::Return {
                    value: None,
                    site: SiteId(1),
                },
            ),
        ]));
        let mut callee = function.clone();
        callee.id = callee_id;
        callee.name = "actual_owned_identity".into();
        callee.locals.truncate(2);
        callee.locals[0].ty = Ty::Param(0);
        callee.body = Body::Stmts(Block::new(vec![Stmt::new(
            SpanId(0),
            StmtKind::Return {
                value: Some(read(1, Ty::Param(0))),
                site: SiteId(0),
            },
        )]));
        krate.fns.push(callee);
        check(&krate, !false_goal);
    }
}

#[test]
fn postmove_spec_snapshot_remains_readable_without_creating_new_resolution_facts() {
    let mut krate = source(Expr::bool_lit(true, SpanId(0)), vec![Ty::Param(0)], 1);
    let function = &mut krate.fns[0];
    function.mode = Mode::Exec;
    for local in &mut function.locals {
        local.mode = Mode::Exec;
    }
    function.locals[0].ty = Ty::Param(0);
    let mut moved = function.locals[1].clone();
    moved.kind = LocalKind::Let;
    function.locals.push(moved.clone());
    moved.mode = Mode::Spec;
    function.locals.push(moved);
    function.body = Body::Stmts(Block::new(vec![
        Stmt::new(
            SpanId(0),
            StmtKind::Let {
                local: LocalId(2),
                init: Some(read(1, Ty::Param(0))),
            },
        ),
        Stmt::new(
            SpanId(0),
            StmtKind::Let {
                local: LocalId(3),
                init: Some(read(1, Ty::Param(0))),
            },
        ),
        Stmt::new(
            SpanId(0),
            StmtKind::Assert {
                expr: eq(read(3, Ty::Param(0)), read(1, Ty::Param(0))),
                site: SiteId(0),
                attrs: ClauseAttrs::default(),
            },
        ),
        Stmt::new(
            SpanId(0),
            StmtKind::Assert {
                expr: resolved(read(1, Ty::Param(0))),
                site: SiteId(1),
                attrs: ClauseAttrs::default(),
            },
        ),
        Stmt::new(
            SpanId(0),
            StmtKind::Return {
                value: Some(read(2, Ty::Param(0))),
                site: SiteId(2),
            },
        ),
    ]));
    assert!(check_crate(&krate).is_empty(), "{:?}", check_crate(&krate));
    let generated = vcgen::generate(&krate);
    let Some(FnVcs::Checks(checks)) = generated.get(fid()) else {
        panic!("{generated:?}")
    };
    assert_eq!(checks.len(), 2);
    assert!(matches!(
        solve::check(
            &checks[0].query,
            "postmove logical snapshot",
            &Limits::default()
        ),
        Verdict::Proved { .. }
    ));
    assert!(matches!(
        solve::check(
            &checks[1].query,
            "no fresh postmove resolution",
            &Limits::default()
        ),
        Verdict::Refuted { .. }
    ));
}
