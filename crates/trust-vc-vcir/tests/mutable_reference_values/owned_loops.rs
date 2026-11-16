// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Final solver oracles for owned-reference state at isolated loop boundaries.
//! The pinned upstream controls are mut_refs_loops.rs loop1/2, loop8,
//! and nested2/3. An unsupported loop is a failure, never a verdict.

use super::*;
use trust_vc_vcir::solve::{check_detailed, Limits, Verdict};
use trust_vc_vcir::vcgen::term::Term;
use trust_vc_vcir::vcgen::{CheckKind, QueryGroup};

#[derive(Clone, Copy, Debug)]
enum Scenario {
    Stable,
    LaterWrite,
    LoopLocal,
    PartialInitialization,
    BreakOuter,
    BreakInner,
}

fn choice_id() -> FnId {
    FnId(DefHash::new(133, 2))
}

fn resolved(loan: LocalId) -> Expr {
    Expr::new(
        Ty::Bool,
        span(),
        ExprKind::HasResolved(Box::new(read(loan, reference(scalar())))),
    )
}

fn write(loan: LocalId) -> Stmt {
    stmt(StmtKind::Assign {
        place: Place::deref(loan),
        value: integer(20),
    })
}

fn declarations(value: LocalId, loan: LocalId) -> Vec<Stmt> {
    vec![
        stmt(StmtKind::Let {
            local: value,
            init: Some(integer(0)),
        }),
        stmt(StmtKind::Let {
            local: loan,
            init: None,
        }),
    ]
}

fn borrow(value: LocalId, loan: LocalId) -> Vec<Stmt> {
    vec![
        stmt(StmtKind::BorrowMut {
            dest: loan,
            place: Place::local(value),
        }),
        write(loan),
    ]
}

fn choose(flag: LocalId) -> Vec<Stmt> {
    vec![
        stmt(StmtKind::Let {
            local: flag,
            init: None,
        }),
        stmt(StmtKind::Call {
            callee: choice_id(),
            type_args: vec![],
            args: vec![],
            dest: Some(Place::local(flag)),
            site: SiteId(1),
        }),
    ]
}

fn leave(target: u32, site: u32) -> Stmt {
    stmt(StmtKind::Break {
        target: LoopId(target),
        site: SiteId(site),
    })
}

fn isolated(number: u32, body: Vec<Stmt>) -> Stmt {
    let base = 10 + number * 10;
    Stmt::new(
        SpanId(100 + number),
        StmtKind::Loop(Box::new(Loop {
            id: LoopId(number),
            isolation: true,
            allow_complex_invariants: false,
            cond: None,
            invariants: vec![],
            decreases: vec![],
            body: Block::new(body),
            sites: LoopSites {
                entry: SiteId(base),
                end: SiteId(base + 1),
                exit: SiteId(base + 2),
            },
        })),
    )
}

fn source(scenario: Scenario) -> VcCrate {
    let mut caller = function(Ty::Unit);
    let value = add(&mut caller, scalar(), Mode::Exec, LocalKind::Let);
    let loan = add(&mut caller, reference(scalar()), Mode::Exec, LocalKind::Let);
    let flag = add(&mut caller, Ty::Bool, Mode::Exec, LocalKind::Let);
    let mut statements = Vec::new();
    match scenario {
        Scenario::Stable | Scenario::LaterWrite => {
            statements.extend(declarations(value, loan));
            statements.extend(borrow(value, loan));
            // The assertion also lies on an immediate terminating path:
            // assert; choose true; break; then the optional later write.
            let mut body = vec![assertion(resolved(loan), 0)];
            body.extend(choose(flag));
            body.push(stmt(StmtKind::If {
                cond: read(flag, Ty::Bool),
                then_block: Block::new(vec![leave(0, 13)]),
                else_block: Block::default(),
            }));
            statements.push(isolated(0, body));
            if matches!(scenario, Scenario::LaterWrite) {
                statements.push(write(loan));
            }
        }
        Scenario::LoopLocal => {
            let mut body = choose(flag);
            body.push(stmt(StmtKind::If {
                cond: read(flag, Ty::Bool),
                then_block: Block::new(vec![leave(0, 13)]),
                else_block: Block::default(),
            }));
            body.extend(declarations(value, loan));
            body.extend(borrow(value, loan));
            body.push(assertion(resolved(loan), 0));
            body.push(stmt(StmtKind::Continue {
                target: LoopId(0),
                site: SiteId(14),
            }));
            statements.push(isolated(0, body));
        }
        Scenario::PartialInitialization => {
            statements.extend(declarations(value, loan));
            let mut body = choose(flag);
            let mut initialized_exit = borrow(value, loan);
            initialized_exit.push(leave(0, 13));
            body.push(stmt(StmtKind::If {
                cond: read(flag, Ty::Bool),
                then_block: Block::new(initialized_exit),
                // This uninitialized path leaves the function, so every
                // normal loop exit has initialized the owned reference.
                else_block: Block::new(vec![stmt(StmtKind::Return {
                    value: None,
                    site: SiteId(91),
                })]),
            }));
            statements.push(isolated(0, body));
            statements.push(assertion(resolved(loan), 0));
        }
        Scenario::BreakOuter | Scenario::BreakInner => {
            statements.extend(declarations(value, loan));
            statements.extend(borrow(value, loan));
            let mut inner = choose(flag);
            inner.push(stmt(StmtKind::If {
                cond: read(flag, Ty::Bool),
                then_block: Block::new(vec![
                    assertion(resolved(loan), 0),
                    leave(
                        if matches!(scenario, Scenario::BreakOuter) {
                            0
                        } else {
                            1
                        },
                        23,
                    ),
                ]),
                else_block: Block::default(),
            }));
            inner.push(write(loan));
            inner.push(leave(1, 24));
            statements.push(isolated(0, vec![isolated(1, inner)]));
        }
    }
    statements.push(ret(None));
    caller.body = Body::Stmts(Block::new(statements));

    // The executable body is real, but without a postcondition the modular
    // call result is an arbitrary Bool. Its default MayUnwind is retained.
    let mut choice = function(Ty::Bool);
    choice.id = choice_id();
    choice.name = "some_bool".into();
    choice.body = Body::Stmts(Block::new(vec![ret(Some(Expr::bool_lit(true, span())))]));
    let mut source = krate(caller);
    source.fns.push(choice);
    source
}

fn require(scenario: Scenario, proved: bool) {
    let source = source(scenario);
    let errors = check_crate(&source);
    assert!(errors.is_empty(), "{scenario:?}: {errors:?}");
    let generated = vcgen::generate(&source);
    assert_eq!(generated.fns.len(), 2);
    for function in &source.fns {
        assert!(
            matches!(generated.get(function.id), Some(FnVcs::Checks(_))),
            "{scenario:?}: an owned loop must generate actual checks: {generated:?}"
        );
    }
    let Some(FnVcs::Checks(checks)) = generated.get(id()) else {
        unreachable!()
    };
    assert_eq!(checks.len(), 1, "{scenario:?}: {checks:?}");
    assert!(matches!(generated.get(choice_id()), Some(FnVcs::Checks(checks)) if checks.is_empty()));
    let check = &checks[0];
    assert_eq!(check.site, SiteId(0));
    assert_eq!(
        check.kind,
        CheckKind::Assert {
            span: span(),
            attrs: ClauseAttrs::default()
        }
    );
    let group = match scenario {
        Scenario::PartialInitialization => QueryGroup::Body,
        Scenario::BreakOuter | Scenario::BreakInner => QueryGroup::Loop {
            index: 0,
            span: SpanId(101),
        },
        _ => QueryGroup::Loop {
            index: 0,
            span: SpanId(100),
        },
    };
    assert_eq!(check.group, group, "{scenario:?}");
    assert!(!check.approximate && !check.order_unknown);
    assert!(check.query.architectures.is_none() && check.query.bitvector.is_none());
    assert!(
        matches!(&check.query.goal, Term::Call { name, .. } if name == "has_resolved"),
        "{scenario:?}: the actual nonliteral resolution goal must reach AY: {:?}",
        check.query.goal
    );
    let answer = check_detailed(
        &check.query,
        "owned-reference isolated-loop resolution",
        &Limits::default(),
    );
    assert!(
        if proved {
            matches!(answer.verdict, Verdict::Proved { .. })
        } else {
            matches!(answer.verdict, Verdict::Refuted { .. })
        },
        "{scenario:?}: expected proved={proved}: {answer:?}; check={check:?}"
    );
}

#[test]
fn a_stable_owned_reference_resolves_at_an_isolated_loop_header() {
    require(Scenario::Stable, true);
}

#[test]
fn a_write_after_the_loop_blocks_resolution_inside_the_loop() {
    require(Scenario::LaterWrite, false);
}

#[test]
fn a_loop_local_borrow_resolves_before_continue_and_reinitializes_next_iteration() {
    require(Scenario::LoopLocal, true);
}

#[test]
fn only_normal_loop_exits_contribute_to_owned_reference_initialization() {
    require(Scenario::PartialInitialization, true);
}

#[test]
fn breaking_the_outer_loop_resolves_an_owned_reference_before_the_exit() {
    require(Scenario::BreakOuter, true);
}

#[test]
fn breaking_only_the_inner_loop_retains_the_outer_mutation_backedge() {
    require(Scenario::BreakInner, false);
}
