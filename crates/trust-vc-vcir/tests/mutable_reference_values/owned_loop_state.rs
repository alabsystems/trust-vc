// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Ownership-cut controls beyond the unchanged canonical isolated-loop oracles.
use super::*;
use trust_vc_vcir::solve::{check_detailed, Limits, Verdict};
use trust_vc_vcir::vcgen::term::Term;
use trust_vc_vcir::vcgen::{CheckKind, InvariantAt, QueryGroup};

#[path = "owned_loop_state/availability.rs"]
mod availability;
#[path = "owned_loop_state/may_sources.rs"]
mod may_sources;
#[path = "owned_loop_state/moves.rs"]
mod moves;
#[path = "owned_loop_state/nested.rs"]
mod nested;
#[path = "owned_loop_state/proxies.rs"]
mod proxies;
#[path = "owned_loop_state/resources.rs"]
mod resources;
#[path = "owned_loop_state/snapshots.rs"]
mod snapshots;
#[path = "owned_loop_state/unknown_aliases.rs"]
mod unknown_aliases;
#[path = "owned_loop_state/writeback.rs"]
mod writeback;

fn choose_id() -> FnId {
    FnId(DefHash::new(133, 2))
}

fn resolved(loan: LocalId) -> Expr {
    Expr::new(
        Ty::Bool,
        span(),
        ExprKind::HasResolved(Box::new(read(loan, reference(scalar())))),
    )
}

fn write(loan: LocalId, value: i128) -> Stmt {
    stmt(StmtKind::Assign {
        place: Place::deref(loan),
        value: integer(value),
    })
}

fn initial(value: LocalId, loan: LocalId) -> Vec<Stmt> {
    vec![
        stmt(StmtKind::Let {
            local: value,
            init: Some(integer(0)),
        }),
        stmt(StmtKind::Let {
            local: loan,
            init: None,
        }),
        stmt(StmtKind::BorrowMut {
            dest: loan,
            place: Place::local(value),
        }),
    ]
}

fn choose(flag: LocalId, site: u32) -> Vec<Stmt> {
    vec![
        stmt(StmtKind::Let {
            local: flag,
            init: None,
        }),
        stmt(StmtKind::Call {
            callee: choose_id(),
            type_args: vec![],
            args: vec![],
            dest: Some(Place::local(flag)),
            site: SiteId(site),
        }),
    ]
}

fn leave(target: u32, site: u32) -> Stmt {
    stmt(StmtKind::Break {
        target: LoopId(target),
        site: SiteId(site),
    })
}

fn again(target: u32, site: u32) -> Stmt {
    stmt(StmtKind::Continue {
        target: LoopId(target),
        site: SiteId(site),
    })
}

fn invariant(expr: Expr) -> LoopInvariant {
    LoopInvariant {
        kind: InvariantKind::Always,
        expr,
        span: span(),
    }
}

fn isolated(number: u32, body: Vec<Stmt>, invariants: Vec<LoopInvariant>) -> Stmt {
    let base = 10 + number * 10;
    Stmt::new(
        SpanId(100 + number),
        StmtKind::Loop(Box::new(Loop {
            id: LoopId(number),
            isolation: true,
            allow_complex_invariants: false,
            cond: None,
            invariants,
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

fn with_choice(caller: FnDecl) -> VcCrate {
    let mut choice = function(Ty::Bool);
    choice.id = choose_id();
    choice.name = "some_bool".into();
    choice.body = Body::Stmts(Block::new(vec![ret(Some(Expr::bool_lit(true, span())))]));
    let mut source = krate(caller);
    source.fns.push(choice);
    source
}

fn loop_group(number: u32) -> QueryGroup {
    QueryGroup::Loop {
        index: 0,
        span: SpanId(100 + number),
    }
}

fn require(source: VcCrate, assertions: &[(u32, bool, QueryGroup)], invariants: usize) {
    let errors = check_crate(&source);
    assert!(errors.is_empty(), "{errors:?}");
    let generated = vcgen::generate(&source);
    for function in &source.fns {
        assert!(
            matches!(generated.get(function.id), Some(FnVcs::Checks(_))),
            "{generated:?}"
        );
    }
    let Some(FnVcs::Checks(checks)) = generated.get(id()) else {
        unreachable!()
    };
    assert_eq!(checks.len(), assertions.len() + invariants, "{checks:?}");
    let mut seen = vec![0; assertions.len()];
    let mut seen_invariants = 0;
    for check in checks {
        assert!(!check.approximate && !check.order_unknown);
        let proved = match &check.kind {
            CheckKind::Assert { span: at, attrs } => {
                assert_eq!((*at, attrs), (span(), &ClauseAttrs::default()));
                let index = assertions
                    .iter()
                    .position(|(site, _, _)| check.site == SiteId(*site))
                    .expect("unexpected ownership assertion site");
                seen[index] += 1;
                assert_eq!(check.group, assertions[index].2);
                assert_ne!(
                    check.query.goal,
                    Term::Bool(true),
                    "the assertion must reach AY"
                );
                assertions[index].1
            }
            CheckKind::LoopInvariant {
                at,
                invariant,
                kind,
            } => {
                assert_eq!((*invariant, *kind), (span(), InvariantKind::Always));
                let expected = match at {
                    InvariantAt::Entry => (SiteId(10), QueryGroup::Body),
                    InvariantAt::End => (SiteId(11), loop_group(0)),
                    InvariantAt::Break(_) => (SiteId(13), loop_group(0)),
                    other => panic!("unexpected invariant transition: {other:?}"),
                };
                assert_eq!((check.site, check.group), expected);
                seen_invariants += 1;
                true
            }
            other => panic!("unexpected ownership check: {other:?}"),
        };
        let answer = check_detailed(
            &check.query,
            "owned loop state collateral",
            &Limits::default(),
        );
        assert!(
            if proved {
                matches!(answer.verdict, Verdict::Proved { .. })
            } else {
                matches!(answer.verdict, Verdict::Refuted { .. })
            },
            "expected proved={proved}: {answer:?}; check={check:?}"
        );
    }
    assert_eq!(seen, vec![1; assertions.len()]);
    assert_eq!(seen_invariants, invariants);
}

fn require_refusal(source: VcCrate, tag: &str) {
    let errors = check_crate(&source);
    assert!(errors.is_empty(), "{errors:?}");
    let generated = vcgen::generate(&source);
    assert!(
        matches!(generated.get(id()), Some(FnVcs::Refused(problem)) if problem.tag == tag),
        "expected {tag}: {generated:?}"
    );
    for function in source.fns.iter().skip(1) {
        assert!(
            matches!(generated.get(function.id), Some(FnVcs::Checks(_))),
            "{generated:?}"
        );
    }
}
