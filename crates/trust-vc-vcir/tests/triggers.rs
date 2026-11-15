//! Verus's choice of triggers (`trust_vc_vcir::triggers`) on hand-built
//! quantifier bodies: the automatic choice, manual triggers, and Verus's
//! errors for them.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! Every accepted quantifier has a twin that differs from it in one place
//! and gets Verus's error, or the other way round.

use trust_vc_vcir::triggers::{
    build_triggers, msg_not_covered, AutoMode, Mark, Quantifier, TriggerError, MSG_BOOL_IN_TRIGGER,
    MSG_INEQ_IN_TRIGGER, MSG_MANUAL_AND_AUTO, MSG_NO_TRIGGERS, MSG_TRIGGER_FORM,
};
use trust_vc_vcir::{BinOp, DefHash, Expr, ExprKind, FnId, LocalId, Place, SpanId, Ty};

const X: LocalId = LocalId(1);
const Y: LocalId = LocalId(2);
/// A local bound outside the quantifier.
const N: LocalId = LocalId(3);

const P: u64 = 1;
const Q: u64 = 2;
const G: u64 = 3;

fn span() -> SpanId {
    SpanId(1)
}

fn rd(local: LocalId) -> Expr {
    Expr::read(Place::local(local), Ty::int(), span())
}

fn lit(value: i128) -> Expr {
    Expr::int_lit(value, Ty::int(), span())
}

fn call(f: u64, args: Vec<Expr>, ty: Ty) -> Expr {
    Expr::new(
        ty,
        span(),
        ExprKind::Call {
            callee: FnId(DefHash::new(0, f)),
            type_args: Vec::new(),
            args,
        },
    )
}

/// `p(args)`, a spec predicate.
fn p(args: Vec<Expr>) -> Expr {
    call(P, args, Ty::Bool)
}

/// `q(args)`, another spec predicate.
fn q(args: Vec<Expr>) -> Expr {
    call(Q, args, Ty::Bool)
}

/// `g(args)`, a spec function to `int`.
fn g(args: Vec<Expr>) -> Expr {
    call(G, args, Ty::int())
}

fn bin(op: BinOp, lhs: Expr, rhs: Expr) -> Expr {
    let ty = if op.is_arithmetic() {
        Ty::int()
    } else {
        Ty::Bool
    };
    Expr::binary(op, lhs, rhs, ty, span())
}

fn mark(term: Expr) -> Mark {
    Mark { group: None, term }
}

/// The triggers Verus chooses for `vars` over `body`.
fn choose(
    vars: &[LocalId],
    body: &Expr,
    marks: &[Mark],
    with_triggers: &[Vec<Expr>],
    auto: AutoMode,
) -> Result<Vec<Vec<Expr>>, TriggerError> {
    let local_ty = |_| Some(Ty::int());
    let q = Quantifier {
        vars,
        body,
        marks,
        with_triggers,
        auto,
        span: SpanId(9),
        local_ty: &local_ty,
        no_auto_trigger: &|_| false,
    };
    build_triggers(&q, &|id: LocalId| format!("v{}", id.index()))
}

#[track_caller]
fn message(result: Result<Vec<Vec<Expr>>, TriggerError>) -> String {
    match result {
        Err(error) => error.message,
        Ok(found) => panic!("expected Verus's error, got triggers {found:?}"),
    }
}

/// `forall|x| p(x) ==> x > 0` gets the trigger `p(x)`; with `x + 1 > 0` in
/// place of `p(x)` nothing can be a trigger (arithmetic and comparisons
/// are never chosen), which is Verus's error.
#[test]
fn an_application_is_chosen_and_arithmetic_is_not() {
    let body = bin(
        BinOp::Implies,
        p(vec![rd(X)]),
        bin(BinOp::Gt, rd(X), lit(0)),
    );
    let found = choose(&[X], &body, &[], &[], AutoMode::None).expect("triggers");
    assert_eq!(found, vec![vec![p(vec![rd(X)])]]);

    let sum = bin(BinOp::Add, rd(X), lit(1));
    let body = bin(BinOp::Gt, sum, lit(0));
    assert_eq!(
        message(choose(&[X], &body, &[], &[], AutoMode::None)),
        MSG_NO_TRIGGERS
    );
}

/// With two variables the fewest terms that cover both win: `q(x, y)`
/// alone, not `p(x)` with `q(x, y)`. Without `q`'s second argument
/// nothing covers `y`.
#[test]
fn the_smallest_cover_of_the_variables_is_chosen() {
    let body = bin(BinOp::And, p(vec![rd(X)]), q(vec![rd(X), rd(Y)]));
    let found = choose(&[X, Y], &body, &[], &[], AutoMode::None).expect("triggers");
    assert_eq!(found, vec![vec![q(vec![rd(X), rd(Y)])]]);

    let body = bin(BinOp::And, p(vec![rd(X)]), q(vec![rd(X), rd(N)]));
    assert_eq!(
        message(choose(&[X, Y], &body, &[], &[], AutoMode::None)),
        MSG_NO_TRIGGERS
    );
}

/// `forall|x| p(g(x)) == p(g(x + 1))`: `g(x)` would match `g(x + 1)`
/// with a bigger term, an obvious matching loop, so it is not chosen, and
/// nothing else is. A `#[trigger]` mark on `g(x)` is the manual choice and
/// is accepted.
#[test]
fn obvious_matching_loops_are_not_chosen_automatically() {
    let next = bin(BinOp::Add, rd(X), lit(1));
    let body = bin(BinOp::Eq, p(vec![g(vec![rd(X)])]), p(vec![g(vec![next])]));
    assert_eq!(
        message(choose(&[X], &body, &[], &[], AutoMode::None)),
        MSG_NO_TRIGGERS
    );
    let marks = [mark(g(vec![rd(X)]))];
    let found = choose(&[X], &body, &marks, &[], AutoMode::None).expect("triggers");
    assert_eq!(found, vec![vec![g(vec![rd(X)])]]);
}

/// Without an annotation only the best-scoring cover is kept: `p(x)`, the
/// shallowest. `#![all_triggers]` keeps every minimal cover, in the order
/// the terms were met.
#[test]
fn all_triggers_keeps_every_minimal_cover() {
    let body = bin(BinOp::And, p(vec![rd(X)]), q(vec![g(vec![rd(X)])]));
    let found = choose(&[X], &body, &[], &[], AutoMode::None).expect("triggers");
    assert_eq!(found, vec![vec![p(vec![rd(X)])]]);

    let found = choose(&[X], &body, &[], &[], AutoMode::All).expect("triggers");
    assert_eq!(
        found,
        vec![
            vec![p(vec![rd(X)])],
            vec![g(vec![rd(X)])],
            vec![q(vec![g(vec![rd(X)])])],
        ]
    );
}

/// A manual trigger must cover every variable: `#[trigger] q(x, y)` does,
/// `#[trigger] p(x)` misses `y`, which Verus reports by name.
#[test]
fn a_manual_trigger_covers_every_variable() {
    let body = bin(BinOp::Implies, p(vec![rd(X)]), q(vec![rd(X), rd(Y)]));
    let marks = [mark(q(vec![rd(X), rd(Y)]))];
    let found = choose(&[X, Y], &body, &marks, &[], AutoMode::None).expect("triggers");
    assert_eq!(found, vec![vec![q(vec![rd(X), rd(Y)])]]);

    let marks = [mark(p(vec![rd(X)]))];
    assert_eq!(
        message(choose(&[X, Y], &body, &marks, &[], AutoMode::None)),
        msg_not_covered(None, "v2")
    );
}

/// `#![trigger ..]` groups are taken as given and must cover every
/// variable too.
#[test]
fn trigger_groups_are_taken_as_given() {
    let body = bin(BinOp::Implies, p(vec![rd(X)]), q(vec![rd(X), rd(Y)]));
    let groups = [vec![p(vec![rd(X)]), g(vec![rd(Y)])]];
    let found = choose(&[X, Y], &body, &[], &groups, AutoMode::None).expect("triggers");
    assert_eq!(found, groups.to_vec());

    let groups = [vec![p(vec![rd(X)]), g(vec![rd(N)])]];
    assert_eq!(
        message(choose(&[X, Y], &body, &[], &groups, AutoMode::None)),
        msg_not_covered(Some(0), "v2")
    );
}

/// Manual triggers and `#![auto]` exclude each other.
#[test]
fn manual_triggers_and_auto_are_exclusive() {
    let body = p(vec![rd(X)]);
    let marks = [mark(p(vec![rd(X)]))];
    assert!(choose(&[X], &body, &marks, &[], AutoMode::None).is_ok());
    assert_eq!(
        message(choose(&[X], &body, &marks, &[], AutoMode::Auto)),
        MSG_MANUAL_AND_AUTO
    );
}

/// The forms a manual trigger may take and contain: an application may
/// hold arithmetic, but not an inequality or a boolean operator, and a
/// comparison is not a trigger at all.
#[test]
fn manual_triggers_have_verus_forms() {
    let body = p(vec![rd(X)]);
    let with_sum = [mark(g(vec![bin(BinOp::Add, rd(X), lit(1))]))];
    assert!(choose(&[X], &body, &with_sum, &[], AutoMode::None).is_ok());

    let with_lt = [mark(p(vec![bin(BinOp::Lt, rd(X), lit(1))]))];
    assert_eq!(
        message(choose(&[X], &body, &with_lt, &[], AutoMode::None)),
        MSG_INEQ_IN_TRIGGER
    );
    let with_and = [mark(p(vec![bin(
        BinOp::And,
        p(vec![rd(X)]),
        q(vec![rd(X)]),
    )]))];
    assert_eq!(
        message(choose(&[X], &body, &with_and, &[], AutoMode::None)),
        MSG_BOOL_IN_TRIGGER
    );
    let comparison = [mark(bin(BinOp::Lt, rd(X), lit(1)))];
    assert_eq!(
        message(choose(&[X], &body, &comparison, &[], AutoMode::None)),
        MSG_TRIGGER_FORM
    );
}
