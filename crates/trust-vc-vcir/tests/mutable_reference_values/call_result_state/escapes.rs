// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! An escaped first-field loan never blocks an independent second-field loan.
use super::*;

fn hide_id() -> FnId {
    FnId(DefHash::new(133, 6))
}

fn source(correct: bool) -> VcCrate {
    let carrier = reference(scalar());
    let tuple = Ty::Tuple(vec![scalar(), scalar()]);
    let mut hide = function(Ty::Unit);
    hide.id = hide_id();
    hide.name = "checked_hide_first_field".into();
    add(&mut hide, carrier.clone(), Mode::Exec, LocalKind::Param);
    hide.body = Body::Stmts(Block::new(vec![ret(None)]));

    let mut caller = function(Ty::Unit);
    let value = add(&mut caller, tuple.clone(), Mode::Exec, LocalKind::Let);
    let parent = add(
        &mut caller,
        reference(tuple.clone()),
        Mode::Exec,
        LocalKind::Let,
    );
    let first = add(&mut caller, carrier.clone(), Mode::Exec, LocalKind::Let);
    let second = add(&mut caller, carrier.clone(), Mode::Exec, LocalKind::Let);
    let child = |index| Place {
        local: parent,
        projections: vec![Projection::Deref, Projection::TupleField(index)],
    };
    let second_storage = Place {
        local: value,
        projections: vec![Projection::TupleField(1)],
    };
    caller.body = Body::Stmts(Block::new(vec![
        stmt(StmtKind::Let {
            local: value,
            init: Some(Expr::new(
                tuple,
                span(),
                ExprKind::Tuple(vec![integer(0), integer(0)]),
            )),
        }),
        stmt(StmtKind::Let {
            local: parent,
            init: None,
        }),
        stmt(StmtKind::BorrowMut {
            dest: parent,
            place: Place::local(value),
        }),
        stmt(StmtKind::Let {
            local: first,
            init: None,
        }),
        stmt(StmtKind::BorrowMut {
            dest: first,
            place: child(0),
        }),
        Stmt::new(
            SpanId(41),
            StmtKind::Call {
                callee: hide.id,
                type_args: vec![],
                args: vec![read(first, carrier.clone())],
                dest: None,
                site: SiteId(2),
            },
        ),
        stmt(StmtKind::Let {
            local: second,
            init: None,
        }),
        stmt(StmtKind::BorrowMut {
            dest: second,
            place: child(1),
        }),
        stmt(StmtKind::Assign {
            place: Place::deref(second),
            value: integer(7),
        }),
        call(identity_id(), read(second, carrier), None),
        assertion(
            eq(
                Expr::read(second_storage, scalar(), SpanId(88)),
                integer(if correct { 7 } else { 8 }),
            ),
            0,
        ),
        ret(None),
    ]));
    let mut source = with_identity(caller, Contract::Identity);
    source.fns.push(hide);
    source
}

fn require(correct: bool) {
    let source = source(correct);
    let errors = check_crate(&source);
    assert!(errors.is_empty(), "{errors:?}");
    assert_eq!(source.fns.len(), 3);
    for f in &source.fns {
        assert_eq!(f.role, FnRole::Item);
        assert_eq!(f.mode, Mode::Exec);
        assert!(f.type_params.is_empty() && f.attrs.instance.is_none());
        assert!(!f.attrs.external_body && f.unwind.is_none());
    }
    assert!(source.fns[2].ensures.is_empty());
    let generated = vcgen::generate(&source);
    assert_eq!(generated.fns.len(), 3);
    let Some(FnVcs::Checks(hidden)) = generated.get(hide_id()) else {
        panic!("the real Hide body must be supported: {generated:?}");
    };
    assert!(hidden.is_empty(), "{hidden:?}");
    let Some(FnVcs::Checks(identity)) = generated.get(identity_id()) else {
        panic!("the real identity body must be supported: {generated:?}");
    };
    assert_eq!(identity.len(), 1, "{identity:?}");
    let post = &identity[0];
    assert_eq!((post.site, post.group), (SiteId(9), QueryGroup::Body));
    assert_eq!(
        post.kind,
        CheckKind::Postcondition {
            exit: span(),
            clause: 0
        }
    );
    assert!(!post.approximate && !post.order_unknown);
    let answer = check_detailed(&post.query, "checked sibling identity", &Limits::default());
    assert!(
        matches!(answer.verdict, Verdict::Proved { .. }),
        "{answer:?}"
    );

    let Some(FnVcs::Checks(checks)) = generated.get(id()) else {
        panic!("the final disjoint-field read must be supported: {generated:?}");
    };
    assert_eq!(checks.len(), 1, "{checks:?}");
    let check = &checks[0];
    assert_eq!((check.site, check.group), (SiteId(0), QueryGroup::Body));
    assert_eq!(
        check.kind,
        CheckKind::Assert {
            span: span(),
            attrs: ClauseAttrs::default()
        }
    );
    assert!(!check.approximate && !check.order_unknown);
    assert!(check.query.architectures.is_none() && check.query.bitvector.is_none());
    assert!(
        !matches!(check.query.goal, Term::Bool(_)),
        "the caller must reach AY"
    );
    let answer = check_detailed(
        &check.query,
        "disjoint sibling call provenance",
        &Limits::default(),
    );
    assert!(
        if correct {
            matches!(answer.verdict, Verdict::Proved { .. })
        } else {
            matches!(answer.verdict, Verdict::Refuted { .. })
        },
        "expected proved={correct}: {answer:?}; check={check:?}"
    );
}

#[test]
fn an_earlier_sibling_escape_preserves_normal_identity_writeback() {
    require(true);
}

#[test]
fn disjoint_sibling_call_writeback_does_not_prove_a_false_value() {
    require(false);
}
