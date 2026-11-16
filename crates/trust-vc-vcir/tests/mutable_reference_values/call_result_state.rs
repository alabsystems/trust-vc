// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Actual checked contracts govern returned ownership, not component equality.
use super::*;
use trust_vc_vcir::solve::{check_detailed, Limits, Verdict};
use trust_vc_vcir::vcgen::term::Term;
use trust_vc_vcir::vcgen::{CheckKind, QueryGroup};

#[path = "call_result_state/escapes.rs"]
mod escapes;
#[path = "call_result_state/tuples.rs"]
mod tuples;

#[derive(Clone, Copy)]
enum Contract {
    Absent,
    Components,
    Labelled,
    Identity,
}

#[derive(Clone, Copy)]
enum Destination {
    InPlace,
    Discard,
    Separate,
}

fn identity_id() -> FnId {
    FnId(DefHash::new(133, 5))
}

fn identity(contract: Contract) -> FnDecl {
    let carrier = reference(scalar());
    let mut f = function(carrier.clone());
    f.id = identity_id();
    f.name = "checked_returned_owner".into();
    let input = add(&mut f, carrier.clone(), Mode::Exec, LocalKind::Param);
    let result = || read(f.ret, carrier.clone());
    let original = || read(input, carrier.clone());
    f.ensures = match contract {
        Contract::Absent => vec![],
        Contract::Components => vec![
            clause(eq(current(result()), current(original()))),
            clause(eq(future(result()), future(original()))),
        ],
        Contract::Identity | Contract::Labelled => {
            let mut equality = clause(eq(result(), original()));
            if matches!(contract, Contract::Labelled) {
                equality
                    .attrs
                    .proof_notes
                    .push("checked locally, never assumed by a caller".into());
            }
            vec![equality]
        }
    };
    f.body = Body::Stmts(Block::new(vec![ret(Some(read(input, carrier)))]));
    f
}

fn resolved(value: Expr) -> Expr {
    Expr::new(Ty::Bool, span(), ExprKind::HasResolved(Box::new(value)))
}

fn call(callee: FnId, argument: Expr, destination: Option<Place>) -> Stmt {
    Stmt::new(
        SpanId(40),
        StmtKind::Call {
            callee,
            type_args: vec![],
            args: vec![argument],
            dest: destination,
            // Assertions use sites zero and one; the sibling Hide call uses two.
            site: SiteId(3),
        },
    )
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
        stmt(StmtKind::Assign {
            place: Place::deref(loan),
            value: integer(7),
        }),
    ]
}

fn with_identity(caller: FnDecl, contract: Contract) -> VcCrate {
    let mut source = krate(caller);
    source.fns.push(identity(contract));
    source
}

fn storage(contract: Contract, destination: Destination, expected: i128) -> VcCrate {
    let carrier = reference(scalar());
    let mut f = function(Ty::Unit);
    let value = add(&mut f, scalar(), Mode::Exec, LocalKind::Let);
    let loan = add(&mut f, carrier.clone(), Mode::Exec, LocalKind::Let);
    let output = add(&mut f, carrier.clone(), Mode::Exec, LocalKind::Let);
    let mut body = initial(value, loan);
    let dest = match destination {
        Destination::InPlace => Some(Place::local(loan)),
        Destination::Discard => None,
        Destination::Separate => {
            body.push(stmt(StmtKind::Let {
                local: output,
                init: None,
            }));
            Some(Place::local(output))
        }
    };
    body.push(call(identity_id(), read(loan, carrier), dest));
    body.push(assertion(eq(read(value, scalar()), integer(expected)), 0));
    body.push(ret(None));
    f.body = Body::Stmts(Block::new(body));
    with_identity(f, contract)
}

fn generated(source: &VcCrate) -> vcgen::CrateVcs {
    let errors = check_crate(source);
    assert!(errors.is_empty(), "{errors:?}");
    assert_eq!(source.fns.len(), 2);
    for f in &source.fns {
        assert_eq!(f.role, FnRole::Item);
        assert_eq!(f.mode, Mode::Exec);
        assert!(f.type_params.is_empty() && f.attrs.instance.is_none());
        assert!(!f.attrs.external_body && f.unwind.is_none());
    }
    let result = vcgen::generate(source);
    assert_eq!(result.fns.len(), 2);
    let target = &source.fns[1];
    let Some(FnVcs::Checks(checks)) = result.get(target.id) else {
        panic!("the actual callee body must be supported: {result:?}");
    };
    assert_eq!(checks.len(), target.ensures.len(), "{checks:?}");
    for (index, check) in checks.iter().enumerate() {
        assert_eq!(check.site, SiteId(9));
        assert_eq!(check.group, QueryGroup::Body);
        assert_eq!(
            check.kind,
            CheckKind::Postcondition {
                exit: span(),
                clause: index
            }
        );
        assert!(!check.approximate && !check.order_unknown);
        let answer = check_detailed(
            &check.query,
            "actual returned-owner callee",
            &Limits::default(),
        );
        assert!(
            matches!(answer.verdict, Verdict::Proved { .. }),
            "{answer:?}"
        );
    }
    result
}

fn require(source: VcCrate, expected: &[bool]) {
    let result = generated(&source);
    let Some(FnVcs::Checks(checks)) = result.get(id()) else {
        panic!("the original caller must be supported: {result:?}");
    };
    assert_eq!(checks.len(), expected.len(), "{checks:?}");
    for (index, (check, proved)) in checks.iter().zip(expected).enumerate() {
        assert_eq!(check.site, SiteId(index as u32));
        assert_eq!(check.group, QueryGroup::Body);
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
            "the assertion must reach AY"
        );
        let answer = check_detailed(&check.query, "returned-owner state", &Limits::default());
        assert!(
            if *proved {
                matches!(answer.verdict, Verdict::Proved { .. })
            } else {
                matches!(answer.verdict, Verdict::Refuted { .. })
            },
            "expected proved={proved}: {answer:?}; check={check:?}"
        );
    }
}

fn require_unreturned(contract: Contract) {
    let result = generated(&storage(contract, Destination::Separate, 7));
    assert!(
        matches!(result.get(id()), Some(FnVcs::Refused(problem))
        if problem.tag == "mut-ref-borrowed"),
        "{result:?}"
    );
}

#[test]
fn an_absent_postcondition_cannot_return_escaped_ownership() {
    require_unreturned(Contract::Absent);
}

#[test]
fn equal_current_and_future_components_do_not_return_carrier_ownership() {
    require_unreturned(Contract::Components);
}

#[test]
fn a_labelled_identity_postcondition_is_not_caller_ownership_authority() {
    require_unreturned(Contract::Labelled);
}

#[test]
fn an_in_place_result_captures_the_argument_before_its_storage_is_overwritten() {
    require(
        storage(Contract::Identity, Destination::InPlace, 7),
        &[true],
    );
}

#[test]
fn an_in_place_result_does_not_prove_a_false_storage_value() {
    require(
        storage(Contract::Identity, Destination::InPlace, 8),
        &[false],
    );
}

#[test]
fn discarding_the_returned_outer_owner_resolves_it_on_normal_return() {
    require(
        storage(Contract::Identity, Destination::Discard, 7),
        &[true],
    );
}

#[test]
fn discarding_a_returned_owner_does_not_prove_a_false_storage_value() {
    require(
        storage(Contract::Identity, Destination::Discard, 8),
        &[false],
    );
}

fn live_return(claim_resolved: bool) -> VcCrate {
    let carrier = reference(scalar());
    let mut f = function(Ty::Unit);
    let value = add(&mut f, scalar(), Mode::Exec, LocalKind::Let);
    let loan = add(&mut f, carrier.clone(), Mode::Exec, LocalKind::Let);
    let output = add(&mut f, carrier.clone(), Mode::Exec, LocalKind::Let);
    let entry_future = add(&mut f, scalar(), Mode::Spec, LocalKind::Let);
    let mut body = initial(value, loan);
    // A scalar Spec snapshot reads the actual pre-call future without
    // consuming the executable reference which the call will receive.
    body.push(stmt(StmtKind::Let {
        local: entry_future,
        init: Some(future(read(loan, carrier.clone()))),
    }));
    body.push(stmt(StmtKind::Let {
        local: output,
        init: None,
    }));
    body.push(call(
        identity_id(),
        read(loan, carrier.clone()),
        Some(Place::local(output)),
    ));
    let predicate = if claim_resolved {
        resolved(read(output, carrier.clone()))
    } else {
        eq(
            future(read(output, carrier.clone())),
            read(entry_future, scalar()),
        )
    };
    body.push(assertion(predicate, 0));
    body.push(stmt(StmtKind::Assign {
        place: Place::deref(output),
        value: integer(8),
    }));
    body.push(assertion(eq(current(read(output, carrier)), integer(8)), 1));
    body.push(ret(None));
    f.body = Body::Stmts(Block::new(body));
    with_identity(f, Contract::Identity)
}

#[test]
fn a_returned_owner_with_a_later_write_preserves_its_entry_future() {
    require(live_return(false), &[true, true]);
}

#[test]
fn a_future_write_refutes_early_resolution_of_a_returned_owner() {
    require(live_return(true), &[false, true]);
}
