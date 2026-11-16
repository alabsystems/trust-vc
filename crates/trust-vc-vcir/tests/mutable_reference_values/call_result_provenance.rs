// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! An exact returned-carrier identity transfers its actual argument's loan.
//! A refusal is not a proof or refutation of these final semantic oracles.
use super::*;
use trust_vc_vcir::solve::{check_detailed, Limits, Verdict};
use trust_vc_vcir::vcgen::term::Term;
use trust_vc_vcir::vcgen::{CheckKind, QueryGroup};

fn identity_id() -> FnId {
    FnId(DefHash::new(133, 2))
}

fn source(correct: bool) -> VcCrate {
    let carrier = reference(scalar());
    let mut identity = function(carrier.clone());
    identity.id = identity_id();
    identity.name = "owned_reference_identity".into();
    let parameter = add(&mut identity, carrier.clone(), Mode::Exec, LocalKind::Param);
    // For new-mode references, postcondition parameters denote their entry
    // carriers. This is whole opaque identity, not equality of projections.
    identity.ensures.push(clause(eq(
        read(identity.ret, carrier.clone()),
        read(parameter, carrier.clone()),
    )));
    identity.body = Body::Stmts(Block::new(vec![ret(Some(read(
        parameter,
        carrier.clone(),
    )))]));

    let mut caller = function(Ty::Unit);
    let value = add(&mut caller, scalar(), Mode::Exec, LocalKind::Let);
    let original = add(&mut caller, carrier.clone(), Mode::Exec, LocalKind::Let);
    let returned = add(&mut caller, carrier.clone(), Mode::Exec, LocalKind::Let);
    caller.body = Body::Stmts(Block::new(vec![
        stmt(StmtKind::Let {
            local: value,
            init: Some(integer(0)),
        }),
        stmt(StmtKind::Let {
            local: original,
            init: None,
        }),
        stmt(StmtKind::BorrowMut {
            dest: original,
            place: Place::local(value),
        }),
        stmt(StmtKind::Assign {
            place: Place::deref(original),
            value: integer(7),
        }),
        stmt(StmtKind::Let {
            local: returned,
            init: None,
        }),
        Stmt::new(
            SpanId(40),
            StmtKind::Call {
                callee: identity.id,
                type_args: vec![],
                args: vec![read(original, carrier)],
                dest: Some(Place::local(returned)),
                site: SiteId(1),
            },
        ),
        assertion(
            eq(read(value, scalar()), integer(if correct { 7 } else { 8 })),
            0,
        ),
        ret(None),
    ]));
    let mut source = krate(caller);
    source.fns.push(identity);
    source
}

fn require(correct: bool) {
    let source = source(correct);
    let errors = check_crate(&source);
    assert!(errors.is_empty(), "{errors:?}");
    assert_eq!(source.fns.len(), 2);
    for function in &source.fns {
        assert_eq!(function.role, FnRole::Item);
        assert_eq!(function.mode, Mode::Exec);
        assert!(function.type_params.is_empty());
        assert!(function.attrs.instance.is_none() && !function.attrs.external_body);
        assert!(function.unwind.is_none());
    }
    let identity = &source.fns[1];
    assert_eq!(identity.id, identity_id());
    assert_eq!(identity.ensures.len(), 1);
    assert!(!identity.ensures[0].attrs.is_labelled());
    let ExprKind::Binary {
        op: BinOp::Eq,
        lhs,
        rhs,
        check: None,
    } = &identity.ensures[0].expr.kind
    else {
        panic!("the contract must state exact opaque-carrier identity");
    };
    assert_eq!(lhs.ty, reference(scalar()));
    assert_eq!(rhs.ty, reference(scalar()));
    assert!(matches!(&lhs.kind, ExprKind::Read(place) if *place == Place::local(identity.ret)));
    assert!(
        matches!(&rhs.kind, ExprKind::Read(place) if *place == Place::local(identity.params[0]))
    );

    let generated = vcgen::generate(&source);
    assert_eq!(generated.fns.len(), 2);
    // Check the real callee before requiring the currently unsupported caller.
    let Some(FnVcs::Checks(postconditions)) = generated.get(identity.id) else {
        panic!("the original identity body must be checked: {generated:?}");
    };
    assert_eq!(postconditions.len(), 1, "{postconditions:?}");
    let postcondition = &postconditions[0];
    assert_eq!(postcondition.site, SiteId(9));
    assert_eq!(postcondition.group, QueryGroup::Body);
    assert_eq!(
        postcondition.kind,
        CheckKind::Postcondition {
            exit: span(),
            clause: 0
        }
    );
    assert!(!postcondition.approximate && !postcondition.order_unknown);
    // Returning the very parameter can simplify this identity to true. It
    // still is a real checked postcondition; only the caller below claims a
    // nonliteral query that necessarily reaches Core and AY.
    let callee = check_detailed(
        &postcondition.query,
        "checked identity postcondition",
        &Limits::default(),
    );
    assert!(
        matches!(callee.verdict, Verdict::Proved { .. }),
        "{callee:?}"
    );

    let Some(FnVcs::Checks(checks)) = generated.get(id()) else {
        panic!("the original caller must reach real VC generation: {generated:?}");
    };
    assert_eq!(checks.len(), 1, "{checks:?}");
    let check = &checks[0];
    assert_eq!(check.site, SiteId(0));
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
        "the caller must send its nonliteral query to AY"
    );
    let result = check_detailed(
        &check.query,
        "owned call-result identity provenance",
        &Limits::default(),
    );
    assert!(
        if correct {
            matches!(result.verdict, Verdict::Proved { .. })
        } else {
            matches!(result.verdict, Verdict::Refuted { .. })
        },
        "expected proved={correct}: {result:?}; check={check:?}"
    );
}

#[test]
fn an_exact_call_result_identity_returns_the_consumed_loan_to_its_owner() {
    require(true);
}

#[test]
fn returned_call_identity_does_not_prove_a_false_storage_value() {
    require(false);
}
