//! Real typed declarations, source witnesses and optional choice diagnostics.

use super::super::{query::CheckKind, relevance::Position, spec::Tables};
use super::*;
use crate::{
    Block, Body, Clause, DefHash, FnAttrs, FnDecl, FnKind, FnRole, LocalDecl, LocalKind, Mode,
    Stmt, StmtKind, VcCrate,
};
use std::{cell::Cell, rc::Rc};

fn id(number: u64) -> FnId {
    FnId(DefHash::new(58, number))
}
fn read(local: u32) -> Expr {
    Expr::read(Place::local(LocalId(local)), Ty::int(), SpanId(0))
}
fn call(number: u64, value: Expr) -> Expr {
    Expr::new(
        Ty::int(),
        SpanId(0),
        ExprKind::Call {
            callee: id(number),
            type_args: vec![],
            args: vec![value],
        },
    )
}
fn equality(left: Expr, right: Expr) -> Expr {
    Expr::binary(BinOp::Eq, left, right, Ty::Bool, SpanId(0))
}
fn chosen(impossible: bool, hint: u64) -> Expr {
    let value = read(2);
    let application = call(1, value.clone());
    let condition = if impossible {
        Expr::binary(
            BinOp::Ne,
            application.clone(),
            application,
            Ty::Bool,
            SpanId(0),
        )
    } else {
        equality(application, Expr::int_lit(3, Ty::int(), SpanId(0)))
    };
    Expr::new(
        Ty::int(),
        SpanId(0),
        ExprKind::Choose {
            vars: vec![(LocalId(2), Ty::int())],
            triggers: vec![vec![call(hint, value.clone())]],
            cond: Box::new(condition),
            result: Box::new(value),
        },
    )
}
fn local(name: &str, ty: Ty, kind: LocalKind) -> LocalDecl {
    LocalDecl {
        name: name.into(),
        ty,
        mode: Mode::Spec,
        prophecy: crate::DeclProphecy::Default,
        mutable: false,
        kind,
        span: SpanId(0),
    }
}
fn source(impossible: bool, hint_domain: bool) -> VcCrate {
    let mut identity = FnDecl {
        id: id(1),
        name: "identity".into(),
        span: SpanId(0),
        mode: Mode::Spec,
        role: FnRole::Item,
        kind: FnKind::Function,
        copy_premises: Vec::new(),
        type_params: vec![],
        locals: vec![
            local("result", Ty::int(), LocalKind::Return),
            local("value", Ty::int(), LocalKind::Param),
        ],
        params: vec![LocalId(1)],
        ret: LocalId(0),
        requires: vec![],
        ensures: vec![],
        recommends: vec![],
        decreases: vec![],
        decreases_when: None,
        decreases_by: None,
        unwind: None,
        attrs: FnAttrs::default(),
        body: Body::Spec(read(1)),
    };
    let mut krate = VcCrate::new("actual source choice hints");
    krate.fns.push(identity.clone());
    if hint_domain {
        identity.id = id(2);
        identity.name = "hint_only".into();
        identity.recommends.push(Clause {
            span: SpanId(0),
            attrs: Default::default(),
            expr: Expr::bool_lit(false, SpanId(0)),
        });
        krate.fns.push(identity);
    }
    krate.fns.push(FnDecl {
        id: id(3),
        name: "failed_proof".into(),
        span: SpanId(0),
        mode: Mode::Proof,
        role: FnRole::Item,
        kind: FnKind::Function,
        copy_premises: Vec::new(),
        type_params: vec![],
        locals: vec![
            local("result", Ty::Unit, LocalKind::Return),
            local("chosen", Ty::int(), LocalKind::Let),
            local("bound", Ty::int(), LocalKind::Bound),
        ],
        params: vec![],
        ret: LocalId(0),
        requires: vec![],
        ensures: vec![],
        recommends: vec![],
        decreases: vec![],
        decreases_when: None,
        decreases_by: None,
        unwind: None,
        attrs: FnAttrs::default(),
        body: Body::Stmts(Block {
            stmts: vec![
                // A REAL ordinary proof assertion, not a query seed or new axiom.
                Stmt {
                    span: SpanId(0),
                    kind: StmtKind::Assert {
                        expr: equality(
                            call(1, Expr::int_lit(3, Ty::int(), SpanId(0))),
                            Expr::int_lit(3, Ty::int(), SpanId(0)),
                        ),
                        site: SiteId(0),
                        attrs: Default::default(),
                    },
                },
                Stmt {
                    span: SpanId(0),
                    kind: StmtKind::Let {
                        local: LocalId(1),
                        init: Some(chosen(impossible, if hint_domain { 2 } else { 1 })),
                    },
                },
                Stmt {
                    span: SpanId(0),
                    kind: StmtKind::Assert {
                        expr: Expr::bool_lit(false, SpanId(0)),
                        site: SiteId(1),
                        attrs: Default::default(),
                    },
                },
                Stmt {
                    span: SpanId(0),
                    kind: StmtKind::Return {
                        value: None,
                        site: SiteId(2),
                    },
                },
            ],
        }),
    });
    assert!(
        crate::check_crate(&krate).is_empty(),
        "{:?}",
        crate::check_crate(&krate)
    );
    krate
}

#[test]
fn actual_choice_hint_and_ground_witness_emit_a_negative_exists_instance() {
    let krate = source(false, false);
    let ctx = Ctx::new(&krate);
    let tables = Tables::build(&ctx, &krate);
    let reads = Reads::default();
    let mut translator =
        Tr::new(&ctx, &tables.sigs, &tables.functions, &reads).with_recommendations(true);
    let ground = translator
        .expr(&call(1, Expr::int_lit(3, Ty::int(), SpanId(0))))
        .unwrap()
        .into_leaf()
        .unwrap();
    translator.expr(&chosen(false, 1)).unwrap();
    assert_eq!(translator.checks.len(), 1);
    assert!(matches!(
        translator.checks[0].kind,
        PendingKind::ChoiceRecommendation
    ));
    let goal = translator.checks[0].cond.clone();
    let predicate = Term::eq(ground, Term::Int(3));
    let hypotheses = [(predicate.clone(), Position::default())];
    let definitions = tables
        .defs
        .values()
        .flatten()
        .map(|definition| (definition.function.as_str(), definition))
        .collect();
    let instances = quant::instantiate(
        &ctx,
        &ctx.quants.borrow(),
        &hypotheses,
        &(goal.clone(), Position::default()),
        &definitions,
        &tables,
    );
    let negative = Term::implies(goal.not(), predicate.not());
    assert!(
        instances.facts.iter().any(|(fact, _)| fact == &negative
            || matches!(fact, Term::Implies(_, body) if **body == negative)),
        "actual retained hint must match the real source application: {:?}",
        instances.facts
    );
}

#[cfg(feature = "solve")]
#[test]
fn source_ground_witness_proves_choice_existence_and_impossible_twin_refutes() {
    for impossible in [false, true] {
        let krate = source(impossible, false);
        let checks = crate::vcgen::GenerationSession::new(&krate)
            .unwrap()
            .recommendations(id(3))
            .unwrap();
        assert_eq!(checks.len(), 1);
        assert!(matches!(
            checks[0].kind,
            CheckKind::ChoiceRecommendation { .. }
        ));
        let verdict = crate::solve::check(
            &checks[0].query,
            "actual source choice witness",
            &crate::solve::Limits::default(),
        );
        assert!(
            if impossible {
                matches!(verdict, crate::solve::Verdict::Refuted { .. })
            } else {
                matches!(verdict, crate::solve::Verdict::Proved { .. })
            },
            "{verdict:?}"
        );
    }
}

#[test]
fn choice_hint_only_domains_are_not_auxiliary_recommendation_obligations() {
    let krate = source(false, true);
    let checks = crate::vcgen::GenerationSession::new(&krate)
        .unwrap()
        .recommendations(id(3))
        .unwrap();
    assert_eq!(checks.len(), 1);
    assert!(
        matches!(checks[0].kind, CheckKind::ChoiceRecommendation { .. }),
        "hint-only false recommends is not a source domain event"
    );
}

#[test]
fn refused_hint_restores_events_flags_and_bound_scope_without_refilling_work() {
    let krate = source(false, false);
    let ctx = Ctx::new(&krate);
    let tables = Tables::build(&ctx, &krate);
    let reads = Reads::default();
    let work = Rc::new(Cell::new(1024));
    let mut translator = Tr::new(&ctx, &tables.sigs, &tables.functions, &reads)
        .with_recommendations(true)
        .with_recommendation_work(work.clone());
    translator.rec_calls = Some(RecCalls {
        members: BTreeSet::new(),
        found: vec![],
        proofs: 7,
    });
    let mut expression = chosen(false, 1);
    let ExprKind::Choose { triggers, .. } = &mut expression.kind else {
        unreachable!()
    };
    // Deliberately invalid trigger DATA: exercise the real refusal after its
    // proof payload, without claiming any native/source acceptance for it.
    *triggers = vec![vec![Expr::new(
        Ty::Unit,
        SpanId(0),
        ExprKind::ProofInSpec(Block::default()),
    )]];
    assert!(translator.expr(&expression).is_err());
    assert!(translator.recommendations && translator.auxiliary_work);
    assert!(Rc::ptr_eq(&translator.inline_work, &work));
    assert!(work.get() < 1024);
    let events = translator.rec_calls.as_ref().unwrap();
    assert_eq!(events.proofs, 7);
    assert!(events.found.is_empty());
    assert!(translator.bound.is_empty() && translator.recommendation_symbols.is_empty());
}
