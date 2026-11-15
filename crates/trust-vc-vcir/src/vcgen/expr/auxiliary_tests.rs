//! Actual translator/resource mechanisms, not native-query substitutes.

use super::super::spec::Tables;
use super::*;
use crate::{Block, DefHash, VcCrate};
use std::{cell::Cell, rc::Rc};

#[test]
fn auxiliary_cached_value_copy_uses_the_retained_nearly_exhausted_grant() {
    let krate = VcCrate::new("auxiliary retained work");
    let ctx = Ctx::new(&krate);
    let tables = Tables::build(&ctx, &krate);
    let reads = Reads::default();
    let expression = Expr::bool_lit(true, SpanId(0));
    let value = Val::Leaf(Term::var("actual_hole".repeat(1024), Sort::Bool));
    let work = Rc::new(Cell::new(2));
    let mut auxiliary =
        Tr::new(&ctx, &tables.sigs, &tables.functions, &reads).with_auxiliary_work(work.clone());
    auxiliary.holes.push((&expression, value.clone()));
    assert!(auxiliary.expr(&expression).is_err());
    assert_eq!(work.get(), 0);
    assert!(auxiliary.checks.is_empty());
    let mut ordinary = Tr::new(&ctx, &tables.sigs, &tables.functions, &reads);
    ordinary.inline_work = Rc::new(Cell::new(2));
    ordinary.holes.push((&expression, value.clone()));
    assert_eq!(
        ordinary.expr(&expression).unwrap(),
        value,
        "the ordinary non-inline path did not acquire an auxiliary cap"
    );
    assert_eq!(ordinary.inline_work.get(), 2);
}

fn predicate(value: Expr) -> Expr {
    Expr::new(
        Ty::Bool,
        SpanId(0),
        ExprKind::Call {
            callee: FnId(DefHash::new(57, 2)),
            type_args: vec![],
            args: vec![value],
        },
    )
}

fn choice(hint_count: usize, proof: bool) -> Expr {
    let value = Expr::read(Place::local(LocalId(7)), Ty::int(), SpanId(0));
    let predicate = predicate(value.clone());
    let condition = if proof {
        Expr::new(
            Ty::Bool,
            SpanId(0),
            ExprKind::Let {
                local: LocalId(8),
                value: Box::new(Expr::new(
                    Ty::Unit,
                    SpanId(0),
                    ExprKind::ProofInSpec(Block::default()),
                )),
                body: Box::new(predicate.clone()),
            },
        )
    } else {
        predicate.clone()
    };
    Expr::new(
        Ty::int(),
        SpanId(0),
        ExprKind::Choose {
            vars: vec![(LocalId(7), Ty::int())],
            triggers: (0..hint_count).map(|_| vec![predicate.clone()]).collect(),
            cond: Box::new(condition),
            result: Box::new(value),
        },
    )
}

#[test]
fn auxiliary_wide_choice_hints_refuse_before_creating_a_choice_key_or_application() {
    let krate = super::super::closed_templates::tests::source();
    assert!(crate::check_crate(&krate).is_empty());
    let ctx = Ctx::new(&krate);
    let tables = Tables::build(&ctx, &krate);
    let reads = Reads::default();
    let work = Rc::new(Cell::new(16));
    let mut translator =
        Tr::new(&ctx, &tables.sigs, &tables.functions, &reads).with_auxiliary_work(work.clone());
    translator.rec_calls = Some(RecCalls {
        members: BTreeSet::new(),
        found: vec![],
        proofs: 0,
    });
    assert!(translator.expr(&choice(1024, false)).is_err());
    assert!(ctx.quants.borrow().function("ch0_0").is_none());
    assert!(translator.rec_calls.as_ref().unwrap().found.is_empty());
    assert!(work.get() < 16);
}

#[test]
fn choice_pure_skip_keeps_one_event_per_physical_proof_and_the_following_ordinal() {
    let krate = super::super::closed_templates::tests::source();
    let ctx = Ctx::new(&krate);
    let tables = Tables::build(&ctx, &krate);
    let reads = Reads::default();
    let mut translator =
        Tr::new(&ctx, &tables.sigs, &tables.functions, &reads).with_recommendations(true);
    translator.rec_calls = Some(RecCalls {
        members: BTreeSet::new(),
        found: vec![],
        proofs: 0,
    });
    translator.expr(&choice(1, true)).unwrap();
    translator
        .expr(&Expr::new(
            Ty::Unit,
            SpanId(0),
            ExprKind::ProofInSpec(Block::default()),
        ))
        .unwrap();
    let calls = translator.rec_calls.as_ref().unwrap();
    let ordinals = calls
        .found
        .iter()
        .filter_map(|event| {
            if let RecEvent::Proof(proof) = event {
                Some(proof.ordinal)
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    assert_eq!(ordinals, vec![0, 1]);
    assert_eq!(calls.proofs, 2);
    assert!(translator.recommendations);
    assert!(calls.found.iter().any(|event| matches!(
        event,
        RecEvent::Diagnostic(PendingCheck {
            kind: PendingKind::ChoiceRecommendation,
            ..
        })
    )));
}

#[test]
fn pure_choice_refusal_restores_the_actual_auxiliary_event_stream() {
    let krate = super::super::closed_templates::tests::source();
    let ctx = Ctx::new(&krate);
    let tables = Tables::build(&ctx, &krate);
    let reads = Reads::default();
    let work = Rc::new(Cell::new(1));
    let mut translator = Tr::new(&ctx, &tables.sigs, &tables.functions, &reads)
        .with_recommendations(true)
        .with_recommendation_work(work.clone());
    translator.rec_calls = Some(RecCalls {
        members: BTreeSet::new(),
        found: vec![],
        proofs: 7,
    });
    let source = choice(1, true);
    let ExprKind::Choose {
        vars,
        triggers,
        cond,
        result,
    } = &source.kind
    else {
        unreachable!()
    };
    assert!(translator
        .choice_value_without_events(&source, vars, triggers, cond, result)
        .is_err());
    assert!(translator.recommendations);
    assert_eq!(translator.rec_calls.as_ref().unwrap().proofs, 7);
    assert!(translator.rec_calls.as_ref().unwrap().found.is_empty());
    assert!(ctx.quants.borrow().function("ch0_0").is_none());
}

fn generic_formal_id(number: u64) -> FnId {
    FnId(DefHash::new(59, number))
}

fn generic_formal_local(name: &str, ty: Ty, kind: crate::LocalKind) -> crate::LocalDecl {
    crate::LocalDecl {
        name: name.into(),
        ty,
        mode: crate::Mode::Spec,
        mutable: false,
        kind,
        span: SpanId(0),
    }
}

fn generic_formal_application(actual: &Ty, allowed: bool, limit: i128) -> Expr {
    let value = if *actual == Ty::Bool {
        Expr::bool_lit(true, SpanId(0))
    } else {
        Expr::int_lit(7, actual.clone(), SpanId(0))
    };
    Expr::new(
        actual.clone(),
        SpanId(0),
        ExprKind::Call {
            callee: generic_formal_id(1),
            type_args: vec![actual.clone()],
            args: vec![
                value,
                Expr::bool_lit(allowed, SpanId(0)),
                Expr::int_lit(limit, Ty::int(), SpanId(0)),
            ],
        },
    )
}

fn generic_formal_source(actual: &Ty, allowed: bool, limit: i128) -> VcCrate {
    use crate::{Body, Clause, FnAttrs, FnDecl, FnKind, FnRole, LocalKind, Mode, Stmt, StmtKind};
    let read = |local, ty| Expr::read(Place::local(LocalId(local)), ty, SpanId(0));
    let mut krate = VcCrate::new("generic source recommends parameters");
    krate.architecture = crate::bitvector::Architecture::Either32Or64;
    krate.fns.push(FnDecl {
        id: generic_formal_id(1),
        name: "source_identity".into(),
        span: SpanId(0),
        mode: Mode::Spec,
        role: FnRole::Item,
        kind: FnKind::Function,
        type_params: vec!["A".into()],
        locals: vec![
            generic_formal_local("result", Ty::Param(0), LocalKind::Return),
            generic_formal_local("value", Ty::Param(0), LocalKind::Param),
            generic_formal_local("allowed", Ty::Bool, LocalKind::Param),
            generic_formal_local("limit", Ty::int(), LocalKind::Param),
        ],
        params: vec![LocalId(1), LocalId(2), LocalId(3)],
        ret: LocalId(0),
        requires: vec![],
        ensures: vec![],
        recommends: vec![
            Clause {
                span: SpanId(0),
                attrs: Default::default(),
                expr: read(2, Ty::Bool),
            },
            Clause {
                span: SpanId(0),
                attrs: Default::default(),
                expr: Expr::binary(
                    BinOp::Gt,
                    read(3, Ty::int()),
                    Expr::int_lit(0, Ty::int(), SpanId(0)),
                    Ty::Bool,
                    SpanId(0),
                ),
            },
        ],
        decreases: vec![],
        decreases_when: None,
        decreases_by: None,
        attrs: FnAttrs::default(),
        body: Body::Spec(read(1, Ty::Param(0))),
    });
    let false_result = if *actual == Ty::Bool {
        Expr::bool_lit(false, SpanId(0))
    } else {
        Expr::int_lit(8, actual.clone(), SpanId(0))
    };
    krate.fns.push(FnDecl {
        id: generic_formal_id(2),
        name: "real_false_assertion".into(),
        span: SpanId(0),
        mode: Mode::Proof,
        role: FnRole::Item,
        kind: FnKind::Function,
        type_params: vec![],
        locals: vec![generic_formal_local("result", Ty::Unit, LocalKind::Return)],
        params: vec![],
        ret: LocalId(0),
        requires: vec![],
        ensures: vec![],
        recommends: vec![],
        decreases: vec![],
        decreases_when: None,
        decreases_by: None,
        attrs: FnAttrs::default(),
        body: Body::Stmts(Block {
            stmts: vec![
                Stmt {
                    span: SpanId(0),
                    kind: StmtKind::Assert {
                        expr: Expr::binary(
                            BinOp::Eq,
                            generic_formal_application(actual, allowed, limit),
                            false_result,
                            Ty::Bool,
                            SpanId(0),
                        ),
                        site: SiteId(0),
                        attrs: Default::default(),
                    },
                },
                Stmt {
                    span: SpanId(0),
                    kind: StmtKind::Return {
                        value: None,
                        site: SiteId(1),
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
fn generic_uf_diagnostic_formals_keep_native_bool_and_integer_values() {
    for actual in [Ty::Bool, Ty::Int(crate::IntRange::U(8))] {
        for (allowed, limit) in [(true, 1), (false, 1), (true, 0)] {
            let krate = generic_formal_source(&actual, allowed, limit);
            let ctx = Ctx::new(&krate);
            let tables = Tables::build(&ctx, &krate);
            let reads = Reads::default();
            let mut translator =
                Tr::new(&ctx, &tables.sigs, &tables.functions, &reads).with_recommendations(true);
            let result = translator
                .expr(&generic_formal_application(&actual, allowed, limit))
                .unwrap();
            assert_eq!(
                result.into_leaf().unwrap().sort(),
                if actual == Ty::Bool {
                    Sort::Bool
                } else {
                    Sort::Int
                }
            );
            assert_eq!(translator.checks.len(), 2);
            assert_eq!(translator.checks[0].cond, Term::Bool(allowed));
            assert_eq!(translator.checks[1].cond, Term::Bool(limit > 0));
            assert!(translator.checks.iter().all(|check| matches!(check.kind,
                PendingKind::Recommendation { callee, .. } if callee == generic_formal_id(1))));
            // The diagnostic native layout does not alter the generic UF ABI.
            let signature = &tables.sigs[&generic_formal_id(1)];
            let mut leaves = Vec::new();
            for shape in &signature.params {
                shape.leaves(&mut leaves);
            }
            assert_eq!(leaves.len(), 3);
            assert!(leaves.iter().all(|leaf| leaf.sort() == Sort::Poly));
        }
    }
}

#[cfg(feature = "solve")]
#[test]
fn generic_native_domain_queries_discharge_without_changing_the_primary_false_result() {
    use crate::solve::{self, Limits, Verdict};
    use crate::vcgen::{CheckKind, FnVcs};
    for actual in [Ty::Bool, Ty::Int(crate::IntRange::U(8))] {
        for (allowed, limit) in [(true, 1), (false, 1), (true, 0)] {
            let krate = generic_formal_source(&actual, allowed, limit);
            let diagnostics = crate::vcgen::Recommendations::new(&krate)
                .unwrap()
                .function(generic_formal_id(2))
                .unwrap();
            assert_eq!(diagnostics.len(), 2);
            for (check, expected) in diagnostics.iter().zip([allowed, limit > 0]) {
                assert!(
                    matches!(check.kind, CheckKind::Recommendation { callee, .. }
                    if callee == generic_formal_id(1))
                );
                let verdict =
                    solve::check(&check.query, "generic native domain", &Limits::default());
                assert!(
                    if expected {
                        matches!(verdict, Verdict::Proved { .. })
                    } else {
                        matches!(verdict, Verdict::Refuted { .. })
                    },
                    "{verdict:?}"
                );
            }
            let vcs = crate::vcgen::generate(&krate);
            let (_, FnVcs::Checks(checks)) = vcs
                .fns
                .iter()
                .find(|(id, _)| *id == generic_formal_id(2))
                .unwrap()
            else {
                panic!("{vcs:?}")
            };
            assert_eq!(checks.len(), 1);
            assert!(matches!(
                solve::check(
                    &checks[0].query,
                    "unchanged false generic result",
                    &Limits::default()
                ),
                Verdict::Refuted { .. }
            ));
        }
    }
}
