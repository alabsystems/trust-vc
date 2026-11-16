//! Rejected source binders retain their typed structure for diagnostics only.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>

use trust_vc_vcir::vcgen::{self, FnVcs};
use trust_vc_vcir::*;

fn id(number: u64) -> FnId {
    FnId(DefHash::new(81, number))
}
fn read(local: u32, ty: Ty, span: u32) -> Expr {
    Expr::read(Place::local(LocalId(local)), ty, SpanId(span))
}
fn choice() -> Expr {
    Expr::new(
        Ty::int(),
        SpanId(10),
        ExprKind::UntriggeredChoose {
            vars: vec![(LocalId(1), Ty::int())],
            trigger_candidates: vec![read(1, Ty::int(), 11)],
            cond: Box::new(Expr::binary(
                BinOp::Eq,
                read(1, Ty::int(), 12),
                Expr::int_lit(3, Ty::int(), SpanId(13)),
                Ty::Bool,
                SpanId(14),
            )),
            result: Box::new(read(1, Ty::int(), 15)),
        },
    )
}
fn quantifier() -> Expr {
    Expr::new(
        Ty::Bool,
        SpanId(10),
        ExprKind::UntriggeredQuant {
            kind: QuantKind::Forall,
            vars: vec![(LocalId(1), Ty::int())],
            trigger_candidates: vec![read(1, Ty::int(), 11)],
            body: Box::new(Expr::binary(
                BinOp::Eq,
                read(1, Ty::int(), 12),
                Expr::int_lit(3, Ty::int(), SpanId(13)),
                Ty::Bool,
                SpanId(14),
            )),
        },
    )
}
fn function(number: u64, body: Expr) -> FnDecl {
    FnDecl {
        id: id(number),
        name: format!("source_{number}"),
        span: SpanId(1),
        mode: Mode::Spec,
        role: FnRole::Item,
        kind: FnKind::Function,
        type_params: vec![],
        locals: vec![
            LocalDecl {
                name: "result".into(),
                ty: body.ty.clone(),
                mode: Mode::Spec,
                prophecy: trust_vc_vcir::DeclProphecy::Default,
                mutable: false,
                kind: LocalKind::Return,
                span: SpanId(2),
            },
            LocalDecl {
                name: "bound".into(),
                ty: Ty::int(),
                mode: Mode::Spec,
                prophecy: trust_vc_vcir::DeclProphecy::Default,
                mutable: false,
                kind: LocalKind::Bound,
                span: SpanId(3),
            },
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
        body: Body::Spec(body),
    }
}
fn source(body: Expr) -> VcCrate {
    let mut krate = VcCrate::new("incomplete source binders");
    krate.fns.push(function(1, body));
    krate
}

#[test]
fn diagnostic_walk_retains_real_conditions_results_candidates_and_headers() {
    for body in [choice(), quantifier()] {
        let mut krate = source(body);
        krate.fns[0].requires.push(Clause {
            expr: Expr::bool_lit(false, SpanId(20)),
            span: SpanId(20),
            attrs: ClauseAttrs::default(),
        });
        let original = krate.clone();
        let found = check_crate_for_diagnostics(&krate);
        assert!(found.errors.is_empty(), "{:?}", found.errors);
        assert_eq!(found.incomplete_binders, [(id(1), SpanId(10))]);
        assert_eq!(
            krate, original,
            "diagnostics must not rewrite the source declaration"
        );
        let rejected = check_crate(&krate);
        assert_eq!(rejected.len(), 1, "{rejected:?}");
        assert_eq!(rejected[0].class, WfClass::Malformed);
        assert_eq!(rejected[0].span, SpanId(10));
    }
}

#[test]
fn earlier_headers_and_other_functions_are_checked_even_at_the_same_span() {
    let mut krate = source(choice());
    krate.fns[0].requires.push(Clause {
        expr: Expr::bool_lit(true, SpanId(10)),
        span: SpanId(10),
        attrs: ClauseAttrs {
            proof_notes: vec!["first".into(), "second".into()],
            ..ClauseAttrs::default()
        },
    });
    let mut earlier = function(0, Expr::bool_lit(true, SpanId(10)));
    earlier.requires.push(Clause {
        expr: Expr::bool_lit(true, SpanId(10)),
        span: SpanId(10),
        attrs: ClauseAttrs {
            custom_errs: vec!["a".into(), "b".into()],
            ..ClauseAttrs::default()
        },
    });
    krate.fns.insert(0, earlier);
    let found = check_crate_for_diagnostics(&krate);
    assert_eq!(found.incomplete_binders, [(id(1), SpanId(10))]);
    assert_eq!(found.errors.len(), 2, "{:?}", found.errors);
    for (problem, owner) in found.errors.iter().zip([id(0), id(1)]) {
        assert_eq!(problem.function, Some(owner));
        assert_eq!(problem.class, WfClass::User);
        assert_eq!(problem.span, SpanId(10));
        assert_eq!(problem.message, wf::MSG_DUPLICATE_NOTE);
    }
}

#[test]
fn diagnostic_binders_still_check_every_child_and_bound_local_type() {
    for component in 0..4 {
        let mut body = choice();
        let ExprKind::UntriggeredChoose {
            vars,
            trigger_candidates,
            cond,
            result,
        } = &mut body.kind
        else {
            unreachable!()
        };
        match component {
            0 => vars[0].1 = Ty::Bool,
            1 => trigger_candidates[0] = read(1, Ty::Bool, 11),
            2 => **cond = Expr::int_lit(1, Ty::int(), SpanId(14)),
            3 => **result = Expr::bool_lit(true, SpanId(15)),
            _ => unreachable!(),
        }
        let found = check_crate_for_diagnostics(&source(body));
        assert!(
            !found.errors.is_empty(),
            "component {component} escaped type checking"
        );
        assert!(found
            .errors
            .iter()
            .all(|error| error.class == WfClass::Malformed));
    }
    let mut body = quantifier();
    let ExprKind::UntriggeredQuant { body: inner, .. } = &mut body.kind else {
        unreachable!()
    };
    **inner = Expr::int_lit(0, Ty::int(), SpanId(14));
    assert!(check_crate_for_diagnostics(&source(body))
        .errors
        .iter()
        .any(|error| error.span == SpanId(14) && error.message.contains("not a bool")));
}

#[test]
fn ordinary_binders_without_triggers_remain_malformed_in_both_checkers() {
    for body in [choice(), quantifier()] {
        let mut ordinary = body.clone();
        ordinary.kind = match body.kind {
            ExprKind::UntriggeredChoose {
                vars, cond, result, ..
            } => ExprKind::Choose {
                vars,
                triggers: vec![],
                cond,
                result,
            },
            ExprKind::UntriggeredQuant {
                kind, vars, body, ..
            } => ExprKind::Quant {
                kind,
                vars,
                triggers: vec![],
                body,
            },
            _ => unreachable!(),
        };
        let krate = source(ordinary);
        let found = check_crate_for_diagnostics(&krate);
        assert!(found.incomplete_binders.is_empty());
        assert_eq!(found.errors, check_crate(&krate));
        assert!(found
            .errors
            .iter()
            .any(|error| error.message.contains("without triggers")));
    }
}

#[test]
fn incomplete_binders_are_rejected_before_dead_branch_folding_or_call_translation() {
    for body in [choice(), quantifier()] {
        let alternative = match body.ty {
            Ty::Bool => Expr::bool_lit(true, SpanId(30)),
            _ => Expr::int_lit(0, Ty::int(), SpanId(30)),
        };
        let hidden = Expr::new(
            body.ty.clone(),
            SpanId(31),
            ExprKind::If {
                cond: Box::new(Expr::bool_lit(false, SpanId(32))),
                then_expr: Box::new(body),
                else_expr: Box::new(alternative),
            },
        );
        let mut krate = source(hidden);
        let caller = Expr::new(
            krate.fns[0].ret_ty().unwrap().clone(),
            SpanId(40),
            ExprKind::Call {
                callee: id(1),
                type_args: vec![],
                args: vec![],
            },
        );
        krate.fns.push(function(2, caller));
        assert!(check_crate_for_diagnostics(&krate).errors.is_empty());
        let generated = vcgen::generate(&krate);
        for owner in [id(1), id(2)] {
            assert!(
                matches!(generated.get(owner), Some(FnVcs::Refused(problem))
                if problem.tag == "source-construction"),
                "{generated:?}"
            );
        }
    }
}

#[test]
fn incomplete_source_is_never_admitted_through_headers_loops_or_embedded_proofs() {
    let clause = || Clause {
        expr: quantifier(),
        span: SpanId(10),
        attrs: ClauseAttrs::default(),
    };
    let assertion = || {
        Stmt::new(
            SpanId(10),
            StmtKind::Assert {
                expr: quantifier(),
                site: SiteId(0),
                attrs: ClauseAttrs::default(),
            },
        )
    };
    let variants: Vec<FnDecl> = (0..12)
        .map(|position| {
            let mut decl = function(1, Expr::bool_lit(true, SpanId(40)));
            match position {
                0 => decl.requires.push(clause()),
                1 => decl.ensures.push(clause()),
                2 => decl.recommends.push(clause()),
                3 => decl.decreases.push(choice()),
                4 => decl.decreases_when = Some(quantifier()),
                5 => {
                    decl.body = Body::Spec(Expr::new(
                        Ty::Unit,
                        SpanId(40),
                        ExprKind::ProofInSpec(Block::new(vec![assertion()])),
                    ));
                }
                6 => {
                    decl.mode = Mode::Proof;
                    decl.attrs.external_body = true;
                    decl.body = Body::Stmts(Block::new(vec![
                        Stmt::new(
                            SpanId(40),
                            StmtKind::Return {
                                value: None,
                                site: SiteId(1),
                            },
                        ),
                        Stmt::new(SpanId(41), StmtKind::Unreachable),
                        Stmt::new(SpanId(42), StmtKind::Ghost(Block::new(vec![assertion()]))),
                    ]));
                }
                _ => {
                    let mut lp = Loop {
                        id: LoopId(0),
                        isolation: true,
                        allow_complex_invariants: false,
                        cond: Some(LoopCond {
                            block: Block::default(),
                            expr: Expr::bool_lit(true, SpanId(40)),
                        }),
                        invariants: vec![],
                        decreases: vec![],
                        body: Block::default(),
                        sites: LoopSites {
                            entry: SiteId(1),
                            end: SiteId(2),
                            exit: SiteId(3),
                        },
                    };
                    match position {
                        7 => lp.cond.as_mut().unwrap().expr = quantifier(),
                        8 => lp.cond.as_mut().unwrap().block.stmts.push(assertion()),
                        9 => lp.invariants.push(LoopInvariant {
                            kind: InvariantKind::Always,
                            expr: quantifier(),
                            span: SpanId(10),
                        }),
                        10 => lp.decreases.push(choice()),
                        11 => lp.body.stmts.push(Stmt::new(
                            SpanId(10),
                            StmtKind::AssertBitVector {
                                requires: vec![clause()],
                                ensures: vec![clause()],
                                architecture: bitvector::Architecture::Either32Or64,
                                site: SiteId(0),
                            },
                        )),
                        _ => unreachable!(),
                    }
                    decl.mode = Mode::Exec;
                    decl.body = Body::Stmts(Block::new(vec![Stmt::new(
                        SpanId(40),
                        StmtKind::Loop(Box::new(lp)),
                    )]));
                }
            }
            decl
        })
        .collect();
    for (position, decl) in variants.into_iter().enumerate() {
        let mut krate = VcCrate::new("diagnostic nodes in source positions");
        krate.fns.push(decl);
        let generated = vcgen::generate(&krate);
        assert!(
            matches!(generated.get(id(1)), Some(FnVcs::Refused(problem))
            if problem.tag == "source-construction"),
            "position {position}: {generated:?}"
        );
    }
}

#[test]
fn diagnostic_children_and_bound_names_survive_local_renaming() {
    for original in [choice(), quantifier()] {
        let renamed = original.rename_locals(&[(LocalId(1), LocalId(8))].into_iter().collect());
        let vars = match &renamed.kind {
            ExprKind::UntriggeredChoose { vars, .. } | ExprKind::UntriggeredQuant { vars, .. } => {
                vars
            }
            _ => panic!("diagnostic node became executable"),
        };
        assert_eq!(vars, &[(LocalId(8), Ty::int())]);
        let mut spans = Vec::new();
        fn walk(expr: &Expr, visit: &mut impl FnMut(&Expr)) {
            visit(expr);
            expr.for_each_child(&mut |child| walk(child, visit));
        }
        walk(&renamed, &mut |expr| {
            spans.push(expr.span);
            if let ExprKind::Read(place) = &expr.kind {
                assert_eq!(place.local, LocalId(8));
            }
        });
        for expected in [11, 12, 13, 14] {
            assert!(spans.contains(&SpanId(expected)));
        }
        if matches!(renamed.kind, ExprKind::UntriggeredChoose { .. }) {
            assert!(spans.contains(&SpanId(15)));
        }
    }
}
