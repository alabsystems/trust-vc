//! Prepared controls for actual typed source/body lowering and query admission.
//! No compiler, solver or native execution accompanies this source proposal.

use super::super::expr::Tr;
use super::super::spec::Tables;
use super::super::term::Term as MathTerm;
use super::super::trigger_pattern::Pattern;
use super::*;
use crate::{SpanId, VcCrate};
use std::sync::Arc;

fn literal(value: i128, ty: Ty) -> Expr {
    Expr::int_lit(value, ty, SpanId(0))
}

fn read(local: u32, ty: Ty) -> Expr {
    Expr::read(Place::local(LocalId(local)), ty, SpanId(0))
}

fn application(range: IntRange, op: BinOp) -> Expr {
    let ty = Ty::Int(range);
    let right = if matches!(op, BinOp::Shl | BinOp::Shr) {
        Ty::Int(IntRange::U(8))
    } else {
        ty.clone()
    };
    Expr::binary(op, read(1, ty.clone()), literal(1, right), ty, SpanId(0))
}

fn quantify(range: IntRange, pattern: Expr) -> Expr {
    let body = Expr::binary(
        BinOp::Eq,
        pattern.clone(),
        literal(2, pattern.ty.clone()),
        Ty::Bool,
        SpanId(0),
    );
    Expr::new(
        Ty::Bool,
        SpanId(0),
        ExprKind::Quant {
            kind: QuantKind::Forall,
            vars: vec![(LocalId(1), Ty::Int(range))],
            triggers: vec![vec![pattern]],
            body: Box::new(body),
        },
    )
}

fn unshared(term: &Term) -> &Term {
    match term {
        Term::Shared(inner) => unshared(inner),
        other => other,
    }
}

fn has(body: &Term, expected: &Term) -> bool {
    if body == expected {
        return true;
    }
    match body {
        Term::Shared(inner) => has(inner, expected),
        Term::App { args, .. } => args.iter().any(|arg| has(arg, expected)),
        Term::If {
            condition,
            then_term,
            else_term,
        } => has(condition, expected) || has(then_term, expected) || has(else_term, expected),
        Term::Let { value, body, .. } => has(value, expected) || has(body, expected),
        Term::Quant { body, .. } => has(body, expected),
        _ => false,
    }
}

fn vars(term: &Term, output: &mut Vec<String>) {
    match term {
        Term::Var(name) => output.push(name.clone()),
        Term::Shared(inner) => vars(inner, output),
        Term::App { args, .. } => {
            for arg in args {
                vars(arg, output);
            }
        }
        Term::If {
            condition,
            then_term,
            else_term,
        } => {
            vars(condition, output);
            vars(then_term, output);
            vars(else_term, output);
        }
        _ => {}
    }
}

#[test]
fn bitwise_family_uses_the_exact_body_application_and_current_width() {
    for width in [32, 64] {
        let krate = VcCrate::new("typed BV applications");
        let ctx = Ctx::for_width(&krate, width);
        for range in [
            IntRange::U(8),
            IntRange::I(8),
            IntRange::USize,
            IntRange::ISize,
        ] {
            for op in [
                BinOp::BitAnd,
                BinOp::BitOr,
                BinOp::BitXor,
                BinOp::Shl,
                BinOp::Shr,
            ] {
                let expr = quantify(range, application(range, op));
                let question = super::lower(&ctx, &[], &expr, &Reads::default(), width).unwrap();
                question.validate().unwrap();
                let Term::Quant {
                    binders,
                    body,
                    triggers,
                    ..
                } = unshared(&question.goal)
                else {
                    panic!("missing quantifier")
                };
                assert_eq!(binders[0].1, Sort::Bits(range.bits(width).unwrap()));
                assert!(matches!(unshared(&triggers[0][0]), Term::App { .. }));
                assert!(
                    has(body, &triggers[0][0]),
                    "trigger must be the whole actual body operation"
                );
                assert!(question.variables.is_empty() && question.requires.is_empty());
            }
        }
    }
}

#[test]
fn ordinary_post_assert_lowering_retains_real_finite_bitwise_patterns() {
    for width in [32, 64] {
        let krate = VcCrate::new("ordinary typed bitwise patterns");
        let ctx = Ctx::for_width(&krate, width);
        let tables = Tables::build(&ctx, &krate);
        let reads = Reads::default();
        for range in [
            IntRange::U(8),
            IntRange::I(8),
            IntRange::USize,
            IntRange::ISize,
        ] {
            for op in [
                BinOp::BitAnd,
                BinOp::BitOr,
                BinOp::BitXor,
                BinOp::Shl,
                BinOp::Shr,
            ] {
                let mut tr = Tr::new(&ctx, &tables.sigs, &tables.functions, &reads);
                let expr = quantify(range, application(range, op));
                let result = tr.bool(&expr);
                assert!(
                    result.is_ok(),
                    "actual source bitwise pattern refused: width={width} {range:?} {op:?}: {result:?}"
                );
            }
        }
    }
}

#[test]
fn nested_operations_and_identity_casts_keep_the_same_whole_application() {
    for width in [32, 64] {
        let krate = VcCrate::new("nested source bitwise trigger");
        let ctx = Ctx::for_width(&krate, width);
        let ty = Ty::Int(IntRange::USize);
        let and = Expr::binary(
            BinOp::BitAnd,
            read(1, ty.clone()),
            literal(3, ty.clone()),
            ty.clone(),
            SpanId(0),
        );
        let xor = Expr::binary(
            BinOp::BitXor,
            and,
            literal(1, ty.clone()),
            ty.clone(),
            SpanId(0),
        );
        let shifted = Expr::binary(
            BinOp::Shl,
            xor,
            literal(1, Ty::Int(IntRange::U(8))),
            ty,
            SpanId(0),
        );
        let pattern = Expr::new(
            Ty::Int(IntRange::Int),
            SpanId(0),
            ExprKind::Cast {
                arg: Box::new(shifted),
                kind: crate::CastKind::As,
            },
        );
        let expr = quantify(IntRange::USize, pattern);
        let question = super::lower(&ctx, &[], &expr, &Reads::default(), width).unwrap();
        let Term::Quant { body, triggers, .. } = unshared(&question.goal) else {
            panic!("missing quantifier")
        };
        assert!(has(body, &triggers[0][0]));
        let tables = Tables::build(&ctx, &krate);
        let reads = Reads::default();
        let result = Tr::new(&ctx, &tables.sigs, &tables.functions, &reads).bool(&expr);
        assert!(
            result.is_ok(),
            "nested source bitwise pattern refused: width={width}: {result:?}"
        );
    }
}

#[test]
fn signed_and_unsigned_not_keep_their_actual_interpretation_and_clip() {
    for width in [32, 64] {
        let krate = VcCrate::new("typed integer not patterns");
        let ctx = Ctx::for_width(&krate, width);
        let tables = Tables::build(&ctx, &krate);
        let reads = Reads::default();
        for range in [
            IntRange::U(8),
            IntRange::I(8),
            IntRange::USize,
            IntRange::ISize,
        ] {
            let ty = Ty::Int(range);
            let pattern = Expr::new(
                ty.clone(),
                SpanId(0),
                ExprKind::Unary {
                    op: UnOp::Not,
                    arg: Box::new(read(1, ty)),
                    check: None,
                },
            );
            let expr = quantify(range, pattern);
            let question = super::lower(&ctx, &[], &expr, &reads, width).unwrap();
            let Term::Quant { body, triggers, .. } = unshared(&question.goal) else {
                panic!("missing quantifier")
            };
            assert!(has(body, &triggers[0][0]));
            assert!(matches!(
                unshared(&triggers[0][0]),
                Term::App { op: Op::BitNot, .. }
            ));
            let result = Tr::new(&ctx, &tables.sigs, &tables.functions, &reads).bool(&expr);
            assert!(
                result.is_ok(),
                "source integer Not pattern refused: width={width} {range:?}: {result:?}"
            );
        }
    }
}

#[test]
fn nested_binders_restore_outer_values_before_lowering_its_patterns() {
    let krate = VcCrate::new("nested typed BV binders");
    let ctx = Ctx::for_width(&krate, 32);
    let inner = quantify(IntRange::U(8), application(IntRange::U(8), BinOp::BitXor));
    let outer_pattern = application(IntRange::USize, BinOp::BitAnd);
    let expr = Expr::new(
        Ty::Bool,
        SpanId(0),
        ExprKind::Quant {
            kind: QuantKind::Forall,
            vars: vec![(LocalId(1), Ty::Int(IntRange::USize))],
            triggers: vec![vec![outer_pattern]],
            body: Box::new(inner),
        },
    );
    let question = super::lower(&ctx, &[], &expr, &Reads::default(), 32).unwrap();
    let Term::Quant {
        binders,
        body,
        triggers,
        ..
    } = unshared(&question.goal)
    else {
        panic!("outer")
    };
    let Term::Quant {
        binders: inner_binders,
        triggers: inner_triggers,
        ..
    } = unshared(body)
    else {
        panic!("inner")
    };
    assert_eq!(binders[0].1, Sort::Bits(32));
    assert_eq!(inner_binders[0].1, Sort::Bits(8));
    assert_ne!(binders[0].0, inner_binders[0].0);
    let mut outer_names = Vec::new();
    vars(&triggers[0][0], &mut outer_names);
    let mut inner_names = Vec::new();
    vars(&inner_triggers[0][0], &mut inner_names);
    assert_eq!(outer_names, [binders[0].0.clone()]);
    assert_eq!(inner_names, [inner_binders[0].0.clone()]);
}

fn direct_question(patterns: Vec<Vec<Term>>) -> Query {
    Query {
        variables: vec![],
        requires: vec![],
        architecture: 64,
        goal: Term::Quant {
            forall: true,
            binders: vec![("x".into(), Sort::Bits(8)), ("y".into(), Sort::Bits(8))],
            body: Box::new(Term::Bool(false)),
            triggers: patterns,
        },
    }
}

fn app(op: Op, left: Term, right: Term) -> Term {
    Term::App {
        op,
        args: vec![left, right],
    }
}

#[test]
fn complete_multi_patterns_are_kept_and_outer_only_or_partial_coverage_refuses() {
    let x = Term::Var("x".into());
    let y = Term::Var("y".into());
    direct_question(vec![
        vec![app(Op::BitAnd, x.clone(), y.clone())],
        vec![
            app(Op::BitOr, x.clone(), y.clone()),
            app(Op::BitXor, y.clone(), x.clone()),
        ],
    ])
    .validate()
    .unwrap();
    assert!(
        direct_question(vec![vec![app(Op::BitAnd, x.clone(), x.clone())]])
            .validate()
            .is_err()
    );
    let mut outside = direct_question(vec![vec![app(
        Op::BitAnd,
        Term::Var("outer".into()),
        Term::Var("outer".into()),
    )]]);
    outside.variables.push(("outer".into(), Sort::Bits(8)));
    assert!(outside.validate().is_err());
    assert!(direct_question(vec![vec![]]).validate().is_err());
    assert!(direct_question(vec![]).validate().is_err());
}

#[test]
fn malformed_nonapplications_and_sort_or_operator_mismatches_refuse() {
    let x = Term::Var("x".into());
    let y = Term::Var("y".into());
    for term in [
        x.clone(),
        Term::Bool(false),
        Term::If {
            condition: Box::new(Term::Bool(true)),
            then_term: Box::new(x.clone()),
            else_term: Box::new(y.clone()),
        },
        app(Op::BitAnd, x.clone(), Term::Bool(true)),
        Term::App {
            op: Op::BitNot,
            args: vec![x.clone(), y.clone()],
        },
    ] {
        assert!(direct_question(vec![vec![term]]).validate().is_err());
    }
    let local_binder = Term::Let {
        name: "x".into(),
        value: Box::new(y.clone()),
        body: Box::new(x.clone()),
    };
    assert!(
        direct_question(vec![vec![app(Op::BitAnd, local_binder, y)]])
            .validate()
            .is_err()
    );
}

#[test]
fn whole_clip_validation_still_rejects_constants_variables_and_fallback_proxies() {
    for term in [
        MathTerm::Int(1),
        MathTerm::var("x", super::super::term::Sort::Int),
        MathTerm::call(
            "clip_u8_oob",
            vec![MathTerm::Int(1)],
            super::super::term::Sort::Int,
        ),
    ] {
        let pattern = Pattern::lowered_finite_clip(term, IntRange::U(8)).unwrap();
        assert!(!pattern.valid_head(&mut |_| true));
    }
    assert!(Pattern::lowered_finite_clip(MathTerm::Bool(false), IntRange::U(8)).is_none());
    assert!(Pattern::lowered_finite_clip(MathTerm::Int(1), IntRange::USize).is_none());
}

#[test]
fn repeated_trigger_edges_spend_the_original_query_grant_and_never_get_a_prefix() {
    let mut pattern = Term::Var("x".into());
    for _ in 0..18 {
        let shared = Arc::new(pattern);
        pattern = app(
            Op::BitAnd,
            Term::Shared(shared.clone()),
            Term::Shared(shared),
        );
    }
    let mut question = direct_question(vec![vec![pattern]]);
    if let Term::Quant { binders, .. } = &mut question.goal {
        binders.pop();
    }
    assert!(question.validate().unwrap_err().contains("work exhausted"));
}
