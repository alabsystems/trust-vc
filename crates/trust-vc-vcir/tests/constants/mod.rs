//! Checked constant initialization and guarded mathematical/BV reads.
//! Prepared controls; no execution is claimed by their presence.

use super::*;
use trust_vc_vcir::{ConstMode, FnKind, IntRange, IntegerConstant};

fn constant(value: Expr) -> FnDecl {
    let mut constant = Fb::new(1, "VALUE", Mode::Spec, value.ty.clone()).decl;
    constant.kind = FnKind::Constant(ConstMode::Dual);
    constant.locals[0].mode = Mode::Exec;
    constant.body = Body::Constant(value);
    constant
}

fn arithmetic(op: BinOp, left: i128, right: i128) -> Expr {
    Expr::new(
        Ty::uint(8),
        SpanId(0),
        ExprKind::Binary {
            op,
            lhs: Box::new(Expr::int_lit(left, Ty::uint(8), SpanId(0))),
            rhs: Box::new(Expr::int_lit(right, Ty::uint(8), SpanId(0))),
            check: Some(SiteId(1)),
        },
    )
}

fn both_contexts(fns: Vec<FnDecl>) -> VcCrate {
    let mut source = krate(fns);
    source.architecture = trust_vc_vcir::bitvector::Architecture::Either32Or64;
    source
}

fn reading(value: FnDecl, expected: Expr, isolated: bool) -> VcCrate {
    let mut proof = Fb::new(2, "reader", Mode::Proof, Ty::Unit);
    let call = proof.call(value.id, Vec::new(), expected.ty.clone());
    let condition = proof.cmp(BinOp::Eq, call, expected);
    let assertion = if isolated {
        let ensures = vec![proof.clause(condition)];
        let site = proof.site();
        proof.stmt(StmtKind::AssertBitVector {
            requires: Vec::new(),
            ensures,
            architecture: trust_vc_vcir::bitvector::Architecture::Either32Or64,
            site,
        })
    } else {
        proof.assert(condition)
    };
    let ret = proof.ret(None);
    both_contexts(vec![value, proof.body(vec![assertion, ret])])
}

#[test]
fn initializer_checks_and_value_equations_are_independent() {
    for isolated in [false, true] {
        for (expected, verdict) in [(3, "P"), (4, "R")] {
            let source = reading(
                constant(arithmetic(BinOp::Add, 1, 2)),
                Expr::int_lit(expected, Ty::uint(8), SpanId(0)),
                isolated,
            );
            assert!(check_crate(&source).is_empty());
            assert!(verdicts(&checks_of(&source, 1)).chars().all(|v| v == 'P'));
            assert_eq!(verdicts(&checks_of(&source, 2)), verdict);
        }
    }
}

#[test]
fn an_overflowing_initializer_cannot_prove_a_false_caller() {
    let source = reading(
        constant(arithmetic(BinOp::Add, 255, 1)),
        Expr::int_lit(7, Ty::uint(8), SpanId(0)),
        false,
    );
    assert!(check_crate(&source).is_empty());
    assert!(verdicts(&checks_of(&source, 1)).starts_with('R'));
    assert_eq!(verdicts(&checks_of(&source, 2)), "R");
    let isolated = reading(
        constant(arithmetic(BinOp::Add, 255, 1)),
        Expr::int_lit(0, Ty::uint(8), SpanId(0)),
        true,
    );
    assert_eq!(verdicts(&checks_of(&isolated, 2)), "R");
}

#[test]
fn partial_operations_keep_their_initializer_branch_guards() {
    for (take_partial, expected) in [(false, "P"), (true, "R")] {
        let value = Expr::new(
            Ty::uint(8),
            SpanId(0),
            ExprKind::If {
                cond: Box::new(Expr::bool_lit(take_partial, SpanId(0))),
                then_expr: Box::new(arithmetic(BinOp::Div, 1, 0)),
                else_expr: Box::new(Expr::int_lit(7, Ty::uint(8), SpanId(0))),
            },
        );
        let source = reading(
            constant(value),
            Expr::int_lit(7, Ty::uint(8), SpanId(0)),
            true,
        );
        assert!(check_crate(&source).is_empty());
        assert_eq!(verdicts(&checks_of(&source, 2)), expected);
        let initialization = checks_of(&source, 1);
        if take_partial {
            assert!(matches!(
                initialization.first().map(|check| &check.kind),
                Some(CheckKind::DivByZero { .. })
            ));
            assert!(verdicts(&initialization).starts_with('R'));
        } else {
            // No operation executes on the false branch. The observed caller
            // proof above must still establish the actual value in both widths.
            assert!(initialization
                .iter()
                .all(|check| !matches!(check.kind, CheckKind::DivByZero { .. })));
            assert!(verdicts(&initialization)
                .chars()
                .all(|verdict| verdict == 'P'));
        }
    }
}

#[test]
fn word_dependent_initializers_are_not_frozen_to_the_host() {
    let word_bits = Expr::new(
        Ty::uint(32),
        SpanId(0),
        ExprKind::IntegerConstant(IntegerConstant::Bits(IntRange::USize)),
    );
    for isolated in [false, true] {
        let source = reading(constant(word_bits.clone()), word_bits.clone(), isolated);
        assert_eq!(verdicts(&checks_of(&source, 2)), "P");
        let false_source = reading(
            constant(word_bits.clone()),
            Expr::int_lit(64, Ty::uint(32), SpanId(0)),
            isolated,
        );
        assert_eq!(verdicts(&checks_of(&false_source, 2)), "R");
    }
}

#[test]
fn an_abstract_trait_constant_has_no_value_definition() {
    let mut abstract_value = constant(Expr::int_lit(7, Ty::uint(8), SpanId(0)));
    abstract_value.role = FnRole::TraitDecl;
    abstract_value.type_params = vec!["Self".into()];
    abstract_value.body = Body::None;
    let mut source = reading(
        abstract_value,
        Expr::int_lit(7, Ty::uint(8), SpanId(0)),
        false,
    );
    let Body::Stmts(block) = &mut source.fns[1].body else {
        panic!("reader body")
    };
    let StmtKind::Assert { expr, .. } = &mut block.stmts[0].kind else {
        panic!("assertion")
    };
    let ExprKind::Binary { lhs, .. } = &mut expr.kind else {
        panic!("equality")
    };
    let ExprKind::Call { type_args, .. } = &mut lhs.kind else {
        panic!("constant read")
    };
    *type_args = vec![Ty::uint(8)];
    assert!(check_crate(&source).is_empty());
    assert!(matches!(
        generate(&source).get(fn_id(1)),
        Some(FnVcs::Declared)
    ));
    assert_eq!(verdicts(&checks_of(&source, 2)), "R");
}

#[test]
fn spec_body_does_not_stand_for_an_executable_initializer() {
    let mut value = constant(Expr::int_lit(3, Ty::uint(8), SpanId(0)));
    value.body = Body::Spec(Expr::int_lit(3, Ty::uint(8), SpanId(0)));
    assert!(!check_crate(&krate(vec![value])).is_empty());
}

#[test]
fn checked_shifts_cannot_use_a_fitting_zero_result_as_initializer_validity() {
    for count in [1, 8] {
        let value = arithmetic(BinOp::Shl, 0, count);
        let source = reading(
            constant(value),
            Expr::int_lit(0, Ty::uint(8), SpanId(0)),
            true,
        );
        assert!(check_crate(&source).is_empty());
        let generated = generate(&source);
        assert!(matches!(generated.get(fn_id(1)), Some(FnVcs::Refused(_))));
        assert!(matches!(generated.get(fn_id(2)), Some(FnVcs::Refused(_))));
    }
    // The existing mathematical BV shift remains supported independently of
    // the deliberately unavailable exec checked-shift representation.
    let mut proof = Fb::new(2, "reader", Mode::Proof, Ty::Unit);
    let mut shift = arithmetic(BinOp::Shl, 0, 1);
    let ExprKind::Binary { check, .. } = &mut shift.kind else {
        unreachable!()
    };
    *check = None;
    let condition = proof.cmp(BinOp::Eq, shift, Expr::int_lit(0, Ty::uint(8), SpanId(0)));
    let ensures = vec![proof.clause(condition)];
    let site = proof.site();
    let assertion = proof.stmt(StmtKind::AssertBitVector {
        requires: Vec::new(),
        ensures,
        architecture: trust_vc_vcir::bitvector::Architecture::Either32Or64,
        site,
    });
    let ret = proof.ret(None);
    assert_eq!(
        verdicts(&checks_of(
            &both_contexts(vec![proof.body(vec![assertion, ret])]),
            2
        )),
        "P"
    );
}
