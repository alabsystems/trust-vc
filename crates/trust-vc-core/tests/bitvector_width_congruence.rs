//! Native consumer controls for the unsigned cross-width division query
//! captured from unchanged upstream `bitvector::test_by_equating_div`.
//! The original two arbitrary zero-divisor values remain independent.

use trust_vc_bitvector::{IntLit, Op, Query, Sort, Term};
use trust_vc_core::query::{check_bitvector, Limits, Verdict};

fn app(op: Op, args: impl Into<Vec<Term>>) -> Term {
    Term::App {
        op,
        args: args.into(),
    }
}

fn var(name: &str) -> Term {
    Term::Var(name.into())
}

fn bits(value: u128, width: u32) -> Term {
    Term::Bits {
        value: IntLit {
            negative: false,
            magnitude: value,
        },
        width,
    }
}

fn division_query(architecture: u32, guarded: bool, wrong_quotient: bool) -> Query {
    let y = var("bv_place_0");
    let a = var("bv_place_1");
    let x = var("bv_place_2");
    let b = var("bv_place_3");
    let small_division = app(Op::UDiv, [a.clone(), b.clone()]);
    let small_division = if wrong_quotient {
        app(Op::Add, [small_division, bits(1, 8)])
    } else {
        small_division
    };
    let small = Term::If {
        condition: Box::new(app(Op::Eq, [b.clone(), bits(0, 8)])),
        then_term: Box::new(var("bv_arbitrary_4")),
        else_term: Box::new(small_division),
    };
    let wide_zero = app(Op::ZeroExtend(31), [bits(0, 1)]);
    let wide = Term::If {
        condition: Box::new(app(Op::Eq, [y.clone(), bits(0, 32)])),
        then_term: Box::new(var("bv_arbitrary_5")),
        else_term: Box::new(app(Op::UDiv, [x.clone(), y.clone()])),
    };
    let same_values = app(
        Op::And,
        [
            app(Op::Eq, [app(Op::ZeroExtend(24), [a]), x]),
            app(Op::Eq, [app(Op::ZeroExtend(24), [b]), y.clone()]),
        ],
    );
    let same_quotient = app(Op::Eq, [app(Op::ZeroExtend(24), [small]), wide]);
    let goal = app(Op::Implies, [same_values, same_quotient]);
    let goal = if guarded {
        let nonzero = app(Op::Not, [app(Op::Eq, [y, wide_zero])]);
        app(Op::Implies, [nonzero, goal])
    } else {
        goal
    };
    Query {
        variables: vec![
            ("bv_place_0".into(), Sort::Bits(32)),
            ("bv_place_1".into(), Sort::Bits(8)),
            ("bv_place_2".into(), Sort::Bits(32)),
            ("bv_place_3".into(), Sort::Bits(8)),
            ("bv_arbitrary_4".into(), Sort::Bits(8)),
            ("bv_arbitrary_5".into(), Sort::Bits(32)),
        ],
        requires: vec![],
        goal,
        architecture,
    }
}

fn check(architecture: u32, guarded: bool, wrong_quotient: bool) -> Verdict {
    let query = division_query(architecture, guarded, wrong_quotient);
    query.validate().expect("complete captured native BV query");
    let limits = Limits {
        wall_ms: 10_000,
        ..Limits::default()
    };
    check_bitvector(&query, "unsigned_width_congruence", &limits)
}

#[test]
fn captured_unsigned_width_congruence_proves_both_architectures() {
    for architecture in [32, 64] {
        let verdict = check(architecture, true, false);
        assert!(
            matches!(verdict, Verdict::Proved { .. }),
            "arch{architecture}: {verdict:?}"
        );
    }
}

#[test]
fn unsigned_width_congruence_refutes_an_incorrect_quotient() {
    for architecture in [32, 64] {
        let verdict = check(architecture, true, true);
        assert!(
            matches!(verdict, Verdict::Refuted { .. }),
            "arch{architecture}: {verdict:?}"
        );
    }
}

#[test]
fn unsigned_width_congruence_keeps_zero_division_values_independent() {
    for architecture in [32, 64] {
        let verdict = check(architecture, false, false);
        assert!(
            matches!(verdict, Verdict::Refuted { .. }),
            "arch{architecture}: {verdict:?}"
        );
    }
}
