//! Actual native isolated BV questions; no surrounding solver hypotheses.

mod euclidean_congruence;
mod mul_congruence;

use super::{check_bitvector, Limits, Verdict};
use trust_vc_bitvector::integer::{Arithmetic, Comparison, Integer};
use trust_vc_bitvector::{IntLit, Op, Query, Sort, Term};

fn integer(value: i128) -> Integer {
    Integer::literal(IntLit {
        negative: value < 0,
        magnitude: value.unsigned_abs(),
    })
}

fn query(goal: Term) -> Query {
    Query {
        variables: vec![],
        requires: vec![],
        goal,
        architecture: 64,
    }
}

fn proved(query: Query) {
    assert!(matches!(
        check_bitvector(&query, "bv_control", &Limits::default()),
        Verdict::Proved { .. }
    ));
}

fn refuted(query: Query) {
    assert!(matches!(
        check_bitvector(&query, "bv_control_false", &Limits::default()),
        Verdict::Refuted { .. }
    ));
}

#[test]
fn native_bv_bitwise_identity_and_false_twin() {
    let x = Integer::from_bits(Term::Var("x".into()), 8, false).unwrap();
    let mask = integer(255);
    let and = x.clone().bitwise(mask, Op::BitAnd).unwrap();
    let mut yes = query(and.compare(x.clone(), Comparison::Eq).unwrap());
    yes.variables.push(("x".into(), Sort::Bits(8)));
    proved(yes);
    let and = x.clone().bitwise(integer(1), Op::BitAnd).unwrap();
    let mut no = query(and.compare(x, Comparison::Eq).unwrap());
    no.variables.push(("x".into(), Sort::Bits(8)));
    refuted(no);
}

#[test]
fn native_bv_signed_mixed_width_casts_and_high_bits() {
    proved(query(
        integer(-1)
            .clip(16, false)
            .unwrap()
            .compare(integer(65_535), Comparison::Eq)
            .unwrap(),
    ));
    refuted(query(
        integer(-1)
            .clip(16, false)
            .unwrap()
            .compare(integer(255), Comparison::Eq)
            .unwrap(),
    ));
    let maximum = Integer::literal(IntLit {
        negative: false,
        magnitude: u128::MAX,
    });
    let doubled = maximum
        .clone()
        .arithmetic(maximum.clone(), Arithmetic::Add)
        .unwrap();
    assert_eq!(doubled.bits(), 129);
    let clipped = doubled.clip(128, false).unwrap();
    let expected = Integer::literal(IntLit {
        negative: false,
        magnitude: u128::MAX - 1,
    });
    proved(query(clipped.compare(expected, Comparison::Eq).unwrap()));
    proved(query(integer(-1).compare(maximum, Comparison::Lt).unwrap()));
}

#[test]
fn native_bv_euclidean_division_and_remainder_keep_negative_semantics() {
    for (denominator, expected_quotient) in [(2, -2), (-2, 2)] {
        let quotient = integer(-3)
            .euclidean(
                integer(denominator),
                false,
                Term::Bits {
                    value: IntLit {
                        negative: false,
                        magnitude: 0,
                    },
                    width: 4,
                },
            )
            .unwrap();
        assert_eq!(quotient.bits(), 4);
        proved(query(
            quotient
                .compare(integer(expected_quotient), Comparison::Eq)
                .unwrap(),
        ));
        let remainder = integer(-3)
            .euclidean(
                integer(denominator),
                true,
                Term::Bits {
                    value: IntLit {
                        negative: false,
                        magnitude: 0,
                    },
                    width: 3,
                },
            )
            .unwrap();
        proved(query(
            remainder.compare(integer(1), Comparison::Eq).unwrap(),
        ));
    }
}

#[test]
fn native_bv_shift_counts_do_not_wrap_and_signed_right_shift_is_arithmetic() {
    let x = Integer::from_bits(Term::Var("x".into()), 8, false).unwrap();
    let shifted = x.clone().shift_left(integer(8), 8, false).unwrap();
    let mut zero = query(shifted.compare(integer(0), Comparison::Eq).unwrap());
    zero.variables.push(("x".into(), Sort::Bits(8)));
    proved(zero);
    let shifted = x.shift_right(integer(256)).unwrap();
    let mut wide = query(shifted.compare(integer(0), Comparison::Eq).unwrap());
    wide.variables.push(("x".into(), Sort::Bits(8)));
    proved(wide);
    proved(query(
        integer(-2)
            .shift_right(integer(1))
            .unwrap()
            .compare(integer(-1), Comparison::Eq)
            .unwrap(),
    ));
    assert!(integer(1).shift_right(integer(-1)).is_err());
}

#[test]
fn native_bv_question_has_only_its_explicit_requires() {
    let x = Integer::from_bits(Term::Var("x".into()), 8, false).unwrap();
    let goal = x.compare(integer(0), Comparison::Eq).unwrap();
    let mut isolated = query(goal.clone());
    isolated.variables.push(("x".into(), Sort::Bits(8)));
    refuted(isolated.clone());
    isolated.requires.push(goal);
    proved(isolated);
}

#[test]
fn native_bv_architecture_cases_have_distinct_width_semantics() {
    for (architecture, should_prove) in [(32, true), (64, false)] {
        let x = Integer::from_bits(Term::Var("x".into()), architecture, false).unwrap();
        let result = x
            .shift_right(integer(32))
            .unwrap()
            .compare(integer(0), Comparison::Eq)
            .unwrap();
        let mut question = query(result);
        question.architecture = architecture;
        question
            .variables
            .push(("x".into(), Sort::Bits(architecture)));
        if should_prove {
            proved(question);
        } else {
            refuted(question);
        }
    }
}

#[test]
fn native_bv_rejects_bad_sort_and_undeclared_or_conflicting_bindings() {
    assert!(matches!(
        check_bitvector(
            &query(Term::Var("missing".into())),
            "bad_bv",
            &Limits::default()
        ),
        Verdict::Error { .. }
    ));
    let malformed = Term::App {
        op: Op::Add,
        args: vec![Term::Bool(true), Term::Bool(false)],
    };
    assert!(matches!(
        check_bitvector(&query(malformed), "bad_bv_sort", &Limits::default()),
        Verdict::Error { .. }
    ));
    let mut duplicate = query(Term::Bool(false));
    duplicate.variables = vec![("x".into(), Sort::Bits(8)), ("x".into(), Sort::Bits(16))];
    assert!(matches!(
        check_bitvector(&duplicate, "bad_bv_duplicate", &Limits::default()),
        Verdict::Error { .. }
    ));
}

#[test]
fn native_bv_quantified_application_preserves_positive_and_refuted_questions() {
    for width in [32, 64] {
        let x = Integer::from_bits(Term::Var("bound_x".into()), width, false).unwrap();
        let mask = x.bitwise(integer(1), Op::BitAnd).unwrap();
        let pattern = mask.clone().into_term();
        let make = |body| Query {
            variables: vec![],
            requires: vec![],
            architecture: width,
            goal: Term::Quant {
                forall: true,
                binders: vec![("bound_x".into(), Sort::Bits(width))],
                body: Box::new(body),
                triggers: vec![vec![pattern.clone()]],
            },
        };
        proved(make(
            mask.clone().compare(integer(1), Comparison::Le).unwrap(),
        ));
        refuted(make(mask.compare(integer(2), Comparison::Eq).unwrap()));
    }
}

#[test]
fn native_bv_malformed_or_unbound_trigger_is_an_error_before_solving() {
    let make = |pattern| {
        query(Term::Quant {
            forall: true,
            binders: vec![("x".into(), Sort::Bits(8))],
            body: Box::new(Term::Bool(true)),
            triggers: vec![vec![pattern]],
        })
    };
    for pattern in [
        Term::Var("x".into()),
        Term::App {
            op: Op::BitAnd,
            args: vec![Term::Var("x".into()), Term::Bool(false)],
        },
        Term::App {
            op: Op::BitOr,
            args: vec![Term::Var("free".into()), Term::Var("free".into())],
        },
    ] {
        assert!(matches!(
            check_bitvector(&make(pattern), "malformed_bv_trigger", &Limits::default()),
            Verdict::Error { .. }
        ));
    }
}
