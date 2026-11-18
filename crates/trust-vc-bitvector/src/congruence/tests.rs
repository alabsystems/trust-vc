use super::*;
use crate::integer::{Arithmetic, Comparison, Integer};

fn app(op: Op, a: Term, b: Term) -> Term {
    Term::App {
        op,
        args: vec![a, b],
    }
}
fn input(name: &str, bits: u32, signed: bool) -> Integer {
    Integer::from_bits(Term::Var(name.into()), bits, signed).unwrap()
}
fn query(goal: Term, small: u32, large: u32) -> Query {
    Query {
        variables: ["a", "b", "c", "d"]
            .into_iter()
            .map(|n| (n.into(), Sort::Bits(small)))
            .chain(
                ["x", "y"]
                    .into_iter()
                    .map(|n| (n.into(), Sort::Bits(large))),
            )
            .collect(),
        requires: vec![],
        goal,
        architecture: 64,
    }
}
fn congruence(
    signed_a: bool,
    signed_b: bool,
    left_sum: bool,
    right_sum: bool,
    small: u32,
    large: u32,
) -> Query {
    let mut a = input("a", small, signed_a);
    let mut b = input("c", small, signed_b);
    if left_sum {
        a = a
            .arithmetic(input("b", small, signed_a), Arithmetic::Add)
            .unwrap();
    }
    if right_sum {
        b = b
            .arithmetic(input("d", small, signed_b), Arithmetic::Add)
            .unwrap();
    }
    let x = input("x", large, true);
    let y = input("y", large, true);
    let premise = app(
        Op::And,
        a.clone().compare(x.clone(), Comparison::Eq).unwrap(),
        b.clone().compare(y.clone(), Comparison::Eq).unwrap(),
    );
    let left = a.arithmetic(b, Arithmetic::Mul).unwrap();
    let right = x.arithmetic(y, Arithmetic::Mul).unwrap();
    query(
        app(
            Op::Implies,
            premise,
            left.compare(right, Comparison::Eq).unwrap(),
        ),
        small,
        large,
    )
}
fn bare(mut term: &Term) -> &Term {
    while let Term::Shared(inner) = term {
        term = inner;
    }
    term
}
fn consequence(term: &Term) -> &Term {
    let Term::App {
        op: Op::Implies,
        args,
    } = bare(term)
    else {
        panic!("expected retained implication")
    };
    bare(&args[1])
}

#[test]
fn scoped_multiplication_congruence_covers_mixed_signs_widths_and_sums() {
    for (small, large) in [(2, 8), (8, 32), (16, 64)] {
        for signed_a in [false, true] {
            for signed_b in [false, true] {
                for (left_sum, right_sum) in [(false, false), (true, false), (false, true)] {
                    let original =
                        congruence(signed_a, signed_b, left_sum, right_sum, small, large);
                    original.validate().unwrap();
                    let changed = simplify(&original).expect("supported exact multiplication");
                    assert!(matches!(consequence(&changed.goal), Term::Bool(true)));
                    assert_eq!(changed.variables, original.variables);
                    assert_eq!(changed.requires, original.requires);
                }
            }
        }
    }
}

#[test]
fn explicit_requires_are_retained_and_no_disjunctive_equations_escape() {
    let mut original = congruence(false, true, true, false, 8, 32);
    let Term::App { args, .. } = original.goal.clone() else {
        unreachable!()
    };
    original.requires.push(args[0].clone());
    original.goal = args[1].clone();
    let changed = simplify(&original).unwrap();
    assert!(matches!(bare(&changed.goal), Term::Bool(true)));
    assert_eq!(changed.requires, original.requires);

    let mut other = congruence(false, true, true, false, 8, 32);
    let Term::App { args, .. } = &mut other.goal else {
        unreachable!()
    };
    args[0] = app(Op::Or, args[0].clone(), Term::Bool(true));
    let changed = simplify(&other).unwrap();
    assert!(!matches!(consequence(&changed.goal), Term::Bool(true)));

    let mut other = congruence(false, true, true, false, 8, 32);
    let Term::App { args, .. } = other.goal.clone() else {
        unreachable!()
    };
    other.goal = app(
        Op::And,
        app(Op::Or, args[0].clone(), Term::Bool(true)),
        args[1].clone(),
    );
    let changed = simplify(&other).unwrap();
    let Term::App { args, .. } = bare(&changed.goal) else {
        panic!()
    };
    assert!(!matches!(bare(&args[1]), Term::Bool(true)));
}

fn extended_product(width: u32, output: u32, signed_output: bool) -> Query {
    let a = Term::Var("a".into());
    let b = Term::Var("b".into());
    let extend = |value, target| Term::App {
        op: Op::ZeroExtend(target - 8),
        args: vec![value],
    };
    let product = app(Op::Mul, extend(a.clone(), width), extend(b.clone(), width));
    let left = Term::App {
        op: if signed_output {
            Op::SignExtend(output - width)
        } else {
            Op::ZeroExtend(output - width)
        },
        args: vec![product],
    };
    let right = app(Op::Mul, extend(a, output), extend(b, output));
    Query {
        variables: vec![("a".into(), Sort::Bits(8)), ("b".into(), Sort::Bits(8))],
        requires: vec![],
        goal: app(Op::Eq, left, right),
        architecture: 64,
    }
}

#[test]
fn overflowing_products_and_signed_views_of_unsigned_high_bits_are_preserved() {
    let full = simplify(&extended_product(16, 32, false)).unwrap();
    assert!(matches!(bare(&full.goal), Term::Bool(true)));
    let padded_signed = simplify(&extended_product(17, 32, true)).unwrap();
    assert!(matches!(bare(&padded_signed.goal), Term::Bool(true)));
    // 255*255 at16bits is65025, whose SIGNED extension is -511, not65025.
    let signed_high = simplify(&extended_product(16, 32, true)).unwrap();
    assert!(!matches!(bare(&signed_high.goal), Term::Bool(true)));
    let overflow = simplify(&extended_product(12, 32, false)).unwrap();
    assert!(!matches!(bare(&overflow.goal), Term::Bool(true)));
}

#[test]
fn truncation_and_division_arbitrary_values_are_not_erased() {
    let mut original = congruence(false, false, false, false, 8, 32);
    let Term::App { args, .. } = &mut original.goal else {
        unreachable!()
    };
    let mut consequence_term = bare(&args[1]).clone();
    let Term::App {
        op: Op::Eq,
        args: equality,
    } = &mut consequence_term
    else {
        panic!("expected a multiplication equality");
    };
    let left = equality[0].clone();
    equality[0] = Term::App {
        op: Op::ZeroExtend(56),
        args: vec![Term::App {
            op: Op::Extract { high: 7, low: 0 },
            args: vec![left],
        }],
    };
    args[1] = consequence_term;
    let changed = simplify(&original).unwrap();
    assert!(!matches!(consequence(&changed.goal), Term::Bool(true)));

    let zero = Term::Bits {
        value: IntLit {
            negative: false,
            magnitude: 0,
        },
        width: 8,
    };
    let arbitrary = Term::If {
        condition: Box::new(Term::Bool(true)),
        then_term: Box::new(Term::Var("a".into())),
        else_term: Box::new(zero.clone()),
    };
    let direct = Query {
        variables: vec![("a".into(), Sort::Bits(8))],
        requires: vec![],
        goal: app(Op::Eq, arbitrary, zero),
        architecture: 64,
    };
    assert!(simplify(&direct).is_none());
}

#[test]
fn malformed_queries_and_exhausted_work_fall_back_without_mutating_inputs() {
    let original = congruence(false, true, true, false, 8, 32);
    let retained = original.clone();
    assert!(transform(&original, &mut 0).is_none());
    assert_eq!(original, retained);
    let mut malformed = original;
    malformed.variables[0].1 = Sort::Bool;
    assert!(simplify(&malformed).is_none());
}
