//! Actual AY controls for the typed multiplication congruence preprocessing.
use super::*;

fn app(op: Op, a: Term, b: Term) -> Term {
    Term::App {
        op,
        args: vec![a, b],
    }
}
fn input(name: &str, bits: u32, signed: bool) -> Integer {
    Integer::from_bits(Term::Var(name.into()), bits, signed).unwrap()
}
fn equated_product(
    signed_a: bool,
    signed_b: bool,
    left_sum: bool,
    right_sum: bool,
    false_twin: bool,
    disjunctive: bool,
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
        if disjunctive { Op::Or } else { Op::And },
        a.clone().compare(x.clone(), Comparison::Eq).unwrap(),
        b.clone().compare(y.clone(), Comparison::Eq).unwrap(),
    );
    let left = a.arithmetic(b, Arithmetic::Mul).unwrap();
    let mut right = x.arithmetic(y, Arithmetic::Mul).unwrap();
    if false_twin {
        right = right.arithmetic(integer(1), Arithmetic::Add).unwrap();
    }
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
        goal: app(
            Op::Implies,
            premise,
            left.compare(right, Comparison::Eq).unwrap(),
        ),
        architecture: 64,
    }
}

#[test]
fn native_typed_bv_equated_products_cover_original_twelve_sign_and_sum_shapes() {
    for architecture in [32, 64] {
        for signed_a in [false, true] {
            for signed_b in [false, true] {
                for (left_sum, right_sum) in [(false, false), (true, false), (false, true)] {
                    let mut question = equated_product(
                        signed_a, signed_b, left_sum, right_sum, false, false, 8, 32,
                    );
                    question.architecture = architecture;
                    proved(question);
                }
            }
        }
    }
}

#[test]
fn native_typed_bv_wrong_product_and_nondominating_equations_have_real_models() {
    // Small widths make the false twins decisive independently of any solver
    // performance improvement. Refuted still requires AY's strict model gate.
    refuted(equated_product(false, true, true, false, true, false, 2, 8));
    refuted(equated_product(false, true, true, false, false, true, 2, 8));
}

fn extension_identity(width: u32, signed_output: bool) -> Query {
    let a = Term::Var("a".into());
    let b = Term::Var("b".into());
    let extend = |value, target| Term::App {
        op: Op::ZeroExtend(target - 8),
        args: vec![value],
    };
    let product = app(Op::Mul, extend(a.clone(), width), extend(b.clone(), width));
    let left = Term::App {
        op: if signed_output {
            Op::SignExtend(32 - width)
        } else {
            Op::ZeroExtend(32 - width)
        },
        args: vec![product],
    };
    let right = app(Op::Mul, extend(a, 32), extend(b, 32));
    Query {
        variables: vec![("a".into(), Sort::Bits(8)), ("b".into(), Sort::Bits(8))],
        requires: vec![],
        goal: app(Op::Eq, left, right),
        architecture: 64,
    }
}

#[test]
fn native_typed_bv_product_extension_rejects_overflow_and_wrong_sign_views() {
    proved(extension_identity(16, false));
    proved(extension_identity(17, true));
    // At a=b=255, sext32(bvmul16(a,b)) is -511, unlike the exact65025.
    refuted(extension_identity(16, true));
    refuted(extension_identity(12, false));
}
