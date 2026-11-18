use super::*;

fn binary(op: Op, a: Term, b: Term) -> Term {
    Term::App {
        op,
        args: vec![a, b],
    }
}

fn input(name: &str, bits: u32, signed: bool) -> Integer {
    Integer::from_bits(Term::Var(name.into()), bits, signed).unwrap()
}

fn negation(term: Term) -> Term {
    Term::App {
        op: Op::Not,
        args: vec![term],
    }
}

fn conclusion(mut term: &Term) -> &Term {
    loop {
        match term {
            Term::Shared(inner) => term = inner,
            Term::App {
                op: Op::Implies,
                args,
            } => term = &args[1],
            _ => return term,
        }
    }
}

fn equated_euclidean(
    signed: (bool, bool),
    sum: (bool, bool),
    width: (u32, u32),
    remainder: bool,
) -> (Query, Term) {
    let (small, large) = width;
    let a = input("a", small, signed.0);
    let c = input("c", small, signed.1);
    let numerator = if sum.0 {
        a.arithmetic(input("b", small, signed.0), Arithmetic::Add)
            .unwrap()
    } else {
        a
    };
    let denominator = if sum.1 {
        c.arithmetic(input("d", small, signed.1), Arithmetic::Add)
            .unwrap()
    } else {
        c
    };
    let x = input("x", large, false);
    let y = input("y", large, false);
    let premise = binary(
        Op::And,
        numerator
            .clone()
            .compare(x.clone(), Comparison::Eq)
            .unwrap(),
        denominator
            .clone()
            .compare(y.clone(), Comparison::Eq)
            .unwrap(),
    );
    let nonzero = negation(y.clone().compare(integer(0), Comparison::Eq).unwrap());
    let left = numerator
        .euclidean(denominator, remainder, Term::Var("zero_left".into()))
        .unwrap();
    let right = x
        .euclidean(y, remainder, Term::Var("zero_right".into()))
        .unwrap();
    let mut variables = ["a", "b", "c", "d"]
        .map(|name| (name.into(), Sort::Bits(small)))
        .to_vec();
    variables.extend([
        ("x".into(), Sort::Bits(large)),
        ("y".into(), Sort::Bits(large)),
        ("zero_left".into(), Sort::Bits(left.bits())),
        ("zero_right".into(), Sort::Bits(right.bits())),
    ]);
    (
        Query {
            variables,
            requires: vec![],
            goal: binary(
                Op::Implies,
                premise,
                left.compare(right, Comparison::Eq).unwrap(),
            ),
            architecture: 64,
        },
        nonzero,
    )
}

#[test]
fn native_euclidean_congruence_covers_original_signed_and_unsigned_operands() {
    for architecture in [32, 64] {
        for remainder in [false, true] {
            for signed_a in [false, true] {
                for signed_b in [false, true] {
                    for sum in [(false, false), (true, false), (false, true)] {
                        let (mut query, nonzero) =
                            equated_euclidean((signed_a, signed_b), sum, (8, 32), remainder);
                        query.goal = binary(Op::Implies, nonzero, query.goal);
                        query.architecture = architecture;
                        let simplified = trust_vc_bitvector::congruence::simplify(&query)
                            .expect("valid scoped Euclidean equality");
                        assert_eq!(conclusion(&simplified.goal), &Term::Bool(true));
                        proved(query);
                    }
                }
            }
        }
    }
}

#[test]
fn native_euclidean_congruence_preserves_a_narrow_signed_result_view() {
    let a = input("a", 3, true);
    let x = input("x", 5, true);
    let y = input("y", 3, false);
    let requires = vec![
        a.clone().compare(x.clone(), Comparison::Eq).unwrap(),
        y.clone().compare(integer(2), Comparison::Eq).unwrap(),
        negation(y.clone().compare(integer(0), Comparison::Eq).unwrap()),
    ];
    let left = a
        .euclidean(y.clone(), false, Term::Var("zero_left".into()))
        .unwrap();
    let right = x
        .euclidean(y, false, Term::Var("zero_right".into()))
        .unwrap();
    let (small, wide) = (left.bits(), right.bits());
    let goal = binary(
        Op::Eq,
        Term::App {
            op: Op::ZeroExtend(wide - small),
            args: vec![left.into_term()],
        },
        right.into_term(),
    );
    let query = Query {
        variables: vec![
            ("a".into(), Sort::Bits(3)),
            ("x".into(), Sort::Bits(5)),
            ("y".into(), Sort::Bits(3)),
            ("zero_left".into(), Sort::Bits(small)),
            ("zero_right".into(), Sort::Bits(wide)),
        ],
        requires,
        goal,
        architecture: 64,
    };
    // At a=x=-3 and y=2, zero-extending the narrow quotient differs from
    // the wider two's-complement quotient for the same integer result.
    refuted(query);
}

#[test]
fn native_euclidean_congruence_preserves_independent_zero_results() {
    for remainder in [false, true] {
        let (query, nonzero) = equated_euclidean((true, false), (true, false), (2, 4), remainder);
        refuted(query.clone());
        let mut disjunctive = query.clone();
        disjunctive.requires = vec![binary(Op::Or, nonzero.clone(), Term::Bool(true))];
        refuted(disjunctive);
        let mut explicit = query;
        explicit.requires = vec![nonzero];
        proved(explicit);
    }
}

#[test]
fn native_euclidean_congruence_handles_negative_values_and_signed_minimum() {
    for (numerator, denominator, quotient, residue) in [(-3, -2, 2, 1), (-128, -1, 128, 0)] {
        for (remainder, expected) in [(false, quotient), (true, residue)] {
            let a = input("a", 8, true);
            let b = input("b", 8, true);
            let x = input("x", 16, true);
            let y = input("y", 16, true);
            let requires = vec![
                a.clone().compare(x.clone(), Comparison::Eq).unwrap(),
                b.clone().compare(y.clone(), Comparison::Eq).unwrap(),
                x.clone()
                    .compare(integer(numerator), Comparison::Eq)
                    .unwrap(),
                y.clone()
                    .compare(integer(denominator), Comparison::Eq)
                    .unwrap(),
                negation(y.clone().compare(integer(0), Comparison::Eq).unwrap()),
            ];
            let narrow = a
                .euclidean(b, remainder, Term::Var("zero_left".into()))
                .unwrap();
            let wide = x
                .euclidean(y, remainder, Term::Var("zero_right".into()))
                .unwrap();
            let variables = vec![
                ("a".into(), Sort::Bits(8)),
                ("b".into(), Sort::Bits(8)),
                ("x".into(), Sort::Bits(16)),
                ("y".into(), Sort::Bits(16)),
                ("zero_left".into(), Sort::Bits(narrow.bits())),
                ("zero_right".into(), Sort::Bits(wide.bits())),
            ];
            let equality = narrow.clone().compare(wide, Comparison::Eq).unwrap();
            let value = narrow.compare(integer(expected), Comparison::Eq).unwrap();
            let mut question = Query {
                variables,
                requires,
                goal: equality.clone(),
                architecture: 64,
            };
            let simplified = trust_vc_bitvector::congruence::simplify(&question).unwrap();
            assert_eq!(conclusion(&simplified.goal), &Term::Bool(true));
            question.goal = binary(Op::And, equality, value);
            proved(question);
        }
    }
}
