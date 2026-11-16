use super::*;

fn compare(a: &Term, b: &Term, budget: usize) -> R<bool> {
    let mut left = budget;
    equal(
        &mut |cost| match left.checked_sub(cost) {
            Some(next) => {
                left = next;
                true
            }
            None => false,
        },
        a,
        b,
    )
}

fn shapes() -> Vec<Term> {
    let mut terms = vec![Term::Bool(false), Term::Bool(true)];
    terms.extend([i128::MIN, -1, 0, 1, i128::MAX].map(Term::Int));
    for sort in [
        Sort::Bool,
        Sort::Int,
        Sort::Nominal(0),
        Sort::Nominal(u32::MAX),
        Sort::Poly,
        Sort::TypeId,
        Sort::Decoration,
    ] {
        for name in ["", "x", "y", "é", "λ"] {
            terms.push(Term::var(name, sort));
            for args in [
                vec![],
                vec![Term::Int(0)],
                vec![Term::Int(0), Term::Int(1)],
                vec![Term::Int(1), Term::Int(0)],
            ] {
                terms.push(Term::Call {
                    name: name.into(),
                    args,
                    sort,
                });
            }
        }
        terms.push(Term::Ite(
            Box::new(Term::Bool(true)),
            Box::new(Term::Int(0)),
            Box::new(Term::Int(1)),
            sort,
        ));
    }
    for x in [Term::Bool(true), Term::Int(-1), Term::var("x", Sort::Int)] {
        terms.push(Term::Not(Box::new(x.clone())));
        terms.push(Term::Neg(Box::new(x.clone())));
        for xs in [
            vec![],
            vec![x.clone()],
            vec![x.clone(), Term::Int(1)],
            vec![Term::Int(1), x.clone()],
        ] {
            terms.push(Term::And(xs.clone()));
            terms.push(Term::Or(xs));
        }
        terms.push(Term::Implies(
            Box::new(x.clone()),
            Box::new(Term::Bool(false)),
        ));
        for op in [CmpOp::Eq, CmpOp::Lt, CmpOp::Le] {
            terms.push(Term::Cmp(op, Box::new(x.clone()), Box::new(Term::Int(1))));
        }
        for op in [
            ArithOp::Add,
            ArithOp::Sub,
            ArithOp::Mul,
            ArithOp::Div,
            ArithOp::Mod,
        ] {
            terms.push(Term::Arith(op, Box::new(x.clone()), Box::new(Term::Int(1))));
        }
    }
    terms
}

#[test]
fn all_term_fields_match_derived_equality() {
    let terms = shapes();
    for a in &terms {
        for b in &terms {
            assert_eq!(compare(a, b, 200_000).unwrap(), a == b, "{a:?} / {b:?}");
        }
    }
}

#[test]
fn refused_payments_are_errors_and_constructor_mismatch_needs_no_census() {
    let large = Term::And(vec![Term::var("long name", Sort::Int); 10_000]);
    assert!(compare(&large, &Term::Int(0), 1).is_err());
    assert_eq!(compare(&large, &Term::Int(0), 2).unwrap(), false);
    assert!(compare(&Term::Int(1), &Term::Int(1), 3).is_err());
    assert_eq!(compare(&Term::Int(1), &Term::Int(1), 4).unwrap(), true);
    assert!(compare(&large, &large, 200_000).is_err());
}

#[test]
fn names_and_worklist_growth_are_paid_before_comparison() {
    let name = "λ".repeat(1_000);
    let a = Term::var(name, Sort::Int);
    assert!(compare(&a, &a, 4_005).is_err());
    assert_eq!(compare(&a, &a, 4_006).unwrap(), true);
    let b = Term::Not(Box::new(Term::Bool(true)));
    assert!(compare(&b, &b, 7).is_err());
    assert_eq!(compare(&b, &b, 12).unwrap(), true);
}

#[test]
fn nested_comparison_uses_borrowed_worklist_without_recursion() {
    let mut a = Term::Bool(true);
    let mut b = Term::Bool(true);
    for _ in 0..2_000 {
        a = Term::Not(Box::new(a));
        b = Term::Not(Box::new(b));
    }
    assert_eq!(compare(&a, &b, 20_000).unwrap(), true);
    // Recursive destruction is unrelated to the equality traversal.
    std::mem::forget(a);
    std::mem::forget(b);
}

#[test]
fn exact_equality_keeps_duplicate_occurrences_ambiguous() {
    let image = Term::call("clip_u8_oob", vec![Term::var("n", Sort::Int)], Sort::Int);
    let duplicate = Term::And(vec![image.clone(), image.clone()]);
    let unique = Term::And(vec![Term::Bool(true), image.clone()]);
    let mut budget = 200_000usize;
    let mut pay = |cost| match budget.checked_sub(cost) {
        Some(next) => {
            budget = next;
            true
        }
        None => false,
    };
    assert_eq!(
        super::super::unique(&duplicate, &image, &mut pay).unwrap(),
        None
    );
    assert_eq!(
        super::super::unique(&unique, &image, &mut pay).unwrap(),
        Some(vec![1])
    );
    assert!(super::super::unique(&unique, &image, &mut |_| false).is_err());
}
