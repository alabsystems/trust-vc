//! Existing two-world semantics remain exact; no arithmetic is_member override.
use super::*;

#[test]
fn an_exact_arithmetic_member_never_overrides_the_actual_operation() {
    let add = Term::Arith(
        ArithOp::Add,
        Box::new(Term::var("x", Sort::Int)),
        Box::new(Term::Int(1)),
    );
    let node = Term::Cmp(CmpOp::Eq, Box::new(add.clone()), Box::new(Term::Int(0)));
    let mut budget = 10_000;
    assert!(!depends(
        &Problem {
            node: &node,
            members: vec![&add],
            sort: Sort::Int,
            facts: vec![],
            exact: true
        },
        &mut budget
    ));
    let mut budget = 10_000;
    assert!(depends(
        &Problem {
            node: &node,
            members: vec![&add],
            sort: Sort::Int,
            facts: vec![],
            exact: false
        },
        &mut budget
    ));
}

#[test]
fn nested_same_operation_points_use_the_existing_bounded_settlement() {
    let inner = Term::Arith(
        ArithOp::Add,
        Box::new(Term::var("x", Sort::Int)),
        Box::new(Term::Int(1)),
    );
    let outer = Term::Arith(ArithOp::Add, Box::new(inner), Box::new(Term::Int(2)));
    let node = Term::Cmp(CmpOp::Eq, Box::new(outer.clone()), Box::new(Term::Int(0)));
    let problem = Problem {
        node: &node,
        members: vec![&outer],
        sort: Sort::Int,
        facts: vec![],
        exact: false,
    };
    let search = Search::new(&problem, 100);
    assert!(
        search.nested,
        "arithmetic arguments also read the class operation; the pending/settle guard is required"
    );
    let mut budget = 100;
    let _ = depends(&problem, &mut budget);
    assert!(
        budget < 100,
        "the same finite witness grant funds the attempted settlement"
    );
}
