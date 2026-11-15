//! Source-only controls intended as a child of vcgen::trigger_pattern.
//! They exercise descriptors and whole-term checks, not registry authority or
//! an SMT verdict. All tests are prepared and unrun.

use super::super::{
    spec,
    term::{ArithOp, Sort, Term},
};
use super::{Head, Pattern, Template};
use crate::IntRange;
use std::collections::HashMap;

fn x() -> Term {
    Term::var("source_x", Sort::Int)
}

fn admitted(pattern: &Pattern) -> bool {
    let mut remaining = 100_000usize;
    pattern.valid_head(&mut |cost| {
        if cost > remaining {
            return false;
        }
        remaining -= cost;
        true
    })
}

fn fallback(term: &Term, range: IntRange) -> Option<Term> {
    spec::clip_fallback(term, range, &mut |_| true).cloned()
}

#[test]
fn canonical_clip_token_retains_the_whole_current_abi() {
    for range in [IntRange::U(8), IntRange::I(8), IntRange::Nat] {
        let token = spec::clip_pattern(range, x()).expect("actual supported clip producer");
        let pattern = Pattern::clipped(token);
        assert_eq!(pattern.head(), Head::Clip(range));
        assert_eq!(pattern.term(), &spec::clip(range, x()));
        assert!(admitted(&pattern));
        assert_eq!(
            fallback(pattern.term(), range),
            Some(Term::call(spec::clip_oob_name(range), vec![x()], Sort::Int))
        );
    }
}

#[test]
fn same_fallback_name_does_not_erase_the_range_identity() {
    let canonical = spec::clip(IntRange::U(8), x());
    assert!(fallback(&canonical, IntRange::U(8)).is_some());
    for wrong in [IntRange::U(16), IntRange::I(8), IntRange::Nat] {
        assert!(fallback(&canonical, wrong).is_none());
    }
    for unsupported in [
        IntRange::Int,
        IntRange::USize,
        IntRange::ISize,
        IntRange::Char,
        IntRange::U(7),
    ] {
        assert!(spec::clip_pattern(unsupported, x()).is_none());
        assert!(fallback(&canonical, unsupported).is_none());
    }
}

#[test]
fn whole_clip_requires_the_actual_condition_and_both_branches() {
    let canonical = spec::clip(IntRange::U(8), x());
    let Term::Ite(condition, value, chosen, sort) = canonical else {
        panic!("symbolic clipping must retain its full conditional");
    };
    let cases = [
        Term::Ite(
            Box::new(Term::Bool(true)),
            value.clone(),
            chosen.clone(),
            sort,
        ),
        Term::Ite(
            condition.clone(),
            Box::new(Term::Int(1)),
            chosen.clone(),
            sort,
        ),
        Term::Ite(
            condition.clone(),
            value.clone(),
            Box::new(Term::Int(0)),
            sort,
        ),
        Term::Ite(condition.clone(), chosen.clone(), value.clone(), sort),
        Term::Ite(condition.clone(), value.clone(), chosen.clone(), Sort::Bool),
    ];
    for malformed in cases {
        assert!(fallback(&malformed, IntRange::U(8)).is_none());
    }
}

#[test]
fn fallback_signature_and_argument_must_match_the_value_branch() {
    let Term::Ite(condition, value, _, sort) = spec::clip(IntRange::U(8), x()) else {
        panic!("symbolic clipping must retain its full conditional");
    };
    let wrong = [
        Term::call(spec::clip_oob_name(IntRange::U(16)), vec![x()], Sort::Int),
        Term::call(spec::clip_oob_name(IntRange::U(8)), vec![], Sort::Int),
        Term::call(
            spec::clip_oob_name(IntRange::U(8)),
            vec![x(), x()],
            Sort::Int,
        ),
        Term::call(
            spec::clip_oob_name(IntRange::U(8)),
            vec![Term::var("other", Sort::Int)],
            Sort::Int,
        ),
        Term::call(
            spec::clip_oob_name(IntRange::U(8)),
            vec![Term::Bool(false)],
            Sort::Int,
        ),
        Term::call(spec::clip_oob_name(IntRange::U(8)), vec![x()], Sort::Bool),
    ];
    for chosen in wrong {
        let malformed = Term::Ite(condition.clone(), value.clone(), Box::new(chosen), sort);
        assert!(fallback(&malformed, IntRange::U(8)).is_none());
    }
}

#[test]
fn raw_ite_never_acquires_the_private_clip_head() {
    let canonical = spec::clip(IntRange::U(8), x());
    assert!(fallback(&canonical, IntRange::U(8)).is_some());
    assert_eq!(Template::root(&canonical), None);
    assert!(Pattern::application(canonical).is_none());
    let ordinary = Term::Ite(
        Box::new(Term::var("condition", Sort::Bool)),
        Box::new(x()),
        Box::new(Term::Int(7)),
        Sort::Int,
    );
    assert_eq!(Template::root(&ordinary), None);
    assert!(Pattern::application(ordinary).is_none());
}

#[test]
fn a_bare_oob_call_is_not_the_full_clip_carrier() {
    let proxy = Term::call(spec::clip_oob_name(IntRange::U(8)), vec![x()], Sort::Int);
    assert!(fallback(&proxy, IntRange::U(8)).is_none());
    let plain_call = Pattern::application(proxy).expect("ordinary typed calls remain calls");
    assert_eq!(plain_call.head(), Head::Call);
    assert_ne!(plain_call.head(), Head::Clip(IntRange::U(8)));
}

#[test]
fn only_int_operands_enter_arithmetic_and_clip_heads() {
    for bad in [Term::Bool(true), Term::var("carrier", Sort::Nominal(2))] {
        assert!(spec::clip_pattern(IntRange::U(8), bad.clone()).is_none());
        let arithmetic = Term::Arith(ArithOp::Add, Box::new(bad), Box::new(Term::Int(1)));
        assert!(Pattern::application(arithmetic).is_none());
    }
    let arithmetic = Term::Arith(ArithOp::Add, Box::new(x()), Box::new(Term::Int(1)));
    let pattern = Pattern::application(arithmetic).expect("actual integer arithmetic head");
    assert_eq!(pattern.head(), Head::Arithmetic(ArithOp::Add));
    assert!(admitted(&pattern));
}

#[test]
fn substitution_preserves_clip_structure_and_rechecks_current_sorts() {
    let pattern = Pattern::clipped(spec::clip_pattern(IntRange::U(8), x()).unwrap());
    let current = Term::Arith(
        ArithOp::Add,
        Box::new(Term::var("current", Sort::Int)),
        Box::new(Term::Int(3)),
    );
    let substituted = pattern.substitute(&HashMap::from([("source_x", current.clone())]));
    assert_eq!(substituted.term(), &spec::clip(IntRange::U(8), current));
    assert!(admitted(&substituted));
    let malformed = pattern.substitute(&HashMap::from([("source_x", Term::Bool(false))]));
    assert!(!admitted(&malformed));
}

#[test]
fn held_or_exhausted_existing_budget_refuses_clip_validation() {
    let pattern = Pattern::clipped(spec::clip_pattern(IntRange::U(8), x()).unwrap());
    let mut attempts = 0;
    assert!(!pattern.valid_head(&mut |_| {
        attempts += 1;
        false
    }));
    assert_eq!(
        attempts, 1,
        "held owner refuses before the deeper whole-term work"
    );
    let mut remaining = 2usize;
    assert!(!pattern.valid_head(&mut |cost| {
        if cost > remaining {
            return false;
        }
        remaining -= cost;
        true
    }));
    assert!(
        admitted(&pattern),
        "independent sufficient original budget admits the same source token"
    );
}
