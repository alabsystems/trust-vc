//! Callback controls test the real scheduling/admission kernel, not a mock
//! reference implementation. They claim no native SAT installation/verdict.
use super::*;
use crate::bitvector;
use crate::solve::{UnknownCategory, Verdict};

fn leaf(width: u32, goal: bool) -> Query {
    Query {
        architectures: None,
        bitvector: Some(vec![bitvector::Query {
            variables: vec![],
            requires: vec![],
            goal: bitvector::Term::Bool(goal),
            architecture: width,
        }]),
        nominal_types: vec![],
        symbols: vec![],
        functions: vec![],
        definitions: vec![],
        hypotheses: vec![],
        goal: Term::Bool(false),
    }
}
fn batch(first: bool, second: bool) -> Query {
    Query {
        architectures: Some(vec![(32, leaf(32, first)), (64, leaf(64, second))]),
        bitvector: None,
        nominal_types: vec![],
        symbols: vec![],
        functions: vec![],
        definitions: vec![],
        hypotheses: vec![],
        goal: Term::Bool(false),
    }
}
fn literal_callback(query: &Query, _: &str, _: &Limits) -> DetailedVerdict {
    let case = &query.bitvector.as_ref().unwrap()[0];
    DetailedVerdict::at(
        if case.goal == bitvector::Term::Bool(true) {
            Verdict::Proved {
                used_hypotheses: None,
            }
        } else {
            Verdict::Refuted { model: vec![] }
        },
        case.architecture,
    )
}
#[test]
fn crossed_failures_follow_real_execution32_then64_not_clause_major() {
    let a = batch(true, false);
    let b = batch(false, true);
    let out = check_with(
        &[(&a, "earlier"), (&b, "later")],
        &Limits::default(),
        literal_callback,
    )
    .unwrap();
    assert_eq!(
        out.iter()
            .map(|(i, r)| (*i, r.refuted_architecture))
            .collect::<Vec<_>>(),
        [(0, None), (1, Some(32)), (0, Some(64)), (1, None)]
    );
}
#[test]
fn all_refutations_retain_both_ordered_case_events_with_original_indices() {
    let a = batch(false, false);
    let b = batch(false, false);
    let out = check_with(
        &[(&a, "a"), (&b, "b")],
        &Limits::default(),
        literal_callback,
    )
    .unwrap();
    assert_eq!(
        out.iter()
            .map(|(i, r)| (*i, r.refuted_architecture))
            .collect::<Vec<_>>(),
        [(0, Some(32)), (1, Some(32)), (0, Some(64)), (1, Some(64))]
    );
}
#[test]
fn later_malformed_architecture_prevents_every_callback_even_after_true_early_goal() {
    let early = batch(true, true);
    let mut late = batch(false, false);
    late.architectures.as_mut().unwrap()[1]
        .1
        .bitvector
        .as_mut()
        .unwrap()[0]
        .goal = bitvector::Term::Var("missing".into());
    let mut calls = 0;
    assert!(check_with(
        &[(&early, "early"), (&late, "late")],
        &Limits::default(),
        |q, l, c| {
            calls += 1;
            literal_callback(q, l, c)
        }
    )
    .is_err());
    assert_eq!(calls, 0);
}
#[test]
fn unknown_and_error_remain_refusals_without_width_or_promotion() {
    let a = batch(true, true);
    let out = check_with(&[(&a, "a")], &Limits::default(), |q, _, _| {
        let width = q.bitvector.as_ref().unwrap()[0].architecture;
        DetailedVerdict::at(
            if width == 32 {
                Verdict::Unknown {
                    reason: "held original limit".into(),
                    category: UnknownCategory::Timeout,
                }
            } else {
                Verdict::Error {
                    message: "original native error".into(),
                }
            },
            width,
        )
    })
    .unwrap();
    assert_eq!(out.len(), 2);
    assert!(matches!(
        &out[0].1.verdict,
        Verdict::Unknown {
            category: UnknownCategory::Timeout,
            ..
        }
    ));
    assert!(matches!(&out[1].1.verdict, Verdict::Error { .. }));
    assert!(out.iter().all(|(_, r)| r.refuted_architecture.is_none()));
}
#[test]
fn later_proof_does_not_replace_an_unknown_case() {
    let a = batch(true, true);
    let out = check_with(&[(&a, "a")], &Limits::default(), |q, l, c| {
        if q.bitvector.as_ref().unwrap()[0].architecture == 32 {
            DetailedVerdict::plain(Verdict::Unknown {
                reason: "unknown".into(),
                category: UnknownCategory::SolverUnknown,
            })
        } else {
            literal_callback(q, l, c)
        }
    })
    .unwrap();
    assert!(matches!(&out[0].1.verdict, Verdict::Unknown { .. }));
    assert!(matches!(&out[1].1.verdict, Verdict::Proved { .. }));
}
#[test]
fn original_limit_object_and_width_qualified_label_reach_each_operation() {
    let a = batch(true, true);
    let limits = Limits::default();
    let address = &limits as *const Limits;
    let mut labels = vec![];
    check_with(&[(&a, "source")], &limits, |q, l, c| {
        assert_eq!(c as *const Limits, address);
        labels.push(l.to_owned());
        literal_callback(q, l, c)
    })
    .unwrap();
    assert_eq!(labels, ["source_arch32", "source_arch64"]);
}
#[test]
fn incompatible_case_inventories_are_rejected_before_solving() {
    let a = batch(true, true);
    let b = leaf(64, false);
    let mut calls = 0;
    assert!(
        check_with(&[(&a, "a"), (&b, "b")], &Limits::default(), |q, l, c| {
            calls += 1;
            literal_callback(q, l, c)
        })
        .is_err()
    );
    assert_eq!(calls, 0);
}
#[test]
fn arbitrary_scalar_false_does_not_gain_bv_group_authority() {
    let mut a = batch(true, true);
    let child = &mut a.architectures.as_mut().unwrap()[1].1;
    child.bitvector = None;
    child.goal = Term::Bool(false);
    assert!(check_with(&[(&a, "a")], &Limits::default(), literal_callback).is_err());
}
#[test]
fn native_group_api_returns_real_refuting_widths_and_keeps_all_events() {
    let a = batch(true, false);
    let b = batch(false, true);
    let out =
        check_bitvector_group(&[(&a, "native_a"), (&b, "native_b")], &Limits::default()).unwrap();
    assert_eq!(
        out.iter()
            .filter_map(|(i, r)| r.refuted_architecture.map(|w| (*i, w)))
            .collect::<Vec<_>>(),
        [(1, 32), (0, 64)]
    );
}

#[test]
fn a_true_placeholder_cannot_replace_a_missing_isolated_obligation() {
    let mut a = batch(true, true);
    let child = &mut a.architectures.as_mut().unwrap()[1].1;
    child.bitvector = None;
    child.goal = Term::Bool(true);
    let mut calls = 0;
    assert!(check_with(&[(&a, "a")], &Limits::default(), |q, l, c| {
        calls += 1;
        literal_callback(q, l, c)
    })
    .is_err());
    assert_eq!(calls, 0);
}
