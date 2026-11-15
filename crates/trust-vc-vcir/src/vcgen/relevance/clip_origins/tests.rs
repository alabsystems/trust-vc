use super::*;

fn n() -> Term {
    Term::var("n", Sort::Int)
}
fn clip(value: Term) -> Term {
    super::super::super::spec::clip(IntRange::U(8), value)
}
fn greater(a: Term, b: Term) -> Term {
    Term::Cmp(CmpOp::Lt, Box::new(b), Box::new(a))
}
fn predicate(value: Term) -> Term {
    Term::call("actual_predicate_shape", vec![value], Sort::Bool)
}
fn work(left: &mut usize, cost: usize) -> bool {
    match left.checked_sub(cost) {
        Some(next) => {
            *left = next;
            true
        }
        None => {
            *left = 0;
            false
        }
    }
}
fn tracked(terms: &[Term]) -> Vec<Formula<usize>> {
    let ranges = [IntRange::U(8)].into_iter().collect();
    let mut budget = 200_000;
    prepare(terms.iter().enumerate(), &ranges, &mut |cost| {
        work(&mut budget, cost)
    })
    .expect("admitted existing grant")
    .expect("consistent original formulas")
}
fn active_formula() -> Formula<usize> {
    tracked(&[greater(n(), Term::Int(255)), predicate(clip(n()))])
        .into_iter()
        .find(|f| f.origins.iter().any(|o| matches!(o.state, State::Active)))
        .expect("same actual source clip selected its fallback")
}

#[test]
fn observation_preserves_actual_local_split_and_propagation_results() {
    let c = clip(n());
    let samples = [
        vec![greater(n(), Term::Int(255)), predicate(c.clone())],
        vec![Term::eq(n(), Term::Int(300)), predicate(c.clone())],
        vec![Term::Or(vec![Term::Bool(true), predicate(c.clone())])],
        vec![Term::eq(c.clone(), c.clone())],
        vec![Term::And(vec![predicate(c.clone()), predicate(c.clone())])],
        vec![Term::Not(Box::new(Term::Or(vec![
            predicate(c.clone()),
            Term::Bool(false),
        ])))],
    ];
    for terms in samples {
        let mut baseline = Vec::new();
        for (tag, term) in terms.iter().enumerate() {
            let mut parts = Vec::new();
            split(Simp::local().go(term), &mut parts);
            baseline.extend(parts.into_iter().map(|part| (part, tag)));
        }
        let expected = propagate(baseline).expect("consistent baseline");
        let actual: Vec<_> = tracked(&terms)
            .into_iter()
            .map(|f| (f.term, f.tag))
            .collect();
        assert_eq!(
            actual, expected,
            "the observer does not change any rewritten query term"
        );
    }
}

#[test]
fn partial_condition_and_actual_operand_rewrites_keep_their_receipts() {
    let roots = [
        Term::Cmp(CmpOp::Le, Box::new(Term::Int(0)), Box::new(n())),
        predicate(clip(n())),
        greater(n(), Term::Int(255)),
    ];
    let partial = tracked(&roots);
    let origin = partial
        .iter()
        .flat_map(|f| &f.origins)
        .find(|o| matches!(o.state, State::Active))
        .expect("pending clip survived the first partial condition rewrite");
    assert_eq!(origin.source, clip(n()));
    assert_eq!(origin.source_operand, n());
    assert_eq!(origin.operand_image, n());
    let changed = tracked(&[Term::eq(n(), Term::Int(300)), predicate(clip(n()))]);
    let origin = changed
        .iter()
        .flat_map(|f| &f.origins)
        .find(|o| matches!(o.state, State::Active))
        .expect("same actual go rewrote the operand");
    assert_eq!(origin.source_operand, n());
    assert_eq!(origin.operand_image, Term::Int(300));
    assert_eq!(child(&origin.image, 0), Some(&Term::Int(300)));
}

#[test]
fn malformed_source_range_operand_image_or_path_never_becomes_a_site() {
    let original = active_formula();
    for corruption in 0..5 {
        let mut left = 200_000;
        let mut bad = Formula {
            term: original.term.clone(),
            tag: original.tag,
            origins: cloned_origins(&original.origins, &mut |cost| work(&mut left, cost)).unwrap(),
        };
        let o = bad
            .origins
            .iter_mut()
            .find(|o| matches!(o.state, State::Active))
            .unwrap();
        match corruption {
            0 => o.source = clip(Term::var("other_source_operand", Sort::Int)),
            1 => o.range = IntRange::U(16),
            2 => o.operand_image = Term::var("other_current_operand", Sort::Int),
            3 => {
                o.image = Term::call(
                    super::super::super::spec::clip_oob_name(IntRange::U(8)),
                    vec![Term::Int(99)],
                    Sort::Int,
                )
            }
            4 => o.path.push(usize::MAX),
            _ => unreachable!(),
        }
        assert!(bad.sites(&mut |cost| work(&mut left, cost)).is_err());
    }
}

#[test]
fn ambiguous_or_absorbed_images_are_conservatively_discarded() {
    let c = clip(n());
    let bare = Term::call(
        super::super::super::spec::clip_oob_name(IntRange::U(8)),
        vec![n()],
        Sort::Int,
    );
    for root in [
        Term::Or(vec![Term::Bool(true), predicate(c.clone())]),
        Term::eq(c.clone(), c.clone()),
        Term::And(vec![predicate(c.clone()), predicate(bare.clone())]),
    ] {
        let formulas = tracked(&[greater(n(), Term::Int(255)), root]);
        assert!(
            formulas
                .iter()
                .all(|f| f.origins.iter().all(|o| !matches!(o.state, State::Active))),
            "a surviving identical bare image cannot borrow a discarded occurrence"
        );
    }
}

#[test]
fn late_site_payload_and_unique_path_exhaustion_return_no_prefix_or_fresh_grant() {
    let formula = active_formula();
    let mut full = 200_000;
    let sites = formula.sites(&mut |cost| work(&mut full, cost)).unwrap();
    assert!(!sites.is_empty());
    let site_cost = 200_000 - full;
    assert!(site_cost > 20);
    let mut held = site_cost - 1;
    assert!(formula.sites(&mut |cost| work(&mut held, cost)).is_err());
    assert_eq!(
        held, 0,
        "last payload copy shares the caller's already-used grant"
    );
    let active = formula
        .origins
        .iter()
        .find(|o| matches!(o.state, State::Active))
        .unwrap();
    let mut full = 200_000;
    assert!(unique(&formula.term, &active.image, &mut |cost| work(
        &mut full, cost
    ))
    .unwrap()
    .is_some());
    let path_cost = 200_000 - full;
    assert!(path_cost > 20);
    let mut held = path_cost - 1;
    assert!(unique(&formula.term, &active.image, &mut |cost| work(
        &mut held, cost
    ))
    .is_err());
    assert_eq!(held, 0);
    let mut zero = 0;
    assert!(formula.sites(&mut |cost| work(&mut zero, cost)).is_err());
}

#[test]
fn an_equal_ite_rebuilt_from_a_discarded_clip_and_bare_branch_is_not_a_new_origin() {
    let source = clip(n());
    let Term::Ite(condition, _, fallback, _) = source.clone() else {
        unreachable!()
    };
    // Local ITE rewriting can recreate the canonical clip VALUE from the
    // outer expression, although its original clip occurrence was under
    // the in-range branch. Outside(n) later selects the separate bare row.
    let outer = Term::Ite(condition, Box::new(source), fallback, Sort::Int);
    let formulas = tracked(&[greater(n(), Term::Int(255)), predicate(outer)]);
    assert!(
        formulas.iter().all(|f| f.origins.is_empty()),
        "a rewritten shape or another bare branch cannot mint source lineage"
    );
}
