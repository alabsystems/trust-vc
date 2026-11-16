//! External source-only controls over the real Analysis::seeds/Simp path.
//! No origin receipt, source capability, solver or publication token is built here.
use super::super::spec;
use super::*;
use crate::IntRange;

fn n() -> Term {
    Term::var("origin_n", Sort::Int)
}
fn m() -> Term {
    Term::var("origin_m", Sort::Int)
}
fn g() -> Term {
    Term::var("origin_g", Sort::Bool)
}
fn clipped(value: Term) -> Term {
    spec::clip(IntRange::U(8), value)
}
fn oob(range: IntRange, value: Term) -> Term {
    Term::call(spec::clip_oob_name(range), vec![value], Sort::Int)
}
fn outside(value: Term) -> Term {
    Term::lt(Term::Int(255), value)
}
fn positive(value: Term) -> Term {
    Term::lt(Term::Int(0), value)
}
fn role(name: &str) -> CallRole {
    if [IntRange::U(8), IntRange::U(16)]
        .iter()
        .any(|range| name == spec::clip_oob_name(*range))
    {
        CallRole::Collect
    } else {
        CallRole::Other
    }
}
fn ranges() -> HashSet<IntRange> {
    [IntRange::U(8)].into_iter().collect()
}
fn placed(terms: Vec<Term>) -> Vec<(Term, Position)> {
    terms
        .into_iter()
        .map(|term| (term, Position::default()))
        .collect()
}
fn resolved(analysis: Analysis<'_>, found: Conds) -> Vec<(Term, Term)> {
    let (calls, conditions): (Vec<_>, Vec<_>) = found.into_items().into_iter().unzip();
    let result = analysis.namer.resolve_each(conditions, 4096);
    assert!(
        result.symbols.is_empty() && result.definitions.is_empty(),
        "small fixture conditions must expand completely, not hide a gate behind a fresh symbol"
    );
    calls.into_iter().zip(result.facts).collect()
}
fn items(hypotheses: &[(Term, Position)]) -> Vec<(Term, Term)> {
    let defs = HashMap::new();
    let requested = ranges();
    let mut analysis = Analysis::new(&role, &defs, 200_000).with_clip_triggers(&requested);
    let found = analysis
        .seeds(hypotheses, &(Term::Bool(false), Position::default()))
        .expect("small unchanged-budget relevance fixture");
    resolved(analysis, found)
}
fn no_clip(found: &[(Term, Term)]) {
    assert!(
        !found.iter().any(|(term, _)| matches!(term, Term::Ite(..))),
        "a bare or discarded image must not mint a whole-clip candidate"
    );
}
fn condition<'a>(found: &'a [(Term, Term)], wanted: &Term) -> Option<&'a Term> {
    found
        .iter()
        .find_map(|(term, guard)| (term == wanted).then_some(guard))
}
fn under_gate(guard: &Term, enabled: bool) -> Term {
    // A concrete interpretation satisfying outside(n) and positive(oob(n)).
    // Actual production EGraph/Simp evaluates the resulting ordinary condition.
    let mut graph = EGraph::default();
    graph.assert(&Term::eq(n(), Term::Int(256)));
    graph.assert(&if enabled { g() } else { g().not() });
    graph.assert(&Term::eq(oob(IntRange::U(8), n()), Term::Int(7)));
    Simp::with(&mut graph).go(guard)
}

#[test]
fn cross_formula_outside_fact_retains_the_genuine_whole_clip_seed() {
    let source = clipped(n());
    for hypotheses in [
        placed(vec![outside(n()), positive(source.clone())]),
        placed(vec![positive(source.clone()), outside(n())]),
    ] {
        let found = items(&hypotheses);
        let guard =
            condition(&found, &source).expect("same actual canonical clip must survive as a seed");
        assert_eq!(under_gate(guard, false), Term::Bool(true));
    }
    // The unchanged quant_arithmetic_tests remain the independent P(n),
    // positive-query and false-query integration assertions.
}

#[test]
fn bare_fallback_in_a_fresh_query_never_acquires_clip_origin() {
    let source = clipped(n());
    assert!(condition(
        &items(&placed(vec![outside(n()), positive(source.clone())])),
        &source
    )
    .is_some());
    let bare = oob(IntRange::U(8), n());
    let fresh = items(&placed(vec![outside(n()), positive(bare.clone())]));
    assert!(
        condition(&fresh, &bare).is_some(),
        "ordinary call material remains observable"
    );
    no_clip(&fresh);
}

#[test]
fn absorbed_equal_and_discarded_clip_origins_do_not_lend_to_another_root() {
    let source = clipped(n());
    let predicate = positive(source.clone());
    let dead = [
        Term::Or(vec![Term::Bool(true), predicate.clone()]),
        Term::Ite(
            Box::new(Term::Bool(false)),
            Box::new(predicate.clone()),
            Box::new(Term::Bool(true)),
            Sort::Bool,
        ),
        Term::Cmp(CmpOp::Eq, Box::new(source.clone()), Box::new(source)),
        Term::Or(vec![predicate.clone(), predicate.not()]),
    ];
    let bare = oob(IntRange::U(8), n());
    for discarded in dead {
        let found = items(&placed(vec![
            outside(n()),
            discarded,
            positive(bare.clone()),
        ]));
        assert!(condition(&found, &bare).is_some());
        no_clip(&found);
    }
}

#[test]
fn split_conjunct_position_tags_cannot_share_discarded_origins() {
    let bare = oob(IntRange::U(8), n());
    let same_input = Term::And(vec![
        Term::Or(vec![Term::Bool(true), positive(clipped(n()))]),
        positive(bare.clone()),
    ]);
    let found = items(&placed(vec![outside(n()), same_input]));
    assert!(condition(&found, &bare).is_some());
    no_clip(&found);
}

#[test]
fn a_final_class_literal_drop_does_not_authorize_an_identical_bare_image() {
    let bare = oob(IntRange::U(8), n());
    // Prefix fact makes the whole third predicate true through class_lit,
    // after its own clip has selected the fallback. The prefix stays live.
    let found = items(&placed(vec![
        outside(n()),
        positive(bare.clone()),
        positive(clipped(n())),
    ]));
    assert!(condition(&found, &bare).is_some());
    no_clip(&found);
}

#[test]
fn discarded_duplicate_after_rewrite_cannot_use_the_kept_bare_occurrence() {
    let bare = oob(IntRange::U(8), n());
    let both = Term::And(vec![positive(bare.clone()), positive(clipped(n()))]);
    let found = items(&placed(vec![outside(n()), both]));
    assert!(condition(&found, &bare).is_some());
    no_clip(&found);
}

#[test]
fn an_opposite_branch_bare_image_cannot_or_away_the_clip_occurrence_gate() {
    let source = clipped(n());
    let bare = oob(IntRange::U(8), n());
    let formula = Term::Or(vec![
        Term::And(vec![g(), positive(source.clone())]),
        Term::And(vec![g().not(), positive(bare.clone())]),
    ]);
    let found = items(&placed(vec![outside(n()), formula]));
    assert!(
        condition(&found, &bare).is_some(),
        "the actual fallback still affects this formula"
    );
    // Duplicate images may be conservatively omitted. If retained, their
    // origin condition must not borrow the opposite branch's bare call.
    if let Some(guard) = condition(&found, &source) {
        assert_eq!(under_gate(guard, false), Term::Bool(false));
    }
}

#[test]
fn a_unique_conditional_clip_keeps_its_own_live_branch_and_position_gate() {
    let source = clipped(n());
    let guarded = Term::Or(vec![g().not(), positive(source.clone())]);
    let found = items(&placed(vec![outside(n()), guarded]));
    let guard = condition(&found, &source).expect("unique live conditional occurrence");
    assert_eq!(under_gate(guard, false), Term::Bool(false));
    assert_eq!(under_gate(guard, true), Term::Bool(true));

    let hypotheses = vec![
        (outside(n()), Position::default()),
        (
            positive(source.clone()),
            Position {
                late: true,
                gate: Some(g()),
            },
        ),
    ];
    let found = items(&hypotheses);
    let guard = condition(&found, &source).expect("late position still retains its genuine gate");
    assert_eq!(under_gate(guard, false), Term::Bool(false));
    assert_eq!(under_gate(guard, true), Term::Bool(true));

    let hypotheses = vec![
        (outside(n()), Position::default()),
        (
            positive(source),
            Position {
                late: true,
                gate: Some(Term::Bool(false)),
            },
        ),
        (positive(oob(IntRange::U(8), n())), Position::default()),
    ];
    no_clip(&items(&hypotheses));
}

#[test]
fn whole_source_operand_and_range_are_not_replaced_by_fallback_spelling() {
    let canonical = clipped(n());
    let Term::Ite(predicate, _, _, _) = &canonical else {
        panic!("nonconstant canonical clip")
    };
    let wrong_range = Term::Ite(
        predicate.clone(),
        Box::new(n()),
        Box::new(oob(IntRange::U(16), n())),
        Sort::Int,
    );
    let Term::Ite(other_predicate, _, _, _) = clipped(m()) else {
        unreachable!()
    };
    let wrong_operand = Term::Ite(
        other_predicate,
        Box::new(n()),
        Box::new(oob(IntRange::U(8), n())),
        Sort::Int,
    );
    for malformed in [wrong_range, wrong_operand] {
        no_clip(&items(&placed(vec![
            outside(n()),
            outside(m()),
            positive(malformed),
        ])));
    }
    // A genuine origin discarded elsewhere cannot attach to another operand.
    let discarded = Term::Or(vec![Term::Bool(true), positive(canonical)]);
    let other = oob(IntRange::U(8), m());
    let found = items(&placed(vec![
        outside(n()),
        outside(m()),
        discarded,
        positive(other.clone()),
    ]));
    assert!(condition(&found, &other).is_some());
    no_clip(&found);

    // A genuinely surviving in-range Var image is not a fallback-call
    // witness and cannot turn every original clip into material metadata.
    let in_range = items(&placed(vec![
        Term::le(Term::Int(0), n()),
        Term::le(n(), Term::Int(255)),
        positive(clipped(n())),
        positive(other),
    ]));
    no_clip(&in_range);
}

#[test]
fn an_actual_operand_literal_rewrite_retains_only_its_original_whole_source() {
    let source = clipped(n());
    let found = items(&placed(vec![
        Term::eq(n(), Term::Int(256)),
        positive(source.clone()),
    ]));
    let guard = condition(&found, &source)
        .expect("actual same-pass operand rewrite carries source provenance");
    assert_eq!(under_gate(guard, false), Term::Bool(true));
    assert!(
        condition(&found, &clipped(m())).is_none(),
        "another source operand has no authority"
    );
}

#[test]
fn seed_origins_do_not_escape_into_body_or_definition_instance_reads() {
    let a0 = Term::var("a0", Sort::Int);
    let definition = SpecDef {
        function: "origin_wrapper".into(),
        params: vec![("a0".into(), Sort::Int)],
        guard: Term::Bool(true),
        body: oob(IntRange::U(8), a0),
    };
    let defs = HashMap::from([("origin_wrapper", &definition)]);
    let read_role = |name: &str| {
        if name == "origin_wrapper" {
            CallRole::Defined
        } else {
            role(name)
        }
    };
    let requested = ranges();
    let mut analysis = Analysis::new(&read_role, &defs, 200_000).with_clip_triggers(&requested);
    let first = analysis
        .seeds(
            &placed(vec![outside(n()), positive(clipped(n()))]),
            &(Term::Bool(false), Position::default()),
        )
        .unwrap()
        .into_items();
    assert!(
        condition(&first, &clipped(n())).is_some(),
        "exercise an activated seed scope first"
    );
    for body in [
        oob(IntRange::U(8), n()),
        Term::call("origin_wrapper", vec![n()], Sort::Int),
    ] {
        let found = analysis.body(&body).unwrap().into_items();
        no_clip(&found);
    }
}

#[test]
fn origin_tracking_and_a_later_body_read_share_the_original_exhausted_grant() {
    let hypotheses = placed(vec![outside(n()), positive(clipped(n()))]);
    let initial: usize = hypotheses
        .iter()
        .map(|(term, _)| term.size())
        .sum::<usize>()
        + 1;
    let budget = initial + 32;
    assert!(
        initial < budget,
        "the input node census alone fits this grant"
    );
    let defs = HashMap::new();
    let requested = ranges();
    let mut analysis = Analysis::new(&role, &defs, budget).with_clip_triggers(&requested);
    assert!(analysis
        .seeds(&hypotheses, &(Term::Bool(false), Position::default()))
        .is_err());
    assert!(
        analysis.body(&oob(IntRange::U(8), n())).is_err(),
        "no new grant may be minted after origin admission exhaustion"
    );
}

fn ordinary_uf() -> Term {
    Term::call("origin_actual_uf", vec![n()], Sort::Int)
}
fn uf_items(hypotheses: &[(Term, Position)]) -> Vec<(Term, Term)> {
    let defs = HashMap::new();
    let requested = ranges();
    let with_uf = |name: &str| {
        if name == "origin_actual_uf" {
            CallRole::Collect
        } else {
            role(name)
        }
    };
    let mut analysis = Analysis::new(&with_uf, &defs, 200_000).with_clip_triggers(&requested);
    let found = analysis
        .seeds(hypotheses, &(Term::Bool(false), Position::default()))
        .expect("unchanged source admission grant");
    resolved(analysis, found)
}
fn evaluate_uf_gate(guard: &Term, gate: bool) -> Term {
    let mut graph = EGraph::default();
    graph.assert(&Term::eq(ordinary_uf(), Term::Int(7)));
    graph.assert(&if gate { g() } else { g().not() });
    Simp::with(&mut graph).go(guard)
}

#[test]
fn a_still_present_canonical_clip_has_its_actual_in_range_uf_witness() {
    let source = clipped(ordinary_uf());
    let found = uf_items(&placed(vec![positive(source.clone())]));
    let guard = condition(&found, &source).expect("the whole still-present canonical application");
    assert_eq!(evaluate_uf_gate(guard, false), Term::Bool(true));
}

#[test]
fn bare_discarded_and_collapsed_uf_images_never_invent_whole_clips() {
    let raw = ordinary_uf();
    no_clip(&uf_items(&placed(vec![positive(raw.clone())])));
    no_clip(&uf_items(&placed(vec![
        Term::Or(vec![Term::Bool(true), positive(clipped(raw.clone()))]),
        positive(raw.clone()),
        positive(oob(IntRange::U(8), raw.clone())),
    ])));
    // This extension only borrows a still-present ITE. A collapsed in-range
    // UF image cannot use a discarded original clip as a candidate.
    no_clip(&uf_items(&placed(vec![
        Term::le(Term::Int(0), raw.clone()),
        Term::le(raw.clone(), Term::Int(255)),
        positive(clipped(raw)),
    ])));
}

#[test]
fn an_opposite_branch_bare_uf_cannot_erase_the_whole_clip_gate() {
    let source = clipped(ordinary_uf());
    let found = uf_items(&placed(vec![Term::Ite(
        Box::new(g()),
        Box::new(positive(source.clone())),
        Box::new(positive(ordinary_uf())),
        Sort::Bool,
    )]));
    let guard = condition(&found, &source).expect("the actual conditional source clip");
    assert_eq!(evaluate_uf_gate(guard, true), Term::Bool(true));
    assert_eq!(evaluate_uf_gate(guard, false), Term::Bool(false));
}
