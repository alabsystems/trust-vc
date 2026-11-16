//! Actual production relevance analysis; no solver or synthetic authority.
use super::super::spec;
use super::*;
use crate::IntRange;

fn items(
    goal: &Term,
    arithmetic: &HashSet<ArithOp>,
    clips: &HashSet<IntRange>,
) -> Vec<(Term, Term)> {
    let defs = HashMap::new();
    let role = |name: &str| {
        if name == spec::clip_oob_name(IntRange::U(8)) {
            CallRole::Collect
        } else {
            CallRole::Other
        }
    };
    Analysis::new(&role, &defs, 200_000)
        .with_arithmetic_triggers(arithmetic)
        .with_clip_triggers(clips)
        .seeds(&[], &(goal.clone(), Position::default()))
        .unwrap()
        .into_items()
}
fn greater_than_zero(value: Term) -> Term {
    Term::Cmp(CmpOp::Lt, Box::new(Term::Int(0)), Box::new(value))
}

#[test]
fn a_live_whole_clip_candidate_retains_the_actual_out_of_range_branch_condition() {
    let x = Term::var("x", Sort::Int);
    let clipped = spec::clip(IntRange::U(8), x.clone());
    let found = items(
        &greater_than_zero(clipped.clone()),
        &HashSet::new(),
        &[IntRange::U(8)].into_iter().collect(),
    );
    let (_, condition) = found
        .iter()
        .find(|(term, _)| term == &clipped)
        .expect("actual live whole clip");
    assert_ne!(
        condition,
        &Term::Bool(true),
        "the oob branch is a real premise, never an always-material clip"
    );
}

#[test]
fn a_bare_fallback_call_cannot_reconstruct_a_whole_clip_candidate() {
    let fallback = Term::call(
        spec::clip_oob_name(IntRange::U(8)),
        vec![Term::var("x", Sort::Int)],
        Sort::Int,
    );
    let found = items(
        &greater_than_zero(fallback.clone()),
        &HashSet::new(),
        &[IntRange::U(8)].into_iter().collect(),
    );
    assert!(
        found.iter().any(|(term, _)| term == &fallback),
        "the genuine call itself remains material"
    );
    assert!(!found.iter().any(|(term, _)| matches!(term, Term::Ite(..))));
}

#[test]
fn folded_or_discarded_clip_subterms_never_become_material_candidates() {
    let clipped = spec::clip(IntRange::U(8), Term::var("x", Sort::Int));
    let same = Term::Cmp(
        CmpOp::Eq,
        Box::new(clipped.clone()),
        Box::new(clipped.clone()),
    );
    let dead = Term::Ite(
        Box::new(Term::Bool(false)),
        Box::new(greater_than_zero(clipped.clone())),
        Box::new(Term::Bool(true)),
        Sort::Bool,
    );
    for goal in [same, dead] {
        assert!(!items(
            &goal,
            &HashSet::new(),
            &[IntRange::U(8)].into_iter().collect()
        )
        .iter()
        .any(|(term, _)| term == &clipped));
    }
}

#[test]
fn an_arithmetic_seed_requires_an_actual_typed_operation_and_relevant_context() {
    let add = Term::Arith(
        ArithOp::Add,
        Box::new(Term::var("x", Sort::Int)),
        Box::new(Term::Int(1)),
    );
    let requested = [ArithOp::Add].into_iter().collect();
    assert!(
        items(&greater_than_zero(add.clone()), &requested, &HashSet::new())
            .iter()
            .any(|(term, _)| term == &add)
    );
    let discarded = Term::Cmp(CmpOp::Eq, Box::new(add.clone()), Box::new(add.clone()));
    assert!(!items(&discarded, &requested, &HashSet::new())
        .iter()
        .any(|(term, _)| term == &add));
    assert!(!items(
        &greater_than_zero(add.clone()),
        &[ArithOp::Sub].into_iter().collect(),
        &HashSet::new()
    )
    .iter()
    .any(|(term, _)| term == &add));
}

#[test]
fn initial_source_admission_stops_under_the_original_shared_budget() {
    let defs = HashMap::new();
    let role = |_: &str| CallRole::Collect;
    let clips = [IntRange::U(8)].into_iter().collect();
    let arithmetic = [ArithOp::Add].into_iter().collect();
    let goal = greater_than_zero(spec::clip(
        IntRange::U(8),
        Term::var("large".repeat(1024), Sort::Int),
    ));
    assert!(Analysis::new(&role, &defs, 3)
        .with_arithmetic_triggers(&arithmetic)
        .with_clip_triggers(&clips)
        .seeds(&[], &(goal, Position::default()))
        .is_err());
}

#[test]
fn admitted_disjoint_facts_pay_for_the_actual_arithmetic_fact_index() {
    // B1 family: N unrelated comparisons plus M independent Add carriers.
    // Their initial syntax is small. The real seeds->rel->filter->arithmetic
    // search must pay construction of the entire fact index before using it.
    let n = 128usize;
    let m = 64usize;
    let mut hypotheses = Vec::new();
    for i in 0..n {
        hypotheses.push((
            Term::Cmp(
                CmpOp::Lt,
                Box::new(Term::var(format!("disjoint_a{i}"), Sort::Int)),
                Box::new(Term::var(format!("disjoint_b{i}"), Sort::Int)),
            ),
            Position::default(),
        ));
    }
    for i in 0..m {
        hypotheses.push((
            Term::Cmp(
                CmpOp::Lt,
                Box::new(Term::Arith(
                    ArithOp::Add,
                    Box::new(Term::var(format!("carrier_x{i}"), Sort::Int)),
                    Box::new(Term::var(format!("carrier_y{i}"), Sort::Int)),
                )),
                Box::new(Term::var(format!("carrier_z{i}"), Sort::Int)),
            ),
            Position::default(),
        ));
    }
    let initial_nodes: usize = hypotheses.iter().map(|(term, _)| term.size()).sum();
    assert!(
        initial_nodes + 1 < 200_000 / 8,
        "initial admission cannot explain this exhaustion"
    );
    let defs = HashMap::new();
    let role = |_: &str| CallRole::Other;
    let heads = [ArithOp::Add].into_iter().collect();
    let mut analysis = Analysis::new(&role, &defs, 200_000).with_arithmetic_triggers(&heads);
    let observed = analysis.seeds(&hypotheses, &(Term::Bool(false), Position::default()));
    assert!(
        analysis.arithmetic_searches > 0,
        "must actually reach the new arithmetic witness path"
    );
    assert!(analysis.fact_closure_calls > 0 && analysis.fact_closure_input_rows > 0);
    assert_eq!(
        analysis.fact_closure_passes, 0,
        "the index itself exhausts the grant before frontier traversal"
    );
    assert!(
        analysis.fact_closure_exhaustions > 0,
        "the shared helper must refuse its own unadmitted work"
    );
    assert!(observed.is_err() && analysis.budget == 0);
}
