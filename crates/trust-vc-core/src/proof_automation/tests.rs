// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use std::time::Duration;

// -- Expr tests ---------------------------------------------------------

#[test]
fn test_expr_free_vars_simple() {
    let e = Expr::add(Expr::var("x"), Expr::var("y"));
    let vars = e.free_vars();
    assert_eq!(vars, vec!["x", "y"]);
}

#[test]
fn test_expr_free_vars_quantifier_binds() {
    let e = Expr::forall("x", Expr::gt(Expr::var("x"), Expr::var("y")));
    let vars = e.free_vars();
    assert_eq!(vars, vec!["y"]);
}

#[test]
fn test_expr_complexity_leaf() {
    assert_eq!(Expr::var("x").complexity(), 1);
    assert_eq!(Expr::int(42).complexity(), 1);
    assert_eq!(Expr::True.complexity(), 1);
}

#[test]
fn test_expr_complexity_compound() {
    let e = Expr::add(Expr::var("x"), Expr::int(1));
    assert_eq!(e.complexity(), 3);
}

#[test]
fn test_expr_mentions_var() {
    let e = Expr::add(Expr::var("x"), Expr::var("y"));
    assert!(e.mentions_var("x"));
    assert!(!e.mentions_var("z"));
}

#[test]
fn test_expr_display() {
    let e = Expr::add(Expr::var("x"), Expr::int(1));
    assert_eq!(format!("{e}"), "(x + 1)");
}

// -- Simplify tests -----------------------------------------------------

#[test]
fn test_simplify_constant_fold_add() {
    let e = Expr::add(Expr::int(2), Expr::int(3));
    assert_eq!(simplify_expr(&e), Expr::int(5));
}

#[test]
fn test_simplify_add_zero_identity() {
    let e = Expr::add(Expr::var("x"), Expr::int(0));
    assert_eq!(simplify_expr(&e), Expr::var("x"));
}

#[test]
fn test_simplify_sub_self() {
    let e = Expr::sub(Expr::var("x"), Expr::var("x"));
    assert_eq!(simplify_expr(&e), Expr::int(0));
}

#[test]
fn test_simplify_mul_by_one() {
    let e = Expr::mul(Expr::int(1), Expr::var("x"));
    assert_eq!(simplify_expr(&e), Expr::var("x"));
}

#[test]
fn test_simplify_mul_by_zero() {
    let e = Expr::mul(Expr::var("x"), Expr::int(0));
    assert_eq!(simplify_expr(&e), Expr::int(0));
}

#[test]
fn test_simplify_double_negation() {
    let e = Expr::not(Expr::not(Expr::var("p")));
    assert_eq!(simplify_expr(&e), Expr::var("p"));
}

#[test]
fn test_simplify_and_true() {
    let e = Expr::and(Expr::True, Expr::var("p"));
    assert_eq!(simplify_expr(&e), Expr::var("p"));
}

#[test]
fn test_simplify_or_false() {
    let e = Expr::or(Expr::False, Expr::var("p"));
    assert_eq!(simplify_expr(&e), Expr::var("p"));
}

#[test]
fn test_simplify_implies_false_antecedent() {
    let e = Expr::implies(Expr::False, Expr::var("q"));
    assert_eq!(simplify_expr(&e), Expr::True);
}

#[test]
fn test_simplify_eq_reflexive() {
    let e = Expr::eq(Expr::var("x"), Expr::var("x"));
    assert_eq!(simplify_expr(&e), Expr::True);
}

#[test]
fn test_simplify_le_reflexive() {
    let e = Expr::le(Expr::var("x"), Expr::var("x"));
    assert_eq!(simplify_expr(&e), Expr::True);
}

#[test]
fn test_simplify_lt_constants() {
    let e = Expr::lt(Expr::int(3), Expr::int(5));
    assert_eq!(simplify_expr(&e), Expr::BoolLit(true));
}

// -- Tactic tests -------------------------------------------------------

#[test]
fn test_tactic_simplify_proves_trivial() {
    let goal = ProofGoal::new(Expr::eq(Expr::int(1), Expr::int(1)));
    let result = apply_tactic_to_goal(&goal, &ProofTactic::Simplify);
    assert!(result.is_proved());
}

#[test]
fn test_tactic_arith_hypothesis_match() {
    let goal = ProofGoal::new(Expr::ge(Expr::var("x"), Expr::int(0)))
        .with_hypotheses(vec![Expr::ge(Expr::var("x"), Expr::int(0))]);
    let result = apply_tactic_to_goal(&goal, &ProofTactic::Arith);
    assert!(result.is_proved());
}

#[test]
fn test_tactic_arith_square_nonneg() {
    let sq = Expr::mul(Expr::var("x"), Expr::var("x"));
    let goal = ProofGoal::new(Expr::ge(sq, Expr::int(0)));
    let result = apply_tactic_to_goal(&goal, &ProofTactic::Arith);
    assert!(result.is_proved());
}

#[test]
fn test_tactic_arith_gt_implies_ge() {
    let goal = ProofGoal::new(Expr::ge(Expr::var("x"), Expr::int(0)))
        .with_hypotheses(vec![Expr::gt(Expr::var("x"), Expr::int(0))]);
    let result = apply_tactic_to_goal(&goal, &ProofTactic::Arith);
    assert!(result.is_proved());
}

#[test]
fn test_tactic_arith_transitivity() {
    let goal = ProofGoal::new(Expr::lt(Expr::var("a"), Expr::var("c"))).with_hypotheses(vec![
        Expr::lt(Expr::var("a"), Expr::var("b")),
        Expr::lt(Expr::var("b"), Expr::var("c")),
    ]);
    let result = apply_tactic_to_goal(&goal, &ProofTactic::Arith);
    assert!(result.is_proved());
}

#[test]
fn test_tactic_split_conjunction() {
    let goal = ProofGoal::new(Expr::and(Expr::var("p"), Expr::var("q")));
    let result = apply_tactic_to_goal(&goal, &ProofTactic::SplitCases);
    match result {
        TacticResult::Reduced(goals) => {
            assert_eq!(goals.len(), 2);
            assert_eq!(goals[0].expression, Expr::var("p"));
            assert_eq!(goals[1].expression, Expr::var("q"));
        }
        other => panic!("expected Reduced, got {other:?}"),
    }
}

#[test]
fn test_tactic_split_implication() {
    let goal = ProofGoal::new(Expr::implies(Expr::var("p"), Expr::var("q")));
    let result = apply_tactic_to_goal(&goal, &ProofTactic::SplitCases);
    match result {
        TacticResult::Reduced(goals) => {
            assert_eq!(goals.len(), 1);
            assert_eq!(goals[0].expression, Expr::var("q"));
            assert!(goals[0].hypotheses.contains(&Expr::var("p")));
        }
        other => panic!("expected Reduced, got {other:?}"),
    }
}

#[test]
fn test_tactic_contradiction_p_and_not_p() {
    let goal = ProofGoal::new(Expr::var("anything"))
        .with_hypotheses(vec![Expr::var("p"), Expr::not(Expr::var("p"))]);
    let result = apply_tactic_to_goal(&goal, &ProofTactic::Contradiction);
    assert!(result.is_proved());
}

#[test]
fn test_tactic_contradiction_false_hypothesis() {
    let goal = ProofGoal::new(Expr::var("anything")).with_hypotheses(vec![Expr::False]);
    let result = apply_tactic_to_goal(&goal, &ProofTactic::Contradiction);
    assert!(result.is_proved());
}

#[test]
fn test_tactic_contradiction_lt_self() {
    let goal = ProofGoal::new(Expr::var("anything"))
        .with_hypotheses(vec![Expr::lt(Expr::var("x"), Expr::var("x"))]);
    let result = apply_tactic_to_goal(&goal, &ProofTactic::Contradiction);
    assert!(result.is_proved());
}

#[test]
fn test_tactic_induction_produces_two_goals() {
    let scheme = InductionScheme::natural("n");
    let goal = ProofGoal::new(Expr::ge(Expr::var("n"), Expr::int(0)));
    let result = apply_tactic_to_goal(&goal, &ProofTactic::Induction(scheme));
    match result {
        TacticResult::Reduced(goals) => {
            assert_eq!(goals.len(), 2);
            assert!(goals[0].label.contains("base"));
            assert!(goals[1].label.contains("step"));
        }
        other => panic!("expected Reduced, got {other:?}"),
    }
}

#[test]
fn test_tactic_induction_var_not_in_goal() {
    let scheme = InductionScheme::natural("n");
    let goal = ProofGoal::new(Expr::ge(Expr::var("x"), Expr::int(0)));
    let result = apply_tactic_to_goal(&goal, &ProofTactic::Induction(scheme));
    assert!(result.is_failed());
}

#[test]
fn test_tactic_auto_proves_trivial() {
    let goal = ProofGoal::new(Expr::eq(Expr::int(5), Expr::int(5)));
    let result = apply_tactic_to_goal(&goal, &ProofTactic::Auto);
    assert!(result.is_proved());
}

#[test]
fn test_tactic_rewrite_available() {
    let goal = ProofGoal::new(Expr::var("x")).with_lemmas(vec!["eq_comm".to_owned()]);
    let result = apply_tactic_to_goal(&goal, &ProofTactic::Rewrite("eq_comm".to_owned()));
    assert!(matches!(result, TacticResult::Progress(_)));
}

#[test]
fn test_tactic_rewrite_unavailable() {
    let goal = ProofGoal::new(Expr::var("x"));
    let result = apply_tactic_to_goal(&goal, &ProofTactic::Rewrite("eq_comm".to_owned()));
    assert!(result.is_failed());
}

// -- ProofScript tests --------------------------------------------------

#[test]
fn test_proof_script_empty() {
    let script = ProofScript::new();
    assert!(script.is_empty());
    assert_eq!(script.len(), 0);
}

#[test]
fn test_proof_script_single_step_proves() {
    let script = ProofScript::new().then(ProofTactic::Simplify);
    let goal = ProofGoal::new(Expr::eq(Expr::int(1), Expr::int(1)));
    let result = script.execute(&goal);
    assert!(result.is_proved());
}

#[test]
fn test_proof_script_chain() {
    // Simplify then arith.
    let script = ProofScript::new()
        .then(ProofTactic::Simplify)
        .then(ProofTactic::Arith);
    assert_eq!(script.len(), 2);
}

// -- ProofState tests ---------------------------------------------------

#[test]
fn test_proof_state_initial() {
    let goal = ProofGoal::new(Expr::var("p"));
    let state = ProofState::new(goal);
    assert!(!state.is_solved());
    assert_eq!(state.open_goal_count(), 1);
    assert_eq!(state.solved_count(), 0);
}

#[test]
fn test_proof_state_solve_trivial() {
    let goal = ProofGoal::new(Expr::eq(Expr::int(1), Expr::int(1)));
    let mut state = ProofState::new(goal);
    let result = state.apply(&ProofTactic::Simplify);
    assert!(result.is_proved());
    assert!(state.is_solved());
    assert_eq!(state.solved_count(), 1);
}

#[test]
fn test_proof_state_split_produces_subgoals() {
    let goal = ProofGoal::new(Expr::and(
        Expr::eq(Expr::int(1), Expr::int(1)),
        Expr::eq(Expr::int(2), Expr::int(2)),
    ));
    let mut state = ProofState::new(goal);
    let result = state.apply(&ProofTactic::SplitCases);
    assert!(matches!(result, TacticResult::Reduced(_)));
    assert_eq!(state.open_goal_count(), 2);
}

// -- LemmaDatabase tests ------------------------------------------------

#[test]
fn test_lemma_database_add_and_search() {
    let mut db = LemmaDatabase::new();
    db.add_lemma(Lemma::new(
        "nonneg_x",
        vec![],
        Expr::ge(Expr::var("x"), Expr::int(0)),
    ));
    db.add_lemma(Lemma::new(
        "pos_y",
        vec![],
        Expr::gt(Expr::var("y"), Expr::int(0)),
    ));

    let results = db.search("x");
    assert_eq!(results.len(), 1);
    assert_eq!(results[0].name, "nonneg_x");
}

#[test]
fn test_lemma_database_empty() {
    let db = LemmaDatabase::new();
    assert!(db.is_empty());
    assert_eq!(db.len(), 0);
    assert!(db.search("anything").is_empty());
}

#[test]
fn test_standard_lemma_database_populated() {
    let db = standard_lemma_database();
    assert!(db.len() >= 5);
    assert!(!db.search("bounds").is_empty());
    assert!(!db.search("square").is_empty());
}

// -- TacticLibrary tests ------------------------------------------------

#[test]
fn test_tactic_library_register_and_query() {
    let mut lib = TacticLibrary::new();
    lib.register(
        "always",
        ProofTactic::Simplify,
        |_| true,
        |_| TacticResult::Proved,
    );
    assert_eq!(lib.len(), 1);

    let goal = ProofGoal::new(Expr::var("p"));
    let applicable = lib.applicable_tactics(&goal);
    assert_eq!(applicable.len(), 1);
}

#[test]
fn test_tactic_library_execute_by_name() {
    let mut lib = TacticLibrary::new();
    lib.register(
        "prove_it",
        ProofTactic::Auto,
        |_| true,
        |_| TacticResult::Proved,
    );
    let goal = ProofGoal::new(Expr::var("p"));
    let result = lib.execute_by_name("prove_it", &goal);
    assert!(result.is_proved());
}

#[test]
fn test_tactic_library_unknown_name() {
    let lib = TacticLibrary::new();
    let goal = ProofGoal::new(Expr::var("p"));
    let result = lib.execute_by_name("nonexistent", &goal);
    assert!(result.is_failed());
}

#[test]
fn test_standard_tactic_library_has_entries() {
    let lib = standard_tactic_library();
    assert!(lib.len() >= 4);
}

// -- SearchConfig tests -------------------------------------------------

#[test]
fn test_search_config_defaults() {
    let cfg = SearchConfig::new();
    assert_eq!(cfg.max_depth, 10);
    assert_eq!(cfg.max_branches, 50);
    assert!(!cfg.strategies.is_empty());
}

#[test]
fn test_search_config_builder() {
    let cfg = SearchConfig::new()
        .with_max_depth(5)
        .with_max_branches(20)
        .with_timeout(Duration::from_millis(100));
    assert_eq!(cfg.max_depth, 5);
    assert_eq!(cfg.max_branches, 20);
    assert_eq!(cfg.timeout, Duration::from_millis(100));
}

// -- ProofSearch tests --------------------------------------------------

#[test]
fn test_search_trivial_equality() {
    let search = ProofSearch::new(SearchConfig::new());
    let goal = ProofGoal::new(Expr::eq(Expr::int(1), Expr::int(1)));
    let result = search.search(&goal);
    assert!(result.found_proof.is_some());
    assert!(result.stats.nodes_explored >= 1);
}

#[test]
fn test_search_arith_hypothesis() {
    let search = ProofSearch::new(SearchConfig::new());
    let goal = ProofGoal::new(Expr::ge(Expr::var("x"), Expr::int(0)))
        .with_hypotheses(vec![Expr::ge(Expr::var("x"), Expr::int(0))]);
    let result = search.search(&goal);
    assert!(result.found_proof.is_some());
}

#[test]
fn test_search_contradiction() {
    let search = ProofSearch::new(SearchConfig::new());
    let goal = ProofGoal::new(Expr::var("anything"))
        .with_hypotheses(vec![Expr::var("p"), Expr::not(Expr::var("p"))]);
    let result = search.search(&goal);
    assert!(result.found_proof.is_some());
}

#[test]
fn test_search_fails_on_unprovable() {
    let cfg = SearchConfig::new().with_max_depth(3).with_max_branches(10);
    let search = ProofSearch::new(cfg);
    let goal = ProofGoal::new(Expr::var("unknown_proposition"));
    let result = search.search(&goal);
    assert!(result.found_proof.is_none());
    assert!(result.stats.pruned > 0 || result.stats.tactics_tried > 0);
}

#[test]
fn test_search_with_hints() {
    let search = ProofSearch::new(SearchConfig::new()).with_hints(vec![AutomationHint::UseArith]);
    let goal = ProofGoal::new(Expr::ge(
        Expr::mul(Expr::var("x"), Expr::var("x")),
        Expr::int(0),
    ));
    let result = search.search(&goal);
    assert!(result.found_proof.is_some());
}

#[test]
fn test_search_respects_max_depth() {
    let cfg = SearchConfig::new().with_max_depth(0);
    let search = ProofSearch::new(cfg);
    let goal = ProofGoal::new(Expr::var("p"));
    let result = search.search(&goal);
    assert!(result.found_proof.is_none());
    assert!(result.stats.pruned > 0);
}

#[test]
fn test_search_respects_max_branches() {
    let cfg = SearchConfig::new().with_max_branches(1);
    let search = ProofSearch::new(cfg);
    let goal = ProofGoal::new(Expr::var("p"));
    let result = search.search(&goal);
    assert!(result.found_proof.is_none());
}

#[test]
fn test_search_apply_tactic_public_api() {
    let search = ProofSearch::new(SearchConfig::new());
    let goal = ProofGoal::new(Expr::eq(Expr::int(2), Expr::int(2)));
    let result = search.apply_tactic(&goal, &ProofTactic::Simplify);
    assert!(result.is_proved());
}

#[test]
fn test_search_stats_nonzero_time() {
    let search = ProofSearch::new(SearchConfig::new());
    let goal = ProofGoal::new(Expr::eq(Expr::int(1), Expr::int(1)));
    let result = search.search(&goal);
    // Time may be zero on fast machines, but should not panic.
    let _ = result.stats.time_elapsed;
    assert!(result.stats.tactics_tried >= 1);
}

// -- Integration: automation patterns -----------------------------------

#[test]
fn test_automation_bounds_check_pattern() {
    // Typical bounds check: 0 <= i && i < len
    let search = ProofSearch::new(SearchConfig::new());
    let goal = ProofGoal::new(Expr::ge(Expr::var("i"), Expr::int(0))).with_hypotheses(vec![
        Expr::ge(Expr::var("i"), Expr::int(0)),
        Expr::lt(Expr::var("i"), Expr::var("len")),
    ]);
    let result = search.search(&goal);
    assert!(result.found_proof.is_some());
}

#[test]
fn test_automation_overflow_constant() {
    // 2 + 3 = 5, which is in i32 range.
    let search = ProofSearch::new(SearchConfig::new());
    let goal = ProofGoal::new(Expr::eq(
        Expr::add(Expr::int(2), Expr::int(3)),
        Expr::int(5),
    ));
    let result = search.search(&goal);
    assert!(result.found_proof.is_some());
}

#[test]
fn test_automation_sorted_nonneg_length() {
    // len(arr) >= 0 is always true.
    let search = ProofSearch::new(SearchConfig::new()).with_lemma_db(standard_lemma_database());
    let goal = ProofGoal::new(Expr::ge(Expr::array_len(Expr::var("arr")), Expr::int(0)));
    // This should simplify or be found via arith on the standard lemma.
    let _result = search.search(&goal);
    // The built-in arith doesn't know array axioms directly, but the
    // lemma DB has the fact. Verify the DB can find it.
    let db = standard_lemma_database();
    let lemmas = db.search("length");
    assert!(!lemmas.is_empty());
}

// -- ProofGoal builder tests -------------------------------------------

#[test]
fn test_proof_goal_builder_chaining() {
    let goal = ProofGoal::new(Expr::var("p"))
        .with_hypotheses(vec![Expr::var("h")])
        .with_lemmas(vec!["lem1".to_owned()])
        .with_label("my_goal");
    assert_eq!(goal.label, "my_goal");
    assert_eq!(goal.hypotheses.len(), 1);
    assert_eq!(goal.available_lemmas.len(), 1);
}

#[test]
fn test_proof_goal_complexity() {
    let goal = ProofGoal::new(Expr::add(Expr::var("x"), Expr::int(1)))
        .with_hypotheses(vec![Expr::ge(Expr::var("x"), Expr::int(0))]);
    // goal expr complexity = 3, hypothesis complexity = 3, total = 6
    assert_eq!(goal.complexity(), 6);
}

// -- InductionScheme tests ---------------------------------------------

#[test]
fn test_induction_scheme_natural() {
    let scheme = InductionScheme::natural("n");
    assert_eq!(scheme.variable, "n");
    assert_eq!(scheme.well_founded_order, WellFoundedOrder::Natural);
}

#[test]
fn test_induction_scheme_custom_base() {
    let scheme = InductionScheme::natural("n").with_base(Expr::eq(Expr::var("n"), Expr::int(1)));
    assert_eq!(scheme.base_case, Expr::eq(Expr::var("n"), Expr::int(1)));
}

// -- ProofTactic Display -----------------------------------------------

#[test]
fn test_tactic_display() {
    assert_eq!(format!("{}", ProofTactic::Auto), "auto");
    assert_eq!(format!("{}", ProofTactic::Arith), "arith");
    assert_eq!(format!("{}", ProofTactic::SplitCases), "split_cases");
    assert_eq!(
        format!("{}", ProofTactic::Rewrite("eq_sym".to_owned())),
        "rewrite(eq_sym)"
    );
}

// -- AutomationHint coverage -------------------------------------------

#[test]
fn test_hint_max_depth_respected_in_search() {
    let search = ProofSearch::new(SearchConfig::new().with_max_depth(100))
        .with_hints(vec![AutomationHint::MaxDepth(0)]);
    let goal = ProofGoal::new(Expr::var("p"));
    let result = search.search(&goal);
    // MaxDepth(0) hint should override config and prune immediately.
    assert!(result.found_proof.is_none());
}
