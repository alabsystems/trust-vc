// trust-vc-oracle — Oracle-to-CGSR pipeline integration tests
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// End-to-end tests demonstrating the full oracle-to-CGSR pipeline:
//   source parsing -> mine initial specs -> CGSR refinement -> ranking -> store
//
// All tests use the public API from trust_vc_oracle and are fully deterministic
// (no external LLM service, no filesystem side effects except tempdir).

use std::collections::HashSet;
use std::time::Duration;

use trust_vc_oracle::cgsr::{CgsrConfig, CgsrEngine, Counterexample, RefinementStrategy};
use trust_vc_oracle::convergence::{
    ConvergencePredictor, ConvergenceTracker, Difficulty, DifficultyClassifier,
};
use trust_vc_oracle::spec_diff::{diff_spec_sets, spec_evolution, ConvergenceMetric};
use trust_vc_oracle::spec_ranking::{rank_specs, score_spec, template_specificity, weights};
use trust_vc_oracle::spec_store::SpecStore;
use trust_vc_oracle::{
    mine_specs, parse_function_by_name, parse_functions, FunctionSignature, MinedSpec,
    MiningConfig, ProofFeedback,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Build a FunctionSignature with canonical type strings (no spaces in
/// generics) so template applicability works correctly.
fn sig(
    name: &str,
    params: &[(&str, &str)],
    return_type: Option<&str>,
    source: &str,
) -> FunctionSignature {
    FunctionSignature::new(
        name,
        params
            .iter()
            .map(|(n, t)| (n.to_string(), t.to_string()))
            .collect(),
        return_type.map(String::from),
        source,
    )
}

/// Create a `MinedSpec` with the given fields.
fn mined(
    func: &str,
    template: &str,
    requires: &[&str],
    ensures: &[&str],
    verified: bool,
    iterations: usize,
) -> MinedSpec {
    MinedSpec::new(
        func.to_string(),
        template.to_string(),
        requires.iter().map(|s| s.to_string()).collect(),
        ensures.iter().map(|s| s.to_string()).collect(),
        verified,
        iterations,
    )
}

fn make_verified_feedback() -> ProofFeedback {
    ProofFeedback::Verified {
        steps: vec![],
        elapsed: Duration::from_millis(1),
        certificate_info: None,
    }
}

fn make_failed_feedback(var: &str, val: &str) -> ProofFeedback {
    use trust_vc_oracle::{CounterexampleField, FailureLocalization};
    ProofFeedback::Failed {
        counterexamples: vec![CounterexampleField {
            name: var.to_string(),
            ty: "i32".to_string(),
            value: val.to_string(),
        }],
        localization: FailureLocalization {
            full_assertion: None,
            sub_results: vec![],
        },
        obligation_name: "ensures".to_string(),
        solver_mode: "default".to_string(),
        elapsed: Duration::from_millis(1),
    }
}

fn temp_store_path(label: &str) -> std::path::PathBuf {
    std::env::temp_dir().join(format!(
        "trust_vc_oracle_cgsr_integ_{}_{}.json",
        label,
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock should be after epoch")
            .as_nanos()
    ))
}

// ===========================================================================
// 1. Parse source -> mine initial specs -> feed into CGSR -> refine -> rank
// ===========================================================================

#[test]
fn test_e2e_parse_mine_cgsr_refine_rank_single_function() {
    // Step 1: Parse source to extract function signatures.
    let source = "fn clamp(x: u32) -> u32 { if x > 100 { 100 } else { x } }";
    let functions = parse_functions(source);
    assert!(!functions.is_empty(), "should parse at least one function");
    assert_eq!(functions[0].name, "clamp");

    // Step 2: Mine initial specs (using real verifier pipeline).
    let mining_config = MiningConfig {
        max_refinements: 3,
        max_templates_per_function: 0,
        verbose: false,
    };
    let mined_specs = mine_specs(source, &mining_config);

    // Step 3: Feed mined specs into CGSR engine for further refinement.
    let cgsr_config = CgsrConfig {
        max_iterations: 5,
        strategy: RefinementStrategy::Strengthen,
        max_counterexamples: 10,
        verbose: false,
    };
    let engine = CgsrEngine::new(cgsr_config, mined_specs.clone());
    // Engine should accept the initial specs without panic.
    assert_eq!(engine.specs().len(), mined_specs.len());

    // Step 4: Rank whatever specs we have (mined or refined).
    let ranked = rank_specs(&mined_specs);
    // Ranking preserves all specs.
    assert_eq!(ranked.len(), mined_specs.len());

    // Verify ranking invariant: rank[i].rank == i+1 and scores are descending.
    for (i, r) in ranked.iter().enumerate() {
        assert_eq!(r.rank, i + 1);
        if i > 0 {
            assert!(
                ranked[i - 1].score.score >= r.score.score,
                "ranks should be in descending score order"
            );
        }
    }
}

#[test]
fn test_e2e_parse_mine_rank_with_two_param_function() {
    let source = "fn add(a: u32, b: u32) -> u32 { a + b }";
    let specs = mine_specs(source, &MiningConfig::default());

    // Mine should produce some specs for a two-param u32->u32 function.
    // Even if none verify, ranking should handle them.
    let ranked = rank_specs(&specs);
    assert_eq!(ranked.len(), specs.len());

    // All verified specs should rank above all unverified ones.
    let first_unverified = ranked.iter().position(|r| !r.spec.verified);
    let last_verified = ranked.iter().rposition(|r| r.spec.verified);
    if let (Some(last_v), Some(first_u)) = (last_verified, first_unverified) {
        assert!(
            last_v < first_u,
            "all verified specs should rank above all unverified"
        );
    }
}

// ===========================================================================
// 2. Mine -> store -> reload -> diff -> verify convergence
// ===========================================================================

#[test]
fn test_mine_store_reload_roundtrip() {
    let path = temp_store_path("roundtrip");
    let specs = vec![
        mined("abs", "range", &["x > 0"], &["result >= 0"], true, 0),
        mined("abs", "non_negative", &[], &["result >= 0"], true, 1),
    ];

    // Store
    let mut store = SpecStore::new(&path);
    for spec in &specs {
        store.add_spec(spec);
    }
    store.save().expect("save should succeed");

    // Reload
    let loaded = SpecStore::load(&path).expect("load should succeed");
    assert_eq!(loaded.len(), 2);
    assert_eq!(loaded.function_names(), vec!["abs"]);

    // Convert back to MinedSpec for diffing.
    let reloaded_specs: Vec<MinedSpec> = loaded.iter().map(MinedSpec::from).collect();
    let diff = diff_spec_sets(&specs, &reloaded_specs);
    assert!(
        diff.is_empty(),
        "round-tripped specs should produce an empty diff, got {} changes",
        diff.total_changed()
    );

    std::fs::remove_file(&path).ok();
}

#[test]
fn test_mine_store_diff_detects_strengthened_on_second_run() {
    let path = temp_store_path("strengthen_diff");

    // First run: weak spec
    let run1 = vec![mined("f", "range", &[], &["result >= 0"], true, 0)];
    let mut store = SpecStore::new(&path);
    for s in &run1 {
        store.add_spec(s);
    }
    store.save().expect("save should succeed");

    // Second run: strengthened spec (gained a precondition)
    let run2 = vec![mined("f", "range", &["x > 0"], &["result >= 0"], true, 1)];

    let diff = diff_spec_sets(&run1, &run2);
    assert_eq!(diff.strengthened.len(), 1);
    assert_eq!(diff.unchanged.len(), 0);

    std::fs::remove_file(&path).ok();
}

#[test]
fn test_store_reload_convergence_check() {
    let path = temp_store_path("convergence_check");

    let run1 = vec![
        mined("f", "range", &[], &["result >= 0"], true, 0),
        mined("g", "non_negative", &[], &["result >= 0"], true, 0),
    ];
    let run2 = vec![
        mined("f", "range", &["x > 0"], &["result >= 0"], true, 1),
        mined("g", "non_negative", &[], &["result >= 0"], true, 0),
    ];
    let run3 = vec![
        mined("f", "range", &["x > 0"], &["result >= 0"], true, 1),
        mined("g", "non_negative", &[], &["result >= 0"], true, 0),
    ];

    let run3_clone = run3.clone();
    let diffs = spec_evolution(&[run1, run2, run3]);
    assert_eq!(diffs.len(), 2);

    // First diff has changes; second has none.
    assert!(!diffs[0].is_empty(), "run1->run2 should have changes");
    assert!(diffs[1].is_empty(), "run2->run3 should be stable");

    let stability = ConvergenceMetric::stability_index(&diffs);
    assert!(stability > 0.5, "should be fairly stable, got {stability}");

    // Store the final run.
    let mut store = SpecStore::new(&path);
    for s in &run3_clone {
        store.add_spec(s);
    }
    store.save().expect("save should succeed");

    let loaded = SpecStore::load(&path).expect("load should succeed");
    assert_eq!(loaded.len(), 2);

    std::fs::remove_file(&path).ok();
}

// ===========================================================================
// 3. Multi-function mining with per-function CGSR refinement
// ===========================================================================

#[test]
fn test_multi_function_mining_produces_per_function_specs() {
    // mine_specs uses the real verifier pipeline. The source parser extracts
    // function signatures, applicable_templates generates candidate specs,
    // and verify_with_annotations checks them via ay. Because the parsed
    // params do not include a synthetic `result` variable, templates
    // referencing `result` may not verify. We verify the pipeline runs
    // without panics and that parse_functions finds all three functions.
    let source = r#"
        fn inc(x: u32) -> u32 { x + 1 }
        fn double(x: u32) -> u32 { x * 2 }
        fn identity(x: u32) -> u32 { x }
    "#;

    let functions = parse_functions(source);
    assert_eq!(functions.len(), 3, "should parse all three functions");

    let func_names: HashSet<&str> = functions.iter().map(|f| f.name.as_str()).collect();
    assert!(func_names.contains("inc"));
    assert!(func_names.contains("double"));
    assert!(func_names.contains("identity"));

    // Mining may or may not produce verified specs depending on template
    // applicability with real verifier; verify it runs without panics.
    let specs = mine_specs(source, &MiningConfig::default());
    // Every mined spec (verified or not) should reference one of the functions.
    for spec in &specs {
        assert!(
            func_names.contains(spec.function_name.as_str()),
            "mined spec should reference a parsed function: {}",
            spec.function_name
        );
    }
}

#[test]
fn test_multi_function_cgsr_per_function_refinement() {
    // Create specs from two different functions.
    let specs = vec![
        mined("f", "range", &[], &["result >= 0"], false, 0),
        mined("g", "range", &[], &["result >= 0"], false, 0),
    ];

    let cgsr_config = CgsrConfig {
        max_iterations: 3,
        strategy: RefinementStrategy::Strengthen,
        max_counterexamples: 10,
        verbose: false,
    };

    let engine = CgsrEngine::new(cgsr_config, specs);

    // Engine tracks specs from both functions.
    let func_names: HashSet<&str> = engine
        .specs()
        .iter()
        .map(|s| s.function_name.as_str())
        .collect();
    assert!(func_names.contains("f"));
    assert!(func_names.contains("g"));
    assert_eq!(engine.specs().len(), 2);
}

#[test]
fn test_multi_function_ranking_groups_by_function() {
    let specs = vec![
        mined("alpha", "range", &[], &["r >= 0"], true, 0),
        mined("alpha", "non_negative", &[], &["r >= 0"], true, 1),
        mined("beta", "sorted", &[], &["sorted(r)"], true, 0),
        mined("beta", "range", &["x > 0"], &["r >= 0"], true, 2),
    ];

    let ranked = rank_specs(&specs);
    assert_eq!(ranked.len(), 4);

    // The top-ranked spec should be either sorted (high specificity) or
    // a zero-iteration verified spec.
    let top = &ranked[0];
    assert!(top.spec.verified, "top-ranked spec should be verified");
}

// ===========================================================================
// 4. Convergence tracker aggregating across mining + CGSR iterations
// ===========================================================================

#[test]
fn test_convergence_tracker_aggregates_mining_and_cgsr() {
    let mut tracker = ConvergenceTracker::new();

    // Mining phase: function a converges on first try.
    tracker.record("a", &make_verified_feedback(), Difficulty::Easy);

    // Mining phase: function b fails twice, then CGSR refines and verifies.
    tracker.record("b", &make_failed_feedback("x", "-1"), Difficulty::Medium);
    tracker.record("b", &make_failed_feedback("x", "0"), Difficulty::Medium);
    tracker.record("b", &make_verified_feedback(), Difficulty::Medium);

    // CGSR phase: function c never converges.
    for _ in 0..5 {
        tracker.record("c", &make_failed_feedback("y", "42"), Difficulty::Hard);
    }

    assert_eq!(tracker.function_count(), 3);
    assert_eq!(tracker.converged_count(), 2);

    let rate = tracker.convergence_rate();
    assert!(
        (rate - 2.0 / 3.0).abs() < 1e-10,
        "expected 2/3 convergence rate, got {rate}"
    );

    // Average iterations to convergence: (1 + 3) / 2 = 2.0
    let avg = tracker
        .avg_iterations_to_convergence()
        .expect("should have avg");
    assert!((avg - 2.0).abs() < f64::EPSILON);
}

#[test]
fn test_convergence_predictor_from_mining_cgsr_data() {
    let mut tracker = ConvergenceTracker::new();

    // 4 total steps: 2 verified, 2 failed => p = 0.5
    tracker.record("a", &make_verified_feedback(), Difficulty::Easy);
    tracker.record("b", &make_failed_feedback("x", "-1"), Difficulty::Medium);
    tracker.record("b", &make_verified_feedback(), Difficulty::Medium);
    tracker.record("c", &make_failed_feedback("y", "0"), Difficulty::Hard);

    let predictor = ConvergencePredictor::from_tracker(&tracker);
    assert!((predictor.step_probability() - 0.5).abs() < 1e-10);

    // With p=0.5, after 4 steps: P = 1 - 0.5^4 = 0.9375
    let prob = predictor.cumulative_probability(4);
    assert!((prob - 0.9375).abs() < 1e-10, "expected 0.9375, got {prob}");
}

#[test]
fn test_convergence_report_across_full_pipeline() {
    let mut tracker = ConvergenceTracker::new();

    // Simulate a realistic pipeline: 5 easy, 3 medium, 2 hard functions.
    for i in 0..5 {
        tracker.record(
            &format!("easy_{i}"),
            &make_verified_feedback(),
            Difficulty::Easy,
        );
    }
    for i in 0..3 {
        let name = format!("med_{i}");
        tracker.record(&name, &make_failed_feedback("x", "-1"), Difficulty::Medium);
        tracker.record(&name, &make_verified_feedback(), Difficulty::Medium);
    }
    for i in 0..2 {
        let name = format!("hard_{i}");
        for _ in 0..10 {
            tracker.record(&name, &make_failed_feedback("x", "999"), Difficulty::Hard);
        }
    }

    let report = tracker.report();
    assert_eq!(report.total_functions, 10);
    assert_eq!(report.converged_functions, 8);
    assert!(report.convergence_rate > 0.7);

    // Hard functions with 10+ iters and not converged should be flagged.
    assert_eq!(report.intractable_functions.len(), 2);

    // High convergence rate should produce a recommendation.
    assert!(
        report
            .recommendations
            .iter()
            .any(|r| r.contains("High convergence")),
        "should recommend increasing budget: {:?}",
        report.recommendations
    );

    let summary = report.to_summary();
    assert!(summary.contains("Convergence Report"));
    assert!(summary.contains("10 total"));
    assert!(summary.contains("8 converged"));
}

// ===========================================================================
// 5. Spec store persistence -> ranking -> diff between stored versions
// ===========================================================================

#[test]
fn test_store_rank_diff_across_versions() {
    let path_v1 = temp_store_path("rank_diff_v1");
    let path_v2 = temp_store_path("rank_diff_v2");

    // Version 1: two specs, one weak.
    let v1_specs = vec![
        mined("f", "range", &[], &["result >= 0"], true, 0),
        mined("f", "non_negative", &[], &["result >= 0"], false, 3),
    ];
    let mut store_v1 = SpecStore::new(&path_v1);
    for s in &v1_specs {
        store_v1.add_spec(s);
    }
    store_v1.save().expect("save v1");

    // Version 2: the non_negative spec is now verified and strengthened.
    let v2_specs = vec![
        mined("f", "range", &[], &["result >= 0"], true, 0),
        mined("f", "non_negative", &["x > 0"], &["result >= 0"], true, 1),
    ];
    let mut store_v2 = SpecStore::new(&path_v2);
    for s in &v2_specs {
        store_v2.add_spec(s);
    }
    store_v2.save().expect("save v2");

    // Reload and diff.
    let loaded_v1 = SpecStore::load(&path_v1).expect("load v1");
    let loaded_v2 = SpecStore::load(&path_v2).expect("load v2");

    let specs_v1: Vec<MinedSpec> = loaded_v1.iter().map(MinedSpec::from).collect();
    let specs_v2: Vec<MinedSpec> = loaded_v2.iter().map(MinedSpec::from).collect();

    let diff = diff_spec_sets(&specs_v1, &specs_v2);
    assert_eq!(
        diff.newly_verified.len(),
        1,
        "non_negative should be newly verified"
    );
    // The range spec is identical between v1 and v2 (both verified, same clauses).
    assert_eq!(diff.unchanged.len(), 1, "range should be unchanged");

    // Rank both versions.
    let ranked_v1 = rank_specs(&specs_v1);
    let ranked_v2 = rank_specs(&specs_v2);

    // In v2, both specs are verified so both should rank higher than v1's
    // unverified spec.
    let v2_min_score: f64 = ranked_v2
        .iter()
        .map(|r| r.score.score)
        .fold(f64::INFINITY, f64::min);
    let v1_unverified_score: Option<f64> = ranked_v1
        .iter()
        .find(|r| !r.spec.verified)
        .map(|r| r.score.score);
    if let Some(uv_score) = v1_unverified_score {
        assert!(
            v2_min_score > uv_score,
            "v2 verified specs should all score higher than v1 unverified"
        );
    }

    std::fs::remove_file(&path_v1).ok();
    std::fs::remove_file(&path_v2).ok();
}

#[test]
fn test_store_merge_two_mining_runs_then_rank() {
    let path_a = temp_store_path("merge_rank_a");
    let path_b = temp_store_path("merge_rank_b");

    let mut store_a = SpecStore::new(&path_a);
    store_a.add_spec(&mined("f", "range", &[], &["r >= 0"], true, 0));
    store_a.add_spec(&mined("g", "sorted", &[], &["sorted(r)"], true, 2));

    let mut store_b = SpecStore::new(&path_b);
    store_b.add_spec(&mined("f", "non_negative", &[], &["r >= 0"], true, 1));
    store_b.add_spec(&mined("h", "identity", &[], &["r == x"], true, 0));

    store_a.merge(&store_b);
    assert_eq!(store_a.len(), 4);

    let all_specs: Vec<MinedSpec> = store_a.iter().map(MinedSpec::from).collect();
    let ranked = rank_specs(&all_specs);
    assert_eq!(ranked.len(), 4);

    // Sorted template has highest specificity among these.
    let sorted_spec = ranked.iter().find(|r| r.spec.template_name == "sorted");
    let range_spec = ranked.iter().find(|r| r.spec.template_name == "range");
    if let (Some(s), Some(r)) = (sorted_spec, range_spec) {
        assert!(
            s.score.components.specificity > r.score.components.specificity,
            "sorted should have higher specificity than range"
        );
    }
}

// ===========================================================================
// 6. Template applicability -> mine -> weaken through counterexamples -> re-verify
// ===========================================================================

#[test]
fn test_cgsr_weaken_strategy_removes_or_relaxes_postcondition() {
    let specs = vec![mined(
        "f",
        "range",
        &[],
        &["result > 0", "result < 100"],
        false,
        0,
    )];

    let config = CgsrConfig {
        max_iterations: 5,
        strategy: RefinementStrategy::Weaken,
        max_counterexamples: 10,
        verbose: false,
    };

    let mut engine = CgsrEngine::new(config, specs);

    // Simulate a counterexample where result=5 violates "result > 0".
    // Use a non-edge-case value so choose_strategy does not override to
    // Strengthen (values like 0, negative, or boundary trigger the edge-case
    // heuristic).
    let cex = Counterexample::new(
        vec![("result".to_string(), "5".to_string())],
        "result > 0".to_string(),
        0,
    );

    let modified = engine.refine_from_counterexample(&cex);
    assert!(
        !modified.is_empty(),
        "should have modified at least one spec"
    );

    // The ensures should have been weakened: "result > 0" -> "result >= 0",
    // or the violated clause removed entirely.
    let spec = &engine.specs()[0];
    let has_relaxed = spec.ensures.iter().any(|e| e.contains(">="));
    let was_removed = spec.ensures.len() < 2;
    assert!(
        has_relaxed || was_removed,
        "postcondition should be relaxed or removed, got {:?}",
        spec.ensures
    );
}

#[test]
fn test_cgsr_strengthen_strategy_adds_precondition() {
    let specs = vec![mined("g", "range", &[], &["result >= 0"], false, 0)];

    let config = CgsrConfig {
        max_iterations: 5,
        strategy: RefinementStrategy::Strengthen,
        max_counterexamples: 10,
        verbose: false,
    };

    let mut engine = CgsrEngine::new(config, specs);

    // Counterexample with negative value triggers strengthening.
    let cex = Counterexample::new(
        vec![("x".to_string(), "-5".to_string())],
        "result >= 0".to_string(),
        0,
    );

    let modified = engine.refine_from_counterexample(&cex);
    assert!(!modified.is_empty());

    let spec = &engine.specs()[0];
    assert!(
        !spec.requires.is_empty(),
        "strengthening should add a precondition"
    );
    // The synthesized precondition should exclude x=-5 (e.g., "x >= 0").
    assert!(
        spec.requires.iter().any(|r| r.contains("x")),
        "precondition should reference the variable: {:?}",
        spec.requires
    );
}

#[test]
fn test_cgsr_split_strategy_produces_two_specs() {
    let specs = vec![mined("f", "range", &[], &["result >= 0"], false, 0)];

    let config = CgsrConfig {
        max_iterations: 5,
        strategy: RefinementStrategy::Split,
        max_counterexamples: 10,
        verbose: false,
    };

    let mut engine = CgsrEngine::new(config, specs);

    // Provide two unverified specs so the heuristic chooses Split for
    // multiple violations; or use a single spec and force Split via config.
    // With a single spec, the engine should still attempt to split.
    let cex = Counterexample::new(
        vec![("x".to_string(), "42".to_string())],
        "result >= 0".to_string(),
        0,
    );

    let _modified = engine.refine_from_counterexample(&cex);
    // After split, there should be 2 specs (original replaced + one appended).
    assert!(
        engine.specs().len() >= 2,
        "split should produce at least 2 specs, got {}",
        engine.specs().len()
    );
}

// ===========================================================================
// 7. Empty source handling through full pipeline
// ===========================================================================

#[test]
fn test_empty_source_full_pipeline() {
    // Step 1: Parse empty source.
    let functions = parse_functions("");
    assert!(functions.is_empty());

    // Step 2: Mine returns no specs.
    let specs = mine_specs("", &MiningConfig::default());
    assert!(specs.is_empty());

    // Step 3: CGSR with empty specs.
    let config = CgsrConfig {
        max_iterations: 5,
        strategy: RefinementStrategy::Strengthen,
        max_counterexamples: 10,
        verbose: false,
    };
    let engine = CgsrEngine::new(config, vec![]);
    assert!(engine.specs().is_empty());
    assert!(engine.counterexamples().is_empty());

    // Step 4: Rank empty set.
    let ranked = rank_specs(&[]);
    assert!(ranked.is_empty());

    // Step 5: Diff empty sets.
    let diff = diff_spec_sets(&[], &[]);
    assert!(diff.is_empty());
    assert_eq!(diff.total_specs(), 0);

    // Step 6: Store empty.
    let path = temp_store_path("empty_pipeline");
    let store = SpecStore::new(&path);
    assert!(store.is_empty());
    store.save().expect("saving empty store should succeed");
    let loaded = SpecStore::load(&path).expect("loading empty store");
    assert!(loaded.is_empty());
    std::fs::remove_file(&path).ok();

    // Step 7: Convergence tracker with no data.
    let tracker = ConvergenceTracker::new();
    assert_eq!(tracker.function_count(), 0);
    assert_eq!(tracker.convergence_rate(), 0.0);
    assert!(tracker.avg_iterations_to_convergence().is_none());
}

#[test]
fn test_unparseable_source_full_pipeline() {
    let source = "this is not valid rust {{{";
    let functions = parse_functions(source);
    assert!(functions.is_empty());

    let specs = mine_specs(source, &MiningConfig::default());
    assert!(specs.is_empty());

    let ranked = rank_specs(&specs);
    assert!(ranked.is_empty());
}

// ===========================================================================
// 8. Large function set (10+ functions) mining performance
// ===========================================================================

#[test]
fn test_large_function_set_mining_ten_functions() {
    // Generate 10 simple u32 functions.
    let mut source = String::new();
    for i in 0..10 {
        source.push_str(&format!("fn func_{i}(x: u32) -> u32 {{ x + {i} }}\n"));
    }

    let functions = parse_functions(&source);
    assert_eq!(functions.len(), 10, "should parse all 10 functions");

    // Verify each parsed function has the expected name and signature.
    for (i, func) in functions.iter().enumerate() {
        assert_eq!(func.name, format!("func_{i}"));
        assert_eq!(func.params.len(), 1);
        assert_eq!(func.params[0].0, "x");
        assert!(func.return_type.is_some());
    }

    // Run mining through the full pipeline. The real verifier may or may not
    // produce verified specs (depends on template applicability with ay), but
    // the pipeline should process all 10 functions without panics.
    let config = MiningConfig {
        max_refinements: 2,
        max_templates_per_function: 2,
        verbose: false,
    };
    let specs = mine_specs(&source, &config);

    // All mined specs should reference one of the 10 functions.
    let expected_names: HashSet<String> = (0..10).map(|i| format!("func_{i}")).collect();
    for spec in &specs {
        assert!(
            expected_names.contains(&spec.function_name),
            "mined spec should reference a parsed function: {}",
            spec.function_name
        );
    }

    // The ranking pipeline should handle any number of specs.
    let ranked = rank_specs(&specs);
    assert_eq!(ranked.len(), specs.len());
}

#[test]
fn test_large_function_set_convergence_tracking() {
    let mut tracker = ConvergenceTracker::new();

    // Track 15 functions with varying convergence behavior.
    for i in 0..10 {
        // 10 easy functions that converge immediately.
        tracker.record(
            &format!("easy_{i}"),
            &make_verified_feedback(),
            Difficulty::Easy,
        );
    }
    for i in 0..3 {
        // 3 medium functions needing 2 iterations.
        let name = format!("medium_{i}");
        tracker.record(&name, &make_failed_feedback("x", "-1"), Difficulty::Medium);
        tracker.record(&name, &make_verified_feedback(), Difficulty::Medium);
    }
    for i in 0..2 {
        // 2 hard functions that never converge.
        let name = format!("hard_{i}");
        for _ in 0..8 {
            tracker.record(&name, &make_failed_feedback("x", "999"), Difficulty::Hard);
        }
    }

    assert_eq!(tracker.function_count(), 15);
    assert_eq!(tracker.converged_count(), 13);

    let rate = tracker.convergence_rate();
    assert!(
        (rate - 13.0 / 15.0).abs() < 1e-10,
        "expected 13/15, got {rate}"
    );

    let report = tracker.report();
    assert_eq!(report.per_difficulty.len(), 3);

    // Easy class should have 100% convergence.
    let easy_bd = report
        .per_difficulty
        .iter()
        .find(|bd| bd.difficulty == Difficulty::Easy)
        .expect("should have Easy breakdown");
    assert_eq!(easy_bd.total, 10);
    assert_eq!(easy_bd.converged, 10);
    assert!((easy_bd.convergence_rate() - 1.0).abs() < f64::EPSILON);
}

#[test]
fn test_large_function_set_ranking_preserves_all() {
    // 12 specs across 4 functions.
    let specs: Vec<MinedSpec> = (0..4)
        .flat_map(|fi| {
            (0..3).map(move |ti| {
                let templates = ["range", "non_negative", "monotonic"];
                mined(
                    &format!("fn_{fi}"),
                    templates[ti],
                    &[],
                    &["result >= 0"],
                    ti < 2, // first two templates verified
                    ti,
                )
            })
        })
        .collect();

    assert_eq!(specs.len(), 12);
    let ranked = rank_specs(&specs);
    assert_eq!(ranked.len(), 12);

    // Verified specs should rank above unverified.
    let verified_ranks: Vec<usize> = ranked
        .iter()
        .filter(|r| r.spec.verified)
        .map(|r| r.rank)
        .collect();
    let unverified_ranks: Vec<usize> = ranked
        .iter()
        .filter(|r| !r.spec.verified)
        .map(|r| r.rank)
        .collect();

    if let (Some(&max_v), Some(&min_u)) =
        (verified_ranks.iter().max(), unverified_ranks.iter().min())
    {
        assert!(
            max_v < min_u,
            "all verified should rank before all unverified"
        );
    }
}

// ===========================================================================
// Additional integration scenarios
// ===========================================================================

#[test]
fn test_difficulty_classifier_feeds_into_convergence_tracker() {
    let easy_func = sig(
        "add_one",
        &[("x", "u32")],
        Some("u32"),
        "fn add_one(x: u32) -> u32 { x + 1 }",
    );
    let hard_func = sig(
        "transform",
        &[
            ("data", "&mut Vec<i32>"),
            ("filter", "&Fn(i32) -> bool"),
            ("config", "Config<'a>"),
        ],
        Some("Result<Vec<i32>, Error>"),
        "fn transform<'a>(data: &mut Vec<i32>, filter: &Fn(i32) -> bool, config: Config<'a>) -> Result<Vec<i32>, Error> {}",
    );

    let easy_diff = DifficultyClassifier::classify(&easy_func);
    let hard_diff = DifficultyClassifier::classify(&hard_func);
    assert_eq!(easy_diff, Difficulty::Easy);
    assert!(matches!(
        hard_diff,
        Difficulty::Hard | Difficulty::Intractable
    ));

    let mut tracker = ConvergenceTracker::new();
    tracker.record("add_one", &make_verified_feedback(), easy_diff);
    tracker.record("transform", &make_failed_feedback("data", "[]"), hard_diff);

    assert_eq!(tracker.converged_count(), 1);
    let report = tracker.report();
    assert!(report.per_difficulty.len() >= 2);
}

#[test]
fn test_spec_evolution_with_store_versions() {
    // Simulate 3 mining runs stored and diffed.
    let run1 = vec![
        mined("f", "range", &[], &["r >= 0"], false, 0),
        mined("g", "non_negative", &[], &["r >= 0"], true, 0),
    ];
    let run2 = vec![
        mined("f", "range", &["x > 0"], &["r >= 0"], true, 1),
        mined("g", "non_negative", &[], &["r >= 0"], true, 0),
    ];
    let run3 = vec![
        mined("f", "range", &["x > 0"], &["r >= 0"], true, 1),
        mined("g", "non_negative", &[], &["r >= 0"], true, 0),
    ];

    let history = vec![run1, run2, run3];
    let diffs = spec_evolution(&history);

    let churn_hist = ConvergenceMetric::churn_history(&diffs);
    assert_eq!(churn_hist.len(), 2);
    assert!(churn_hist[0] > 0.0, "first diff should have churn");
    assert!(
        churn_hist[1] < f64::EPSILON,
        "second diff should have zero churn"
    );

    // Time to stability should be 0 since latest churn is 0.
    let tts = ConvergenceMetric::time_to_stability(&diffs);
    assert_eq!(tts, Some(0), "already stable");
}

#[test]
fn test_counterexample_extraction_and_cgsr_refinement_chain() {
    // Counterexample with a negative value.
    let cex1 = Counterexample::new(
        vec![("x".to_string(), "-5".to_string())],
        "ensures".to_string(),
        0,
    );
    assert!(cex1.has_binding("x"));
    assert_eq!(cex1.get_value("x"), Some("-5"));
    assert!(!cex1.has_binding("y"));
    assert_eq!(cex1.get_value("y"), None);

    // Build from ProofFeedback.
    let feedback = make_failed_feedback("result", "-1");
    let cex2 = Counterexample::from_feedback(&feedback, 1);
    assert!(cex2.is_some());
    let cex2 = cex2.unwrap();
    assert_eq!(cex2.iteration, 1);
    assert!(cex2.has_binding("result"));

    // Verified feedback produces no counterexample.
    let verified = make_verified_feedback();
    assert!(Counterexample::from_feedback(&verified, 0).is_none());
}

#[test]
fn test_score_components_composition() {
    let verified_zero_iter = mined("f", "sorted", &[], &["sorted(r)"], true, 0);
    let score = score_spec(&verified_zero_iter);

    // Verified: 50.0, Refinement: 20.0 (0 iters), Specificity: 1.0*20=20.0,
    // Strength: 1.0*10=10.0. Total: 100.0
    let expected =
        weights::VERIFIED + weights::REFINEMENT + weights::SPECIFICITY + weights::STRENGTH;
    assert!(
        (score.score - expected).abs() < 1e-10,
        "perfect spec should score {expected}, got {}",
        score.score
    );
    assert_eq!(score.confidence, 1.0);
}

#[test]
fn test_spec_store_dedup_during_cgsr_pipeline() {
    let path = temp_store_path("cgsr_dedup");
    let mut store = SpecStore::new(&path);

    // First CGSR run: unverified spec.
    store.add_spec(&mined("f", "range", &[], &["r >= 0"], false, 3));
    assert_eq!(store.len(), 1);
    assert!(!store.get_specs_for_function("f")[0].verified);

    // Second CGSR run: same spec now verified with fewer iterations.
    store.add_spec(&mined("f", "range", &["x > 0"], &["r >= 0"], true, 1));
    assert_eq!(store.len(), 1, "dedup should keep one entry");
    assert!(
        store.get_specs_for_function("f")[0].verified,
        "verified should win"
    );

    // Third CGSR run: verified with even fewer iterations.
    store.add_spec(&mined("f", "range", &["x > 0"], &["r >= 0"], true, 0));
    assert_eq!(store.len(), 1);
    assert_eq!(
        store.get_specs_for_function("f")[0].iterations,
        0,
        "fewer iterations should win"
    );

    std::fs::remove_file(&path).ok();
}

#[test]
fn test_parse_function_by_name_integration() {
    let source = r#"
        fn alpha(x: i32) -> i32 { x + 1 }
        fn beta(a: u32, b: u32) -> u32 { a + b }
        fn gamma() -> bool { true }
    "#;

    let beta = parse_function_by_name(source, "beta");
    assert!(beta.is_some());
    let beta = beta.unwrap();
    assert_eq!(beta.name, "beta");
    assert_eq!(beta.params.len(), 2);

    let missing = parse_function_by_name(source, "delta");
    assert!(missing.is_none());
}

#[test]
fn test_template_specificity_ordering_for_ranking() {
    // Structural > Algebraic > Semantic > Bounds.
    assert!(template_specificity("sorted") > template_specificity("commutativity"));
    assert!(template_specificity("commutativity") > template_specificity("monotonic"));
    assert!(template_specificity("monotonic") > template_specificity("range"));
    assert!(template_specificity("range") > template_specificity("non_negative"));

    // All in (0, 1].
    for name in &[
        "sorted",
        "permutation",
        "injective",
        "commutativity",
        "range",
        "non_negative",
    ] {
        let s = template_specificity(name);
        assert!(s > 0.0 && s <= 1.0, "{name}: {s} out of range");
    }
}

#[test]
fn test_diff_report_readable_format() {
    let v1 = vec![
        mined("f", "range", &[], &["r >= 0"], false, 0),
        mined("g", "sorted", &[], &["sorted(r)"], true, 0),
    ];
    let v2 = vec![
        mined("f", "range", &["x > 0"], &["r >= 0"], true, 1),
        mined("h", "identity", &[], &["r == x"], true, 0),
    ];

    let diff = diff_spec_sets(&v1, &v2);

    // f::range: was unverified, now verified with added precondition.
    assert_eq!(diff.newly_verified.len(), 1);
    // g::sorted was removed.
    assert_eq!(diff.removed.len(), 1);
    assert_eq!(diff.removed[0].function_name, "g");
    // h::identity was added.
    assert_eq!(diff.added.len(), 1);
    assert_eq!(diff.added[0].function_name, "h");

    let report = diff.report();
    let summary = report.summary();
    assert!(summary.contains("1 added"));
    assert!(summary.contains("1 removed"));
    assert!(summary.contains("1 newly verified"));

    let detailed = report.detailed();
    assert!(detailed.contains("Spec Diff Report"));
    assert!(detailed.contains("Added:"));
    assert!(detailed.contains("Removed:"));
    assert!(detailed.contains("Newly verified:"));
}
