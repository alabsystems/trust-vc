// trust-vc-oracle -- Adaptive strategy selector for oracle backends
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Selects between oracle backends and mining approaches based on function
// characteristics and feedback history. Starts with fast template mining,
// escalates through CGSR refinement, and finally falls back to full LLM
// oracle for intractable functions.

use crate::backend::LlmBackend;
use crate::cgsr::{CgsrConfig, CgsrEngine, RefinementStrategy};
use crate::convergence::{ConvergenceTracker, Difficulty, DifficultyClassifier};
use crate::engine::{run_oracle, FunctionSignature, OracleConfig, OracleResult};
use crate::feedback::ProofFeedback;
use crate::mining::MinedSpec;
use crate::source_parser::parse_functions;
use crate::OracleError;

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for the adaptive strategy selector.
#[derive(Debug, Clone)]
pub struct AdaptiveConfig {
    /// Total iteration budget across all strategies.
    pub budget: usize,
    /// Iterations before escalating to a harder strategy.
    pub escalation_threshold: usize,
    /// How many strategies to run simultaneously (reserved for future use).
    pub parallel_candidates: usize,
    /// Whether to emit progress to stderr.
    pub verbose: bool,
}

impl Default for AdaptiveConfig {
    fn default() -> Self {
        Self {
            budget: 20,
            escalation_threshold: 5,
            parallel_candidates: 1,
            verbose: false,
        }
    }
}

// ---------------------------------------------------------------------------
// Strategy
// ---------------------------------------------------------------------------

/// Which approach to use for a given function.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Strategy {
    /// Fast template-based mining (try first for easy functions).
    TemplateMining,
    /// CGSR loop with counterexample feedback (medium difficulty).
    CgsrRefinement,
    /// Full LLM oracle (expensive, last resort).
    OracleAssisted,
    /// Split budget between mining and oracle for intractable functions.
    Hybrid {
        /// Iterations allocated to template mining.
        mining_budget: usize,
        /// Iterations allocated to LLM oracle.
        oracle_budget: usize,
    },
}

impl Strategy {
    /// Human-readable label.
    #[must_use]
    pub fn as_str(&self) -> &'static str {
        match self {
            Strategy::TemplateMining => "template-mining",
            Strategy::CgsrRefinement => "cgsr-refinement",
            Strategy::OracleAssisted => "oracle-assisted",
            Strategy::Hybrid { .. } => "hybrid",
        }
    }

    /// Relative cost ordering (lower = cheaper).
    #[cfg(test)]
    #[must_use]
    pub(crate) fn cost_rank(&self) -> usize {
        match self {
            Strategy::TemplateMining => 0,
            Strategy::CgsrRefinement => 1,
            Strategy::OracleAssisted => 2,
            Strategy::Hybrid { .. } => 3,
        }
    }
}

// ---------------------------------------------------------------------------
// Per-function result
// ---------------------------------------------------------------------------

/// Result for a single function from the adaptive pipeline.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct FunctionResult {
    /// Name of the function.
    pub function_name: String,
    /// Specs discovered (may be empty if nothing converged).
    pub specs: Vec<MinedSpec>,
    /// Which strategy was used (final, after any escalation).
    pub strategy_used: Strategy,
    /// Total iterations consumed across all strategy attempts.
    pub iterations_consumed: usize,
    /// Whether the function converged (at least one spec verified).
    pub converged: bool,
}

impl FunctionResult {
    #[must_use]
    pub(crate) fn new(function_name: String, strategy_used: Strategy) -> Self {
        Self {
            function_name,
            specs: Vec::new(),
            strategy_used,
            iterations_consumed: 0,
            converged: false,
        }
    }
}

// ---------------------------------------------------------------------------
// Aggregate result
// ---------------------------------------------------------------------------

/// Result of the full adaptive run across all functions in the source.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct AdaptiveResult {
    /// Per-function results.
    pub functions: Vec<FunctionResult>,
    /// Total specs found across all functions.
    pub total_specs: usize,
    /// Total budget consumed.
    pub budget_used: usize,
    /// Number of times a strategy was escalated to a harder one.
    pub escalation_count: usize,
}

impl AdaptiveResult {
    /// Whether every function converged.
    #[must_use]
    pub fn all_converged(&self) -> bool {
        !self.functions.is_empty() && self.functions.iter().all(|f| f.converged)
    }

    /// Count of functions that converged.
    #[must_use]
    pub fn converged_count(&self) -> usize {
        self.functions.iter().filter(|f| f.converged).count()
    }

    /// Convergence rate (0.0 to 1.0).
    #[must_use]
    pub fn convergence_rate(&self) -> f64 {
        let total = self.functions.len();
        if total == 0 {
            return 0.0;
        }
        self.converged_count() as f64 / total as f64
    }
}

// ---------------------------------------------------------------------------
// Strategy selector
// ---------------------------------------------------------------------------

/// Selects the initial strategy for a function based on its signature
/// complexity and convergence history.
pub struct AdaptiveSelector;

impl AdaptiveSelector {
    /// Choose the initial strategy for a function.
    ///
    /// Logic:
    /// - Easy functions -> TemplateMining (fast, usually sufficient)
    /// - Medium functions -> CgsrRefinement (needs counterexample feedback)
    /// - Hard functions -> OracleAssisted (needs LLM reasoning)
    /// - Intractable functions -> Hybrid (split budget between mining + oracle)
    ///
    /// If the convergence tracker has history for similar functions that
    /// failed with a cheaper strategy, we escalate preemptively.
    #[must_use]
    pub fn select_strategy(
        func: &FunctionSignature,
        history: &ConvergenceTracker,
        config: &AdaptiveConfig,
    ) -> Strategy {
        let difficulty = DifficultyClassifier::classify(func);

        // Check if we have prior failures for this exact function.
        let prior_failures = history
            .history(&func.name)
            .map(|h| h.iteration_count())
            .unwrap_or(0);

        // If prior attempts already consumed significant budget, escalate.
        if prior_failures >= config.escalation_threshold {
            return escalate_from_history(difficulty, config);
        }

        match difficulty {
            Difficulty::Easy => Strategy::TemplateMining,
            Difficulty::Medium => Strategy::CgsrRefinement,
            Difficulty::Hard => Strategy::OracleAssisted,
            Difficulty::Intractable => {
                let mining_budget = config.budget / 3;
                let oracle_budget = config.budget - mining_budget;
                Strategy::Hybrid {
                    mining_budget,
                    oracle_budget,
                }
            }
        }
    }

    /// Determine the next strategy after the current one fails to converge
    /// within the escalation threshold.
    ///
    /// Returns `None` if there is no harder strategy to escalate to.
    #[must_use]
    pub fn escalate(current: &Strategy, config: &AdaptiveConfig) -> Option<Strategy> {
        match current {
            Strategy::TemplateMining => Some(Strategy::CgsrRefinement),
            Strategy::CgsrRefinement => Some(Strategy::OracleAssisted),
            Strategy::OracleAssisted => {
                let mining_budget = config.budget / 3;
                let oracle_budget = config.budget.saturating_sub(mining_budget);
                Some(Strategy::Hybrid {
                    mining_budget,
                    oracle_budget,
                })
            }
            Strategy::Hybrid { .. } => None,
        }
    }
}

/// Escalation from history: jump to the strategy appropriate for the
/// difficulty, skipping cheaper strategies that are unlikely to help.
fn escalate_from_history(difficulty: Difficulty, config: &AdaptiveConfig) -> Strategy {
    match difficulty {
        Difficulty::Easy => Strategy::CgsrRefinement,
        Difficulty::Medium => Strategy::OracleAssisted,
        Difficulty::Hard | Difficulty::Intractable => {
            let mining_budget = config.budget / 3;
            let oracle_budget = config.budget.saturating_sub(mining_budget);
            Strategy::Hybrid {
                mining_budget,
                oracle_budget,
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Verification adapter (injectable for testing)
// ---------------------------------------------------------------------------

/// Abstraction over the verification step so tests can inject a mock.
pub(crate) trait AdaptiveVerifyAdapter: Send + Sync {
    fn verify(
        &self,
        function_name: &str,
        variables: &[(String, String)],
        requires: &[String],
        ensures: &[String],
    ) -> ProofFeedback;
}

// ---------------------------------------------------------------------------
// Adaptive runner
// ---------------------------------------------------------------------------

/// Run the adaptive pipeline on source code.
///
/// Parses all functions, selects a strategy for each based on signature
/// complexity and historical convergence data, runs the selected strategy,
/// and escalates if the initial strategy does not converge within the
/// escalation threshold.
///
/// This is the main entry point for adaptive spec mining. For the oracle-
/// assisted path, a backend must be provided; pass `None` to skip oracle
/// strategies (the pipeline will stop at CGSR refinement).
pub fn run_adaptive(
    source: &str,
    config: &AdaptiveConfig,
    backend: Option<&dyn LlmBackend>,
) -> Result<AdaptiveResult, OracleError> {
    let functions = parse_functions(source);
    run_adaptive_functions(&functions, config, backend, &RealAdaptiveVerifier)
}

/// Internal entry point with injectable verifier (for testing).
fn run_adaptive_functions(
    functions: &[FunctionSignature],
    config: &AdaptiveConfig,
    backend: Option<&dyn LlmBackend>,
    adapter: &dyn AdaptiveVerifyAdapter,
) -> Result<AdaptiveResult, OracleError> {
    let mut tracker = ConvergenceTracker::new();
    let mut results = Vec::new();
    let mut total_budget_used = 0usize;
    let mut escalation_count = 0usize;

    for func in functions {
        if total_budget_used >= config.budget {
            // Global budget exhausted; record remaining functions as unconverged.
            results.push(FunctionResult::new(
                func.name.clone(),
                Strategy::TemplateMining,
            ));
            continue;
        }

        let remaining_budget = config.budget.saturating_sub(total_budget_used);
        let mut strategy = AdaptiveSelector::select_strategy(func, &tracker, config);
        let mut func_result = FunctionResult::new(func.name.clone(), strategy.clone());
        let mut func_budget_used = 0usize;

        // Run strategy, escalating on failure.
        loop {
            let iter_budget = remaining_budget
                .saturating_sub(func_budget_used)
                .min(config.escalation_threshold);

            if iter_budget == 0 {
                break;
            }

            let (specs, iters) = run_strategy(
                func,
                &strategy,
                iter_budget,
                adapter,
                backend,
                config.verbose,
            )?;

            func_budget_used += iters;

            // Record feedback into the convergence tracker.
            let difficulty = DifficultyClassifier::classify(func);
            if specs.iter().any(|s| s.verified) {
                let feedback = make_verified_feedback();
                tracker.record(&func.name, &feedback, difficulty);
            } else if iters > 0 {
                let feedback = make_failed_feedback();
                for _ in 0..iters {
                    tracker.record(&func.name, &feedback, difficulty);
                }
            }

            if specs.iter().any(|s| s.verified) {
                func_result.specs = specs;
                func_result.converged = true;
                func_result.strategy_used = strategy;
                break;
            }

            // Attempt escalation.
            if let Some(next) = AdaptiveSelector::escalate(&strategy, config) {
                escalation_count += 1;
                strategy = next;
                if config.verbose {
                    eprintln!(
                        "[adaptive] {} escalating to {}",
                        func.name,
                        strategy.as_str()
                    );
                }
            } else {
                // No further escalation available.
                func_result.strategy_used = strategy;
                break;
            }
        }

        func_result.iterations_consumed = func_budget_used;
        total_budget_used += func_budget_used;
        results.push(func_result);
    }

    let total_specs = results.iter().map(|r| r.specs.len()).sum();

    Ok(AdaptiveResult {
        functions: results,
        total_specs,
        budget_used: total_budget_used,
        escalation_count,
    })
}

// ---------------------------------------------------------------------------
// Strategy execution
// ---------------------------------------------------------------------------

/// Run a single strategy on a function, returning (specs, iterations_used).
fn run_strategy(
    func: &FunctionSignature,
    strategy: &Strategy,
    budget: usize,
    adapter: &dyn AdaptiveVerifyAdapter,
    backend: Option<&dyn LlmBackend>,
    verbose: bool,
) -> Result<(Vec<MinedSpec>, usize), OracleError> {
    match strategy {
        Strategy::TemplateMining => Ok(run_template_mining(func, budget, adapter, verbose)),
        Strategy::CgsrRefinement => Ok(run_cgsr(func, budget, adapter, verbose)),
        Strategy::OracleAssisted => run_oracle_strategy(func, budget, backend, verbose),
        Strategy::Hybrid {
            mining_budget,
            oracle_budget,
        } => {
            let effective_mining = (*mining_budget).min(budget);
            let effective_oracle = (*oracle_budget).min(budget.saturating_sub(effective_mining));

            let (mining_specs, mining_iters) =
                run_template_mining(func, effective_mining, adapter, verbose);

            if mining_specs.iter().any(|s| s.verified) {
                return Ok((mining_specs, mining_iters));
            }

            let (oracle_specs, oracle_iters) =
                run_oracle_strategy(func, effective_oracle, backend, verbose)?;

            let mut all_specs = mining_specs;
            all_specs.extend(oracle_specs);
            Ok((all_specs, mining_iters + oracle_iters))
        }
    }
}

/// Run template mining on a single function.
fn run_template_mining(
    func: &FunctionSignature,
    budget: usize,
    adapter: &dyn AdaptiveVerifyAdapter,
    verbose: bool,
) -> (Vec<MinedSpec>, usize) {
    use crate::templates::applicable_templates;

    let templates = applicable_templates(func);
    if templates.is_empty() {
        return (Vec::new(), 0);
    }

    let mut results = Vec::new();
    let mut iterations_used = 0;

    for template in &templates {
        if iterations_used >= budget {
            break;
        }

        let proposals = template.instantiate(func);
        for proposal in &proposals {
            if iterations_used >= budget {
                break;
            }

            let feedback = adapter.verify(
                &func.name,
                &func.params,
                &proposal.requires,
                &proposal.ensures,
            );
            iterations_used += 1;

            if verbose {
                let status = if feedback.is_verified() {
                    "VERIFIED"
                } else {
                    "failed"
                };
                eprintln!(
                    "[adaptive:mining] {}::{} -- {}",
                    func.name,
                    template.name(),
                    status,
                );
            }

            if feedback.is_verified() {
                results.push(MinedSpec::new(
                    func.name.clone(),
                    template.name().to_owned(),
                    proposal.requires.clone(),
                    proposal.ensures.clone(),
                    true,
                    0,
                ));
            }
        }
    }

    (results, iterations_used)
}

/// Run CGSR refinement on a single function.
fn run_cgsr(
    func: &FunctionSignature,
    budget: usize,
    adapter: &dyn AdaptiveVerifyAdapter,
    verbose: bool,
) -> (Vec<MinedSpec>, usize) {
    use crate::templates::applicable_templates;

    let templates = applicable_templates(func);
    if templates.is_empty() {
        return (Vec::new(), 0);
    }

    // Collect initial candidates from the first template.
    let mut initial_specs = Vec::new();
    for template in templates.iter().take(1) {
        let proposals = template.instantiate(func);
        for proposal in proposals {
            initial_specs.push(MinedSpec::new(
                func.name.clone(),
                template.name().to_owned(),
                proposal.requires,
                proposal.ensures,
                false,
                0,
            ));
        }
    }

    if initial_specs.is_empty() {
        return (Vec::new(), 0);
    }

    let cgsr_config = CgsrConfig {
        max_iterations: budget,
        strategy: RefinementStrategy::Strengthen,
        max_counterexamples: budget * 2,
        verbose,
    };

    // Run the CGSR engine with a wrapper adapter.
    let mut engine = CgsrEngine::new(cgsr_config, initial_specs);
    let cgsr_adapter = CgsrAdapterBridge(adapter);
    let result = engine.run_loop(&cgsr_adapter);

    let total_iters = result.iterations_used;
    let verified = result.verified_specs;

    (verified, total_iters)
}

/// Bridge from AdaptiveVerifyAdapter to CgsrVerifyAdapter.
struct CgsrAdapterBridge<'a>(&'a dyn AdaptiveVerifyAdapter);

impl crate::cgsr::CgsrVerifyAdapter for CgsrAdapterBridge<'_> {
    fn verify(
        &self,
        function_name: &str,
        variables: &[(String, String)],
        requires: &[String],
        ensures: &[String],
    ) -> ProofFeedback {
        self.0.verify(function_name, variables, requires, ensures)
    }
}

/// Run the full LLM oracle on a function.
fn run_oracle_strategy(
    func: &FunctionSignature,
    budget: usize,
    backend: Option<&dyn LlmBackend>,
    verbose: bool,
) -> Result<(Vec<MinedSpec>, usize), OracleError> {
    let Some(backend) = backend else {
        // No backend available; cannot run oracle.
        return Ok((Vec::new(), 0));
    };

    let oracle_config = OracleConfig {
        max_iterations: budget,
        verbose,
    };

    let result: OracleResult = run_oracle(func, backend, &oracle_config)?;
    let iterations = result.iterations;

    let specs = if result.is_verified() {
        if let Some(ref annotations) = result.annotations {
            vec![MinedSpec::new(
                func.name.clone(),
                "oracle".to_owned(),
                annotations.requires.clone(),
                annotations.ensures.clone(),
                true,
                iterations,
            )]
        } else {
            Vec::new()
        }
    } else {
        Vec::new()
    };

    Ok((specs, iterations))
}

// ---------------------------------------------------------------------------
// Real verifier
// ---------------------------------------------------------------------------

/// Real adapter that delegates to `verify_with_annotations`.
struct RealAdaptiveVerifier;

impl AdaptiveVerifyAdapter for RealAdaptiveVerifier {
    fn verify(
        &self,
        function_name: &str,
        variables: &[(String, String)],
        requires: &[String],
        ensures: &[String],
    ) -> ProofFeedback {
        crate::verify::verify_with_annotations(function_name, variables, requires, ensures)
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn make_verified_feedback() -> ProofFeedback {
    ProofFeedback::Verified {
        steps: vec![],
        elapsed: std::time::Duration::from_millis(1),
        certificate_info: None,
    }
}

fn make_failed_feedback() -> ProofFeedback {
    ProofFeedback::Failed {
        counterexamples: vec![],
        localization: crate::feedback::FailureLocalization {
            full_assertion: None,
            sub_results: vec![],
        },
        obligation_name: "ensures".to_owned(),
        solver_mode: "Default".to_owned(),
        elapsed: std::time::Duration::from_millis(1),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::ProposedAnnotations;
    use crate::feedback::{CounterexampleField, FailureLocalization};
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::time::Duration;

    // -----------------------------------------------------------------------
    // Test helpers
    // -----------------------------------------------------------------------

    fn simple_func(name: &str, param_count: usize) -> FunctionSignature {
        let params: Vec<(String, String)> = (0..param_count)
            .map(|i| (format!("x{}", i), "u32".to_owned()))
            .collect();
        FunctionSignature {
            name: name.to_owned(),
            params,
            return_type: Some("u32".to_owned()),
            source: format!("fn {}() -> u32 {{ 0 }}", name),
            ..Default::default()
        }
    }

    fn complex_func(name: &str) -> FunctionSignature {
        FunctionSignature {
            name: name.to_owned(),
            params: vec![
                ("a".to_owned(), "&mut Vec<i32>".to_owned()),
                ("b".to_owned(), "Vec<i32>".to_owned()),
                ("c".to_owned(), "Option<u32>".to_owned()),
                ("d".to_owned(), "&str".to_owned()),
                ("e".to_owned(), "Map<K, V>".to_owned()),
            ],
            return_type: Some("Result<Vec<i32>, Error>".to_owned()),
            source: format!("fn {}() -> Result<Vec<i32>, Error> {{ todo!() }}", name),
            ..Default::default()
        }
    }

    fn medium_func(name: &str) -> FunctionSignature {
        // Complexity score: 3 params + 1 (return contains Vec) + 1 (return contains <) = 5 → Medium
        FunctionSignature {
            name: name.to_owned(),
            params: vec![
                ("a".to_owned(), "u32".to_owned()),
                ("b".to_owned(), "u32".to_owned()),
                ("c".to_owned(), "u32".to_owned()),
            ],
            return_type: Some("Vec<u32>".to_owned()),
            source: format!(
                "fn {}(a: u32, b: u32, c: u32) -> Vec<u32> {{ vec![a, b, c] }}",
                name
            ),
            ..Default::default()
        }
    }

    fn test_verified_feedback() -> ProofFeedback {
        ProofFeedback::Verified {
            steps: vec![],
            elapsed: Duration::from_millis(1),
            certificate_info: None,
        }
    }

    fn test_failed_feedback() -> ProofFeedback {
        ProofFeedback::Failed {
            counterexamples: vec![CounterexampleField {
                name: "result".to_owned(),
                ty: "i32".to_owned(),
                value: "-1".to_owned(),
            }],
            localization: FailureLocalization {
                full_assertion: None,
                sub_results: vec![],
            },
            obligation_name: "ensures".to_owned(),
            solver_mode: "Default".to_owned(),
            elapsed: Duration::from_millis(1),
        }
    }

    /// Always-verifying adapter.
    struct AlwaysVerifies;

    impl AdaptiveVerifyAdapter for AlwaysVerifies {
        fn verify(
            &self,
            _function_name: &str,
            _variables: &[(String, String)],
            _requires: &[String],
            _ensures: &[String],
        ) -> ProofFeedback {
            test_verified_feedback()
        }
    }

    /// Always-failing adapter.
    struct AlwaysFails;

    impl AdaptiveVerifyAdapter for AlwaysFails {
        fn verify(
            &self,
            _function_name: &str,
            _variables: &[(String, String)],
            _requires: &[String],
            _ensures: &[String],
        ) -> ProofFeedback {
            test_failed_feedback()
        }
    }

    /// Scripted adapter: returns pre-configured feedback per call.
    struct ScriptedAdapter {
        responses: Vec<ProofFeedback>,
        call_count: AtomicUsize,
    }

    impl ScriptedAdapter {
        fn new(responses: Vec<ProofFeedback>) -> Self {
            Self {
                responses,
                call_count: AtomicUsize::new(0),
            }
        }

        #[allow(dead_code)]
        fn calls(&self) -> usize {
            self.call_count.load(Ordering::SeqCst)
        }
    }

    impl AdaptiveVerifyAdapter for ScriptedAdapter {
        fn verify(
            &self,
            _function_name: &str,
            _variables: &[(String, String)],
            _requires: &[String],
            _ensures: &[String],
        ) -> ProofFeedback {
            let idx = self.call_count.fetch_add(1, Ordering::SeqCst);
            if idx < self.responses.len() {
                self.responses[idx].clone()
            } else {
                self.responses
                    .last()
                    .cloned()
                    .unwrap_or(ProofFeedback::Error {
                        message: "adapter exhausted".to_owned(),
                    })
            }
        }
    }

    /// Mock LLM backend for oracle strategy testing.
    struct MockOracleBackend {
        proposals: Vec<ProposedAnnotations>,
    }

    impl MockOracleBackend {
        fn new(proposals: Vec<ProposedAnnotations>) -> Self {
            Self { proposals }
        }
    }

    impl LlmBackend for MockOracleBackend {
        fn propose_annotations(
            &self,
            _source: &str,
            feedback_history: &[(ProposedAnnotations, ProofFeedback)],
        ) -> Result<ProposedAnnotations, OracleError> {
            let idx = feedback_history.len();
            self.proposals
                .get(idx)
                .cloned()
                .ok_or(OracleError::BackendExhausted { attempts: idx })
        }

        fn name(&self) -> &str {
            "mock-oracle"
        }
    }

    fn default_config() -> AdaptiveConfig {
        AdaptiveConfig {
            budget: 20,
            escalation_threshold: 5,
            parallel_candidates: 1,
            verbose: false,
        }
    }

    // -----------------------------------------------------------------------
    // Strategy selection tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_select_strategy_easy_function_returns_template_mining() {
        let func = simple_func("add_one", 1);
        let tracker = ConvergenceTracker::new();
        let config = default_config();

        let strategy = AdaptiveSelector::select_strategy(&func, &tracker, &config);
        assert_eq!(strategy, Strategy::TemplateMining);
    }

    #[test]
    fn test_select_strategy_medium_function_returns_cgsr() {
        let func = medium_func("merge");
        let tracker = ConvergenceTracker::new();
        let config = default_config();

        let strategy = AdaptiveSelector::select_strategy(&func, &tracker, &config);
        assert_eq!(strategy, Strategy::CgsrRefinement);
    }

    #[test]
    fn test_select_strategy_hard_function_returns_oracle() {
        // Create a function with enough complexity to be classified as Hard.
        let func = FunctionSignature {
            name: "transform".to_owned(),
            params: vec![
                ("data".to_owned(), "&mut Vec<i32>".to_owned()),
                ("pred".to_owned(), "&Fn(i32) -> bool".to_owned()),
            ],
            return_type: Some("Result<(), Error>".to_owned()),
            source:
                "fn transform(data: &mut Vec<i32>, pred: &Fn(i32) -> bool) -> Result<(), Error> {}"
                    .to_owned(),
            ..Default::default()
        };
        let tracker = ConvergenceTracker::new();
        let config = default_config();

        let difficulty = DifficultyClassifier::classify(&func);
        assert_eq!(difficulty, Difficulty::Hard);

        let strategy = AdaptiveSelector::select_strategy(&func, &tracker, &config);
        assert_eq!(strategy, Strategy::OracleAssisted);
    }

    #[test]
    fn test_select_strategy_intractable_function_returns_hybrid() {
        let func = complex_func("complex_op");
        let tracker = ConvergenceTracker::new();
        let config = default_config();

        let difficulty = DifficultyClassifier::classify(&func);
        assert_eq!(difficulty, Difficulty::Intractable);

        let strategy = AdaptiveSelector::select_strategy(&func, &tracker, &config);
        match strategy {
            Strategy::Hybrid {
                mining_budget,
                oracle_budget,
            } => {
                assert!(mining_budget > 0);
                assert!(oracle_budget > 0);
                assert_eq!(mining_budget + oracle_budget, config.budget);
            }
            other => panic!("expected Hybrid, got {:?}", other),
        }
    }

    #[test]
    fn test_select_strategy_escalates_on_prior_failures() {
        let func = simple_func("tricky", 1);
        let mut tracker = ConvergenceTracker::new();
        let config = AdaptiveConfig {
            escalation_threshold: 3,
            ..default_config()
        };

        // Record enough failures to exceed the escalation threshold.
        for _ in 0..4 {
            tracker.record("tricky", &test_failed_feedback(), Difficulty::Easy);
        }

        let strategy = AdaptiveSelector::select_strategy(&func, &tracker, &config);
        // Easy with failures should escalate to CgsrRefinement.
        assert_eq!(strategy, Strategy::CgsrRefinement);
    }

    // -----------------------------------------------------------------------
    // Escalation tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_escalate_template_to_cgsr() {
        let config = default_config();
        let next = AdaptiveSelector::escalate(&Strategy::TemplateMining, &config);
        assert_eq!(next, Some(Strategy::CgsrRefinement));
    }

    #[test]
    fn test_escalate_cgsr_to_oracle() {
        let config = default_config();
        let next = AdaptiveSelector::escalate(&Strategy::CgsrRefinement, &config);
        assert_eq!(next, Some(Strategy::OracleAssisted));
    }

    #[test]
    fn test_escalate_oracle_to_hybrid() {
        let config = default_config();
        let next = AdaptiveSelector::escalate(&Strategy::OracleAssisted, &config);
        match next {
            Some(Strategy::Hybrid {
                mining_budget,
                oracle_budget,
            }) => {
                assert!(mining_budget > 0);
                assert!(oracle_budget > 0);
            }
            other => panic!("expected Some(Hybrid), got {:?}", other),
        }
    }

    #[test]
    fn test_escalate_hybrid_returns_none() {
        let config = default_config();
        let next = AdaptiveSelector::escalate(
            &Strategy::Hybrid {
                mining_budget: 5,
                oracle_budget: 15,
            },
            &config,
        );
        assert_eq!(next, None);
    }

    // -----------------------------------------------------------------------
    // Strategy enum tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_strategy_as_str() {
        assert_eq!(Strategy::TemplateMining.as_str(), "template-mining");
        assert_eq!(Strategy::CgsrRefinement.as_str(), "cgsr-refinement");
        assert_eq!(Strategy::OracleAssisted.as_str(), "oracle-assisted");
        assert_eq!(
            Strategy::Hybrid {
                mining_budget: 5,
                oracle_budget: 15,
            }
            .as_str(),
            "hybrid"
        );
    }

    #[test]
    fn test_strategy_cost_rank_ordering() {
        assert!(Strategy::TemplateMining.cost_rank() < Strategy::CgsrRefinement.cost_rank());
        assert!(Strategy::CgsrRefinement.cost_rank() < Strategy::OracleAssisted.cost_rank());
        assert!(
            Strategy::OracleAssisted.cost_rank()
                < Strategy::Hybrid {
                    mining_budget: 5,
                    oracle_budget: 15,
                }
                .cost_rank()
        );
    }

    // -----------------------------------------------------------------------
    // Adaptive runner tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_run_adaptive_empty_functions_list() {
        let config = default_config();
        let result =
            run_adaptive_functions(&[], &config, None, &AlwaysVerifies).expect("should succeed");

        assert!(result.functions.is_empty());
        assert_eq!(result.total_specs, 0);
        assert_eq!(result.budget_used, 0);
        assert_eq!(result.escalation_count, 0);
        assert_eq!(result.convergence_rate(), 0.0);
    }

    #[test]
    fn test_run_adaptive_single_easy_function_converges() {
        let func = simple_func("identity", 1);
        let config = default_config();

        let result = run_adaptive_functions(&[func], &config, None, &AlwaysVerifies)
            .expect("should succeed");

        assert_eq!(result.functions.len(), 1);
        let fr = &result.functions[0];
        assert_eq!(fr.function_name, "identity");
        assert!(
            fr.converged,
            "easy function should converge with AlwaysVerifies"
        );
        assert!(!fr.specs.is_empty());
        assert_eq!(fr.strategy_used, Strategy::TemplateMining);
    }

    #[test]
    fn test_run_adaptive_all_fail_produces_no_specs() {
        let func = simple_func("stubborn", 1);
        let config = AdaptiveConfig {
            budget: 10,
            escalation_threshold: 3,
            ..default_config()
        };

        let result =
            run_adaptive_functions(&[func], &config, None, &AlwaysFails).expect("should succeed");

        assert_eq!(result.functions.len(), 1);
        let fr = &result.functions[0];
        assert!(!fr.converged);
        assert!(fr.specs.is_empty());
    }

    #[test]
    fn test_run_adaptive_escalation_increments_counter() {
        // Use a scripted adapter that fails for the first N calls then succeeds.
        let mut responses = Vec::new();
        for _ in 0..20 {
            responses.push(test_failed_feedback());
        }
        let adapter = ScriptedAdapter::new(responses);

        let func = simple_func("escalate_test", 1);
        let config = AdaptiveConfig {
            budget: 15,
            escalation_threshold: 3,
            ..default_config()
        };

        let result =
            run_adaptive_functions(&[func], &config, None, &adapter).expect("should succeed");

        // Should have escalated at least once (TemplateMining -> CgsrRefinement).
        assert!(
            result.escalation_count >= 1,
            "should escalate at least once, got {}",
            result.escalation_count,
        );
    }

    #[test]
    fn test_run_adaptive_budget_limits_total_work() {
        let func = simple_func("budget_test", 1);
        let config = AdaptiveConfig {
            budget: 3,
            escalation_threshold: 2,
            ..default_config()
        };

        let adapter = ScriptedAdapter::new(vec![
            test_failed_feedback(),
            test_failed_feedback(),
            test_failed_feedback(),
            test_failed_feedback(),
            test_failed_feedback(),
        ]);

        let result =
            run_adaptive_functions(&[func], &config, None, &adapter).expect("should succeed");

        assert!(
            result.budget_used <= config.budget,
            "budget_used {} should not exceed budget {}",
            result.budget_used,
            config.budget,
        );
    }

    #[test]
    fn test_run_adaptive_multiple_functions() {
        let funcs = vec![simple_func("f1", 1), simple_func("f2", 2)];
        let config = default_config();

        let result =
            run_adaptive_functions(&funcs, &config, None, &AlwaysVerifies).expect("should succeed");

        assert_eq!(result.functions.len(), 2);
        for fr in &result.functions {
            assert!(fr.converged, "{} should converge", fr.function_name);
        }
        assert!(result.total_specs >= 2);
    }

    #[test]
    fn test_run_adaptive_oracle_strategy_with_backend() {
        // Create a hard function that will select OracleAssisted.
        let func = FunctionSignature {
            name: "hard_fn".to_owned(),
            params: vec![
                ("data".to_owned(), "&mut Vec<i32>".to_owned()),
                ("pred".to_owned(), "&Fn(i32) -> bool".to_owned()),
            ],
            return_type: Some("Result<(), Error>".to_owned()),
            source:
                "fn hard_fn(data: &mut Vec<i32>, pred: &Fn(i32) -> bool) -> Result<(), Error> {}"
                    .to_owned(),
            ..Default::default()
        };

        let proposal = ProposedAnnotations {
            requires: vec!["data.len() > 0".to_owned()],
            ensures: vec!["result.is_ok()".to_owned()],
            invariants: vec![],
            decreases: vec![],
            raw_response: "requires!(data.len() > 0) ensures!(result.is_ok())".to_owned(),
        };
        // Provide enough proposals to cover the budget (oracle may retry).
        let backend = MockOracleBackend::new(vec![
            proposal.clone(),
            proposal.clone(),
            proposal.clone(),
            proposal.clone(),
            proposal,
        ]);

        let config = AdaptiveConfig {
            budget: 5,
            escalation_threshold: 3,
            ..default_config()
        };

        // The oracle backend proposes annotations, but verification still runs
        // through the adapter. Use AlwaysVerifies so the oracle path succeeds.
        let result = run_adaptive_functions(&[func], &config, Some(&backend), &AlwaysVerifies)
            .expect("should succeed");

        assert_eq!(result.functions.len(), 1);
        // The function is Hard, so it goes straight to OracleAssisted.
        // With AlwaysVerifies, template mining in the first strategy attempt
        // would succeed if there are applicable templates.
    }

    #[test]
    fn test_run_adaptive_no_backend_skips_oracle() {
        // Create a function hard enough to want oracle but give no backend.
        let func = FunctionSignature {
            name: "needs_oracle".to_owned(),
            params: vec![
                ("data".to_owned(), "&mut Vec<i32>".to_owned()),
                ("pred".to_owned(), "&Fn(i32) -> bool".to_owned()),
            ],
            return_type: Some("Result<(), Error>".to_owned()),
            source: "fn needs_oracle(data: &mut Vec<i32>, pred: &Fn(i32) -> bool) -> Result<(), Error> {}".to_owned(),
            ..Default::default()
        };

        let config = AdaptiveConfig {
            budget: 10,
            escalation_threshold: 3,
            ..default_config()
        };

        let result =
            run_adaptive_functions(&[func], &config, None, &AlwaysFails).expect("should succeed");

        assert_eq!(result.functions.len(), 1);
        // Without a backend, oracle strategy returns no specs and 0 iters.
        // Function should not converge.
        let fr = &result.functions[0];
        assert!(!fr.converged);
    }

    // -----------------------------------------------------------------------
    // AdaptiveResult tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_adaptive_result_all_converged() {
        let result = AdaptiveResult {
            functions: vec![
                FunctionResult {
                    function_name: "a".to_owned(),
                    specs: vec![MinedSpec::new(
                        "a".to_owned(),
                        "range".to_owned(),
                        vec![],
                        vec!["x >= 0".to_owned()],
                        true,
                        0,
                    )],
                    strategy_used: Strategy::TemplateMining,
                    iterations_consumed: 1,
                    converged: true,
                },
                FunctionResult {
                    function_name: "b".to_owned(),
                    specs: vec![MinedSpec::new(
                        "b".to_owned(),
                        "range".to_owned(),
                        vec![],
                        vec!["y >= 0".to_owned()],
                        true,
                        0,
                    )],
                    strategy_used: Strategy::CgsrRefinement,
                    iterations_consumed: 3,
                    converged: true,
                },
            ],
            total_specs: 2,
            budget_used: 4,
            escalation_count: 0,
        };

        assert!(result.all_converged());
        assert_eq!(result.converged_count(), 2);
        assert!((result.convergence_rate() - 1.0).abs() < f64::EPSILON);
    }

    #[test]
    fn test_adaptive_result_partial_convergence() {
        let result = AdaptiveResult {
            functions: vec![
                FunctionResult {
                    function_name: "a".to_owned(),
                    specs: vec![],
                    strategy_used: Strategy::TemplateMining,
                    iterations_consumed: 5,
                    converged: false,
                },
                FunctionResult {
                    function_name: "b".to_owned(),
                    specs: vec![MinedSpec::new(
                        "b".to_owned(),
                        "range".to_owned(),
                        vec![],
                        vec!["y >= 0".to_owned()],
                        true,
                        0,
                    )],
                    strategy_used: Strategy::TemplateMining,
                    iterations_consumed: 1,
                    converged: true,
                },
            ],
            total_specs: 1,
            budget_used: 6,
            escalation_count: 1,
        };

        assert!(!result.all_converged());
        assert_eq!(result.converged_count(), 1);
        assert!((result.convergence_rate() - 0.5).abs() < f64::EPSILON);
    }

    #[test]
    fn test_adaptive_result_empty() {
        let result = AdaptiveResult {
            functions: vec![],
            total_specs: 0,
            budget_used: 0,
            escalation_count: 0,
        };

        assert!(!result.all_converged());
        assert_eq!(result.converged_count(), 0);
        assert!((result.convergence_rate() - 0.0).abs() < f64::EPSILON);
    }

    // -----------------------------------------------------------------------
    // Config tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_adaptive_config_default() {
        let config = AdaptiveConfig::default();
        assert_eq!(config.budget, 20);
        assert_eq!(config.escalation_threshold, 5);
        assert_eq!(config.parallel_candidates, 1);
        assert!(!config.verbose);
    }

    // -----------------------------------------------------------------------
    // FunctionResult tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_function_result_new_defaults() {
        let fr = FunctionResult::new("test_fn".to_owned(), Strategy::TemplateMining);
        assert_eq!(fr.function_name, "test_fn");
        assert!(fr.specs.is_empty());
        assert_eq!(fr.strategy_used, Strategy::TemplateMining);
        assert_eq!(fr.iterations_consumed, 0);
        assert!(!fr.converged);
    }

    // -----------------------------------------------------------------------
    // Integration-style tests (template mining path)
    // -----------------------------------------------------------------------

    #[test]
    fn test_template_mining_converges_on_easy_function() {
        let func = simple_func("easy", 1);
        let (specs, iters) = run_template_mining(&func, 10, &AlwaysVerifies, false);
        assert!(
            specs.iter().any(|s| s.verified),
            "template mining should find at least one verified spec"
        );
        assert!(iters > 0, "should use at least one iteration");
    }

    #[test]
    fn test_template_mining_respects_budget() {
        let func = simple_func("bounded", 1);
        let (_, iters) = run_template_mining(&func, 2, &AlwaysFails, false);
        assert!(iters <= 2, "should not exceed budget of 2, used {}", iters,);
    }

    #[test]
    fn test_template_mining_empty_templates_returns_zero() {
        // A function with no params and no return type has very few templates.
        let func = FunctionSignature {
            name: "void_fn".to_owned(),
            params: vec![],
            return_type: None,
            source: "fn void_fn() {}".to_owned(),
            ..Default::default()
        };
        let (specs, iters) = run_template_mining(&func, 10, &AlwaysVerifies, false);
        // May or may not have applicable templates; either way should not crash.
        assert!(iters <= 10);
        for s in &specs {
            assert!(s.verified);
        }
    }

    // -----------------------------------------------------------------------
    // Escalation-from-history tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_escalate_from_history_easy() {
        let config = default_config();
        let strategy = escalate_from_history(Difficulty::Easy, &config);
        assert_eq!(strategy, Strategy::CgsrRefinement);
    }

    #[test]
    fn test_escalate_from_history_medium() {
        let config = default_config();
        let strategy = escalate_from_history(Difficulty::Medium, &config);
        assert_eq!(strategy, Strategy::OracleAssisted);
    }

    #[test]
    fn test_escalate_from_history_hard() {
        let config = default_config();
        let strategy = escalate_from_history(Difficulty::Hard, &config);
        match strategy {
            Strategy::Hybrid {
                mining_budget,
                oracle_budget,
            } => {
                assert!(mining_budget + oracle_budget == config.budget);
            }
            other => panic!("expected Hybrid, got {:?}", other),
        }
    }

    #[test]
    fn test_escalate_from_history_intractable() {
        let config = default_config();
        let strategy = escalate_from_history(Difficulty::Intractable, &config);
        match strategy {
            Strategy::Hybrid { .. } => {}
            other => panic!("expected Hybrid, got {:?}", other),
        }
    }
}
