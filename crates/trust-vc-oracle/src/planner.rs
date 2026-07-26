// trust-vc-oracle — Strategy planning for multi-step proof synthesis
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Plans multi-step proof strategies based on function characteristics and
// historical convergence data. Executes plans step-by-step with budget
// tracking and provides post-execution analysis with improvement suggestions.

use crate::convergence::{ConvergenceTracker, Difficulty, DifficultyClassifier, FeedbackKind};
use crate::engine::FunctionSignature;
use crate::mining::MinedSpec;

// ---------------------------------------------------------------------------
// Plan types
// ---------------------------------------------------------------------------

/// An action to take within a proof plan step.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum PlanAction {
    /// Try template mining to discover specs from known patterns.
    MineTemplates { templates: Vec<String> },
    /// Run CGSR (Counterexample-Guided Specification Refinement) loop.
    RunCgsr {
        max_rounds: usize,
        initial_spec: Option<String>,
    },
    /// Query the LLM oracle with guidance hints.
    QueryOracle { prompt_hint: String },
    /// Decompose the function into smaller sub-proofs.
    DecomposeFunction { sub_functions: Vec<String> },
    /// Apply a known lemma to discharge a proof obligation.
    ApplyLemma { lemma_name: String },
    /// Use structural induction with the given measure and base case.
    InductionScheme { measure: String, base_case: String },
}

/// A single step within a proof plan.
#[derive(Debug, Clone)]
pub struct PlanStep {
    /// The action to execute.
    pub action: PlanAction,
    /// Iteration budget allocated to this step.
    pub budget: usize,
    /// Precondition that must hold before executing this step.
    pub precondition: Option<String>,
    /// Description of the expected outcome if this step succeeds.
    pub expected_outcome: String,
}

/// A multi-step proof plan for a single function.
#[derive(Debug, Clone)]
pub struct ProofPlan {
    /// Name of the function this plan targets.
    pub function_name: String,
    /// Ordered sequence of plan steps.
    pub steps: Vec<PlanStep>,
    /// Estimated difficulty of the proof.
    pub estimated_difficulty: Difficulty,
    /// Estimated total iterations across all steps.
    pub estimated_iterations: usize,
    /// Fallback strategy if the primary plan fails.
    pub fallback_strategy: Option<Box<ProofPlan>>,
}

impl ProofPlan {
    /// Total budget across all steps.
    #[must_use]
    pub fn total_budget(&self) -> usize {
        self.steps.iter().map(|s| s.budget).sum()
    }
}

// ---------------------------------------------------------------------------
// Execution results
// ---------------------------------------------------------------------------

/// Outcome of executing a single plan step.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum StepOutcome {
    /// Step succeeded — produced verified specs.
    Success,
    /// Step produced partial results (some specs, not fully verified).
    Partial,
    /// Step failed to produce useful results.
    Failed,
    /// Step was skipped (precondition not met or budget exhausted).
    Skipped,
}

/// Result of executing a single plan step.
#[derive(Debug, Clone)]
pub struct PlanStepResult {
    /// The step that was executed.
    pub step: PlanStep,
    /// Outcome of the execution.
    pub outcome: StepOutcome,
    /// Specs produced by this step.
    pub specs_produced: Vec<MinedSpec>,
    /// Number of iterations consumed.
    pub iterations_used: usize,
}

// ---------------------------------------------------------------------------
// Plan analysis
// ---------------------------------------------------------------------------

/// Post-execution analysis of a proof plan.
#[derive(Debug, Clone)]
pub struct PlanAnalysis {
    /// Fraction of steps that succeeded (0.0 to 1.0).
    pub success_rate: f64,
    /// Budget allocated but not productively used.
    pub wasted_budget: usize,
    /// Index of the step that consumed the most budget without success.
    pub bottleneck_step: Option<usize>,
    /// Overall recommendation based on the analysis.
    pub recommendation: String,
}

// ---------------------------------------------------------------------------
// StrategyPlanner
// ---------------------------------------------------------------------------

/// Plans multi-step proof strategies based on function characteristics
/// and historical convergence data.
#[derive(Debug, Clone)]
pub struct StrategyPlanner {
    /// Default budget per step when no history is available.
    default_step_budget: usize,
}

impl StrategyPlanner {
    /// Create a new planner with default settings.
    #[must_use]
    pub fn new() -> Self {
        Self {
            default_step_budget: 5,
        }
    }

    /// Plan a proof strategy for the given function.
    ///
    /// Uses function signature analysis and historical convergence data to
    /// select appropriate proof tactics and allocate iteration budgets.
    #[must_use]
    pub fn plan(&self, func: &FunctionSignature, history: &ConvergenceTracker) -> ProofPlan {
        let difficulty = DifficultyClassifier::classify(func);
        let has_prior_failure = self.had_prior_failure(func, history);
        let traits = FunctionTraits::analyze(func);

        let steps = if has_prior_failure {
            self.plan_with_prior_failure(func, &traits, history)
        } else {
            self.plan_fresh(func, &traits, difficulty)
        };

        let estimated_iterations: usize = steps.iter().map(|s| s.budget).sum();
        let fallback_strategy = self.build_fallback(func, &traits, difficulty);

        ProofPlan {
            function_name: func.name.clone(),
            steps,
            estimated_difficulty: difficulty,
            estimated_iterations,
            fallback_strategy,
        }
    }

    /// Check whether the tracker has a non-converging history for this function.
    fn had_prior_failure(&self, func: &FunctionSignature, history: &ConvergenceTracker) -> bool {
        history
            .history(&func.name)
            .is_some_and(|h| !h.converged && h.iteration_count() > 0)
    }

    /// Plan for a function with no prior history.
    fn plan_fresh(
        &self,
        func: &FunctionSignature,
        traits: &FunctionTraits,
        difficulty: Difficulty,
    ) -> Vec<PlanStep> {
        let mut steps = Vec::new();

        if traits.is_pure && !traits.has_loops {
            // Pure functions without loops: template mining is usually sufficient.
            steps.push(PlanStep {
                action: PlanAction::MineTemplates {
                    templates: vec!["range".into(), "identity".into(), "monotonic".into()],
                },
                budget: self.budget_for_difficulty(difficulty),
                precondition: None,
                expected_outcome: "Discover verified specs via template instantiation".into(),
            });
        }

        if traits.has_loops {
            // Loop-bearing functions need CGSR with invariant focus.
            steps.push(PlanStep {
                action: PlanAction::RunCgsr {
                    max_rounds: self.budget_for_difficulty(difficulty),
                    initial_spec: None,
                },
                budget: self.budget_for_difficulty(difficulty) + 2,
                precondition: None,
                expected_outcome: "Converge on loop invariants via CGSR refinement".into(),
            });
        }

        if traits.is_recursive {
            // Recursive functions need induction.
            let measure = self.infer_measure(func);
            steps.push(PlanStep {
                action: PlanAction::InductionScheme {
                    measure: measure.clone(),
                    base_case: format!("{} == 0", measure),
                },
                budget: self.budget_for_difficulty(difficulty) + 1,
                precondition: None,
                expected_outcome: "Establish termination and correctness via structural induction"
                    .into(),
            });
            steps.push(PlanStep {
                action: PlanAction::QueryOracle {
                    prompt_hint: format!(
                        "Prove recursive function '{}' using induction on '{}'",
                        func.name, measure
                    ),
                },
                budget: self.default_step_budget,
                precondition: Some("Induction scheme established".into()),
                expected_outcome: "LLM proposes inductive proof annotations".into(),
            });
        }

        if traits.has_complex_types {
            // Complex types benefit from decomposition.
            let sub_functions = self.suggest_decomposition(func);
            steps.push(PlanStep {
                action: PlanAction::DecomposeFunction {
                    sub_functions: sub_functions.clone(),
                },
                budget: 2,
                precondition: None,
                expected_outcome: "Break proof into manageable sub-obligations".into(),
            });
            steps.push(PlanStep {
                action: PlanAction::QueryOracle {
                    prompt_hint: format!(
                        "Prove '{}' by composing proofs of: {}",
                        func.name,
                        sub_functions.join(", ")
                    ),
                },
                budget: self.budget_for_difficulty(difficulty),
                precondition: Some("Decomposition complete".into()),
                expected_outcome: "LLM proposes specs leveraging decomposition".into(),
            });
        }

        // If no specialized steps were added, fall back to generic oracle query.
        if steps.is_empty() {
            steps.push(PlanStep {
                action: PlanAction::QueryOracle {
                    prompt_hint: format!("Prove function '{}'", func.name),
                },
                budget: self.budget_for_difficulty(difficulty),
                precondition: None,
                expected_outcome: "LLM proposes annotations for verification".into(),
            });
        }

        steps
    }

    /// Plan for a function that previously failed to converge.
    ///
    /// Avoids repeating the same strategy by choosing a different approach.
    fn plan_with_prior_failure(
        &self,
        func: &FunctionSignature,
        traits: &FunctionTraits,
        history: &ConvergenceTracker,
    ) -> Vec<PlanStep> {
        let func_history = history.history(&func.name);
        let prior_had_errors =
            func_history.is_some_and(|h| h.feedback_sequence.contains(&FeedbackKind::Error));
        let prior_iterations = func_history.map_or(0, |h| h.iteration_count());

        let mut steps = Vec::new();

        // If prior attempts hit errors, try decomposition first to simplify.
        if prior_had_errors || prior_iterations > 5 {
            let sub_functions = self.suggest_decomposition(func);
            steps.push(PlanStep {
                action: PlanAction::DecomposeFunction {
                    sub_functions: sub_functions.clone(),
                },
                budget: 2,
                precondition: None,
                expected_outcome: "Simplify proof obligation via decomposition".into(),
            });
        }

        // Try a lemma-based approach if prior CGSR/template mining failed.
        steps.push(PlanStep {
            action: PlanAction::ApplyLemma {
                lemma_name: format!("{}_helper", func.name),
            },
            budget: 3,
            precondition: None,
            expected_outcome: "Discharge obligation using helper lemma".into(),
        });

        // Oracle with explicit guidance about what failed before.
        steps.push(PlanStep {
            action: PlanAction::QueryOracle {
                prompt_hint: format!(
                    "Previous {} attempts failed for '{}'. Try a fundamentally different approach. {}",
                    prior_iterations,
                    func.name,
                    if traits.has_loops {
                        "Focus on stronger loop invariants."
                    } else if traits.is_recursive {
                        "Consider a different induction measure."
                    } else {
                        "Consider adding preconditions to narrow the input domain."
                    }
                ),
            },
            budget: self.default_step_budget + 2,
            precondition: None,
            expected_outcome: "LLM proposes novel approach avoiding prior failures".into(),
        });

        steps
    }

    /// Build a fallback plan for when the primary plan fails.
    fn build_fallback(
        &self,
        func: &FunctionSignature,
        traits: &FunctionTraits,
        difficulty: Difficulty,
    ) -> Option<Box<ProofPlan>> {
        // Only build fallbacks for non-easy functions.
        if difficulty == Difficulty::Easy {
            return None;
        }

        let mut fallback_steps = Vec::new();

        // Fallback: full oracle query with maximal budget.
        fallback_steps.push(PlanStep {
            action: PlanAction::QueryOracle {
                prompt_hint: format!(
                    "All standard approaches failed for '{}'. Use maximum creativity.",
                    func.name
                ),
            },
            budget: self.default_step_budget * 2,
            precondition: None,
            expected_outcome: "LLM finds unconventional proof strategy".into(),
        });

        // If complex, also try decomposition in fallback.
        if traits.has_complex_types || difficulty == Difficulty::Intractable {
            let sub_functions = self.suggest_decomposition(func);
            fallback_steps.push(PlanStep {
                action: PlanAction::DecomposeFunction { sub_functions },
                budget: 3,
                precondition: None,
                expected_outcome: "Break intractable proof into smaller pieces".into(),
            });
        }

        let estimated = fallback_steps.iter().map(|s| s.budget).sum();

        Some(Box::new(ProofPlan {
            function_name: func.name.clone(),
            steps: fallback_steps,
            estimated_difficulty: difficulty,
            estimated_iterations: estimated,
            fallback_strategy: None,
        }))
    }

    /// Budget allocation based on difficulty.
    fn budget_for_difficulty(&self, difficulty: Difficulty) -> usize {
        match difficulty {
            Difficulty::Easy => 2,
            Difficulty::Medium => self.default_step_budget,
            Difficulty::Hard => self.default_step_budget * 2,
            Difficulty::Intractable => self.default_step_budget * 3,
        }
    }

    /// Infer a termination measure from function source.
    fn infer_measure(&self, func: &FunctionSignature) -> String {
        // Heuristic: first integer-like parameter is likely the measure.
        for (name, ty) in &func.params {
            if is_integer_type(ty) {
                return name.clone();
            }
        }
        // Fallback: use first parameter or "n".
        func.params
            .first()
            .map(|(name, _)| name.clone())
            .unwrap_or_else(|| "n".into())
    }

    /// Suggest decomposition sub-functions based on parameters.
    fn suggest_decomposition(&self, func: &FunctionSignature) -> Vec<String> {
        let mut subs = Vec::new();
        for (name, ty) in &func.params {
            if ty.contains("Vec") || ty.contains("Seq") || ty.contains("Map") || ty.contains("Set")
            {
                subs.push(format!("{}_element_invariant", name));
            }
        }
        if subs.is_empty() {
            subs.push(format!("{}_precondition_check", func.name));
            subs.push(format!("{}_core_logic", func.name));
        }
        subs
    }
}

impl Default for StrategyPlanner {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Function trait analysis (internal)
// ---------------------------------------------------------------------------

/// Structural traits of a function derived from source analysis.
#[derive(Debug, Clone)]
struct FunctionTraits {
    /// True if the function appears to be pure (no &mut, no side-effect keywords).
    is_pure: bool,
    /// True if the function source contains loop constructs.
    has_loops: bool,
    /// True if the function appears to call itself.
    is_recursive: bool,
    /// True if the function uses complex types (collections, generics, etc.).
    has_complex_types: bool,
}

impl FunctionTraits {
    fn analyze(func: &FunctionSignature) -> Self {
        let source = &func.source;
        let has_mut_param = func.params.iter().any(|(_, ty)| ty.contains("&mut"));

        Self {
            is_pure: !has_mut_param
                && !source.contains("unsafe")
                && !source.contains("static")
                && !source.contains("println!")
                && !source.contains("eprintln!"),
            has_loops: source.contains("while ")
                || source.contains("for ")
                || source.contains("loop "),
            is_recursive: source_calls_self(source, &func.name),
            has_complex_types: func.params.iter().any(|(_, ty)| {
                ty.contains("Vec")
                    || ty.contains("Map")
                    || ty.contains("Set")
                    || ty.contains("Seq")
                    || ty.contains("Option")
                    || ty.contains("Result")
            }),
        }
    }
}

/// Check whether the function source contains a call to itself.
fn source_calls_self(source: &str, func_name: &str) -> bool {
    // Look for `func_name(` in the body (after the signature).
    // Crude heuristic: find the first '{' and search within the body.
    let body_start = source.find('{').map(|i| i + 1).unwrap_or(0);
    let body = &source[body_start..];
    let call_pattern = format!("{}(", func_name);
    body.contains(&call_pattern)
}

/// Check if a type string represents an integer type.
fn is_integer_type(ty: &str) -> bool {
    let base = ty.trim_start_matches('&').trim();
    matches!(
        base,
        "u8" | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
    )
}

// ---------------------------------------------------------------------------
// PlanExecutor
// ---------------------------------------------------------------------------

/// Executes a proof plan step-by-step with budget tracking.
#[derive(Debug)]
pub struct PlanExecutor {
    plan: ProofPlan,
    current_step: usize,
    completed: Vec<PlanStepResult>,
    total_budget_used: usize,
}

impl PlanExecutor {
    /// Create a new executor for the given plan.
    #[must_use]
    pub fn new(plan: ProofPlan) -> Self {
        Self {
            plan,
            current_step: 0,
            completed: Vec::new(),
            total_budget_used: 0,
        }
    }

    /// Execute the next step in the plan.
    ///
    /// Returns `None` if all steps have been executed or the budget is exhausted.
    /// The actual execution is simulated: callers should use the returned
    /// `PlanStep` to dispatch real work and then record results.
    pub fn execute_next(&mut self) -> Option<PlanStepResult> {
        if self.current_step >= self.plan.steps.len() {
            return None;
        }

        let step = self.plan.steps[self.current_step].clone();

        // Check if we have budget remaining.
        let remaining = self.remaining_budget();
        if remaining == 0 {
            let result = PlanStepResult {
                step,
                outcome: StepOutcome::Skipped,
                specs_produced: Vec::new(),
                iterations_used: 0,
            };
            self.completed.push(result.clone());
            self.current_step += 1;
            return Some(result);
        }

        // Simulate step execution: consume the step's budget (capped by remaining).
        let budget_to_use = step.budget.min(remaining);
        self.total_budget_used += budget_to_use;

        let result = PlanStepResult {
            step,
            outcome: StepOutcome::Failed, // Default: caller overrides via record_result
            specs_produced: Vec::new(),
            iterations_used: budget_to_use,
        };

        self.completed.push(result.clone());
        self.current_step += 1;
        Some(result)
    }

    /// Record an externally-determined result for the last executed step.
    ///
    /// Overwrites the outcome and specs of the most recently completed step.
    pub fn record_result(&mut self, outcome: StepOutcome, specs: Vec<MinedSpec>) {
        if let Some(last) = self.completed.last_mut() {
            last.outcome = outcome;
            last.specs_produced = specs;
        }
    }

    /// Whether all steps have been executed.
    #[must_use]
    pub fn is_complete(&self) -> bool {
        self.current_step >= self.plan.steps.len()
    }

    /// Total remaining budget across unexecuted steps.
    #[must_use]
    pub fn remaining_budget(&self) -> usize {
        self.plan
            .total_budget()
            .saturating_sub(self.total_budget_used)
    }

    /// Completed step results so far.
    #[must_use]
    pub fn completed_steps(&self) -> &[PlanStepResult] {
        &self.completed
    }

    /// The underlying plan.
    #[must_use]
    pub fn plan(&self) -> &ProofPlan {
        &self.plan
    }
}

// ---------------------------------------------------------------------------
// PlanAnalyzer
// ---------------------------------------------------------------------------

/// Post-execution analysis of proof plan results.
pub struct PlanAnalyzer;

impl PlanAnalyzer {
    /// Analyze a sequence of completed plan step results.
    #[must_use]
    pub fn analyze(results: &[PlanStepResult]) -> PlanAnalysis {
        if results.is_empty() {
            return PlanAnalysis {
                success_rate: 0.0,
                wasted_budget: 0,
                bottleneck_step: None,
                recommendation: "No steps executed — plan was empty or skipped entirely".into(),
            };
        }

        let success_count = results
            .iter()
            .filter(|r| r.outcome == StepOutcome::Success)
            .count();
        let success_rate = success_count as f64 / results.len() as f64;

        let wasted_budget: usize = results
            .iter()
            .filter(|r| r.outcome == StepOutcome::Failed || r.outcome == StepOutcome::Skipped)
            .map(|r| r.iterations_used)
            .sum();

        // Bottleneck: the failed step that consumed the most iterations.
        let bottleneck_step = results
            .iter()
            .enumerate()
            .filter(|(_, r)| r.outcome == StepOutcome::Failed)
            .max_by_key(|(_, r)| r.iterations_used)
            .map(|(i, _)| i);

        let recommendation = Self::build_recommendation(success_rate, wasted_budget, results);

        PlanAnalysis {
            success_rate,
            wasted_budget,
            bottleneck_step,
            recommendation,
        }
    }

    /// Suggest improvements based on plan analysis.
    #[must_use]
    pub fn suggest_improvements(analysis: &PlanAnalysis) -> Vec<String> {
        let mut suggestions = Vec::new();

        if analysis.success_rate == 0.0 {
            suggestions.push(
                "No steps succeeded. Consider a fundamentally different proof strategy.".into(),
            );
        } else if analysis.success_rate < 0.5 {
            suggestions
                .push("Low success rate. Allocate more budget to successful step types.".into());
        }

        if analysis.wasted_budget > 5 {
            suggestions.push(format!(
                "High wasted budget ({}). Reduce allocation to failing steps or add \
                 early-exit conditions.",
                analysis.wasted_budget
            ));
        }

        if let Some(idx) = analysis.bottleneck_step {
            suggestions.push(format!(
                "Step {} is the bottleneck. Consider replacing it with a different tactic \
                 or splitting it into smaller sub-steps.",
                idx
            ));
        }

        if analysis.success_rate >= 0.8 {
            suggestions.push(
                "High success rate. Consider reducing overall budget to save iterations.".into(),
            );
        }

        if suggestions.is_empty() {
            suggestions.push("Plan performed adequately. No changes suggested.".into());
        }

        suggestions
    }

    /// Build a recommendation string from analysis metrics.
    fn build_recommendation(
        success_rate: f64,
        wasted_budget: usize,
        results: &[PlanStepResult],
    ) -> String {
        if success_rate >= 0.8 {
            return "Plan is effective. Consider reducing budget for efficiency.".into();
        }
        if success_rate == 0.0 {
            return "Plan failed entirely. Switch to fallback strategy or manual annotation."
                .into();
        }
        if wasted_budget > results.len() * 2 {
            return "Significant budget waste. Restructure plan to front-load likely-successful \
                    steps."
                .into();
        }
        "Plan partially succeeded. Review failing steps and consider alternative tactics.".into()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::convergence::Difficulty;
    use crate::feedback::ProofFeedback;
    use std::time::Duration;

    fn simple_func(name: &str) -> FunctionSignature {
        FunctionSignature {
            name: name.into(),
            params: vec![("x".into(), "u32".into())],
            return_type: Some("u32".into()),
            source: format!("fn {}(x: u32) -> u32 {{ x }}", name),
            ..Default::default()
        }
    }

    fn loop_func() -> FunctionSignature {
        FunctionSignature {
            name: "sum".into(),
            params: vec![
                ("arr".into(), "&[u32]".into()),
                ("len".into(), "usize".into()),
            ],
            return_type: Some("u32".into()),
            source: "fn sum(arr: &[u32], len: usize) -> u32 { let mut s = 0; for i in 0..len { s += arr[i]; } s }".into(),
            ..Default::default()
        }
    }

    fn recursive_func() -> FunctionSignature {
        FunctionSignature {
            name: "factorial".into(),
            params: vec![("n".into(), "u64".into())],
            return_type: Some("u64".into()),
            source: "fn factorial(n: u64) -> u64 { if n == 0 { 1 } else { n * factorial(n - 1) } }"
                .into(),
            ..Default::default()
        }
    }

    fn complex_func() -> FunctionSignature {
        FunctionSignature {
            name: "merge_maps".into(),
            params: vec![
                ("a".into(), "Map<String, u32>".into()),
                ("b".into(), "Vec<(String, u32)>".into()),
                ("config".into(), "Option<Config>".into()),
            ],
            return_type: Some("Result<Map<String, u32>, Error>".into()),
            source: "fn merge_maps(a: Map<String, u32>, b: Vec<(String, u32)>, config: Option<Config>) -> Result<Map<String, u32>, Error> { todo!() }".into(),
            ..Default::default()
        }
    }

    fn make_failed_feedback() -> ProofFeedback {
        ProofFeedback::Failed {
            counterexamples: vec![],
            localization: crate::feedback::FailureLocalization {
                full_assertion: None,
                sub_results: vec![],
            },
            obligation_name: "ensures".into(),
            solver_mode: "Default".into(),
            elapsed: Duration::from_millis(5),
        }
    }

    fn make_error_feedback() -> ProofFeedback {
        ProofFeedback::Error {
            message: "internal error".into(),
        }
    }

    // --- plan() for simple function produces template mining ---

    #[test]
    fn test_plan_simple_function_produces_template_mining() {
        let planner = StrategyPlanner::new();
        let tracker = ConvergenceTracker::new();
        let func = simple_func("add_one");

        let plan = planner.plan(&func, &tracker);

        assert_eq!(plan.function_name, "add_one");
        assert!(!plan.steps.is_empty());

        let has_mine = plan
            .steps
            .iter()
            .any(|s| matches!(&s.action, PlanAction::MineTemplates { .. }));
        assert!(
            has_mine,
            "simple pure function should include template mining step"
        );
    }

    // --- plan() for loop function includes CGSR ---

    #[test]
    fn test_plan_loop_function_includes_cgsr() {
        let planner = StrategyPlanner::new();
        let tracker = ConvergenceTracker::new();
        let func = loop_func();

        let plan = planner.plan(&func, &tracker);

        let has_cgsr = plan
            .steps
            .iter()
            .any(|s| matches!(&s.action, PlanAction::RunCgsr { .. }));
        assert!(has_cgsr, "loop function should include CGSR step");
    }

    // --- plan() for recursive function includes induction ---

    #[test]
    fn test_plan_recursive_function_includes_induction() {
        let planner = StrategyPlanner::new();
        let tracker = ConvergenceTracker::new();
        let func = recursive_func();

        let plan = planner.plan(&func, &tracker);

        let has_induction = plan
            .steps
            .iter()
            .any(|s| matches!(&s.action, PlanAction::InductionScheme { .. }));
        assert!(
            has_induction,
            "recursive function should include induction scheme step"
        );
    }

    // --- plan() for complex function includes decomposition ---

    #[test]
    fn test_plan_complex_function_includes_decomposition() {
        let planner = StrategyPlanner::new();
        let tracker = ConvergenceTracker::new();
        let func = complex_func();

        let plan = planner.plan(&func, &tracker);

        let has_decompose = plan
            .steps
            .iter()
            .any(|s| matches!(&s.action, PlanAction::DecomposeFunction { .. }));
        assert!(
            has_decompose,
            "complex function should include decomposition step"
        );
    }

    // --- plan() with prior failures changes strategy ---

    #[test]
    fn test_plan_with_prior_failures_changes_strategy() {
        let planner = StrategyPlanner::new();
        let mut tracker = ConvergenceTracker::new();
        let func = simple_func("tricky");

        // Record some failures.
        for _ in 0..3 {
            tracker.record("tricky", &make_failed_feedback(), Difficulty::Medium);
        }

        let plan = planner.plan(&func, &tracker);

        // Should include a lemma step (different from the fresh plan).
        let has_lemma = plan
            .steps
            .iter()
            .any(|s| matches!(&s.action, PlanAction::ApplyLemma { .. }));
        assert!(
            has_lemma,
            "prior-failure plan should include lemma application"
        );

        // Should include an oracle query referencing prior failures.
        let has_failure_aware_oracle = plan.steps.iter().any(|s| {
            if let PlanAction::QueryOracle { prompt_hint } = &s.action {
                prompt_hint.contains("attempts failed")
            } else {
                false
            }
        });
        assert!(
            has_failure_aware_oracle,
            "prior-failure plan should include failure-aware oracle query"
        );
    }

    // --- PlanExecutor tracks progress ---

    #[test]
    fn test_plan_executor_tracks_progress() {
        let plan = ProofPlan {
            function_name: "f".into(),
            steps: vec![
                PlanStep {
                    action: PlanAction::MineTemplates {
                        templates: vec!["range".into()],
                    },
                    budget: 3,
                    precondition: None,
                    expected_outcome: "mine specs".into(),
                },
                PlanStep {
                    action: PlanAction::QueryOracle {
                        prompt_hint: "prove f".into(),
                    },
                    budget: 5,
                    precondition: None,
                    expected_outcome: "oracle proof".into(),
                },
            ],
            estimated_difficulty: Difficulty::Medium,
            estimated_iterations: 8,
            fallback_strategy: None,
        };

        let mut executor = PlanExecutor::new(plan);
        assert!(!executor.is_complete());
        assert_eq!(executor.remaining_budget(), 8);

        let result1 = executor.execute_next();
        assert!(result1.is_some());
        assert_eq!(executor.completed_steps().len(), 1);
        assert!(!executor.is_complete());

        let result2 = executor.execute_next();
        assert!(result2.is_some());
        assert_eq!(executor.completed_steps().len(), 2);
        assert!(executor.is_complete());

        // No more steps.
        assert!(executor.execute_next().is_none());
    }

    // --- PlanExecutor respects budget ---

    #[test]
    fn test_plan_executor_respects_budget() {
        let plan = ProofPlan {
            function_name: "f".into(),
            steps: vec![
                PlanStep {
                    action: PlanAction::RunCgsr {
                        max_rounds: 10,
                        initial_spec: None,
                    },
                    budget: 10,
                    precondition: None,
                    expected_outcome: "cgsr".into(),
                },
                PlanStep {
                    action: PlanAction::QueryOracle {
                        prompt_hint: "prove".into(),
                    },
                    budget: 5,
                    precondition: None,
                    expected_outcome: "oracle".into(),
                },
            ],
            estimated_difficulty: Difficulty::Hard,
            estimated_iterations: 15,
            fallback_strategy: None,
        };

        let mut executor = PlanExecutor::new(plan);

        // Execute first step — uses 10.
        let r1 = executor.execute_next().unwrap();
        assert_eq!(r1.iterations_used, 10);
        assert_eq!(executor.remaining_budget(), 5);

        // Execute second step — uses remaining 5.
        let r2 = executor.execute_next().unwrap();
        assert_eq!(r2.iterations_used, 5);
        assert_eq!(executor.remaining_budget(), 0);
    }

    // --- PlanExecutor handles empty plan ---

    #[test]
    fn test_plan_executor_handles_empty_plan() {
        let plan = ProofPlan {
            function_name: "empty".into(),
            steps: vec![],
            estimated_difficulty: Difficulty::Easy,
            estimated_iterations: 0,
            fallback_strategy: None,
        };

        let mut executor = PlanExecutor::new(plan);
        assert!(executor.is_complete());
        assert_eq!(executor.remaining_budget(), 0);
        assert!(executor.execute_next().is_none());
        assert!(executor.completed_steps().is_empty());
    }

    // --- PlanStepResult records specs ---

    #[test]
    fn test_plan_step_result_records_specs() {
        let spec = MinedSpec::new(
            "f".into(),
            "range".into(),
            vec!["x > 0".into()],
            vec!["result >= 1".into()],
            true,
            1,
        );

        let result = PlanStepResult {
            step: PlanStep {
                action: PlanAction::MineTemplates {
                    templates: vec!["range".into()],
                },
                budget: 3,
                precondition: None,
                expected_outcome: "mine".into(),
            },
            outcome: StepOutcome::Success,
            specs_produced: vec![spec.clone()],
            iterations_used: 2,
        };

        assert_eq!(result.specs_produced.len(), 1);
        assert_eq!(result.specs_produced[0].function_name, "f");
        assert!(result.specs_produced[0].verified);
    }

    // --- PlanAnalyzer computes success rate ---

    #[test]
    fn test_plan_analyzer_computes_success_rate() {
        let results = vec![
            PlanStepResult {
                step: PlanStep {
                    action: PlanAction::MineTemplates { templates: vec![] },
                    budget: 3,
                    precondition: None,
                    expected_outcome: "".into(),
                },
                outcome: StepOutcome::Success,
                specs_produced: vec![],
                iterations_used: 2,
            },
            PlanStepResult {
                step: PlanStep {
                    action: PlanAction::QueryOracle {
                        prompt_hint: "".into(),
                    },
                    budget: 5,
                    precondition: None,
                    expected_outcome: "".into(),
                },
                outcome: StepOutcome::Failed,
                specs_produced: vec![],
                iterations_used: 5,
            },
        ];

        let analysis = PlanAnalyzer::analyze(&results);
        assert!((analysis.success_rate - 0.5).abs() < f64::EPSILON);
    }

    // --- PlanAnalyzer identifies bottleneck ---

    #[test]
    fn test_plan_analyzer_identifies_bottleneck() {
        let results = vec![
            PlanStepResult {
                step: PlanStep {
                    action: PlanAction::MineTemplates { templates: vec![] },
                    budget: 2,
                    precondition: None,
                    expected_outcome: "".into(),
                },
                outcome: StepOutcome::Success,
                specs_produced: vec![],
                iterations_used: 1,
            },
            PlanStepResult {
                step: PlanStep {
                    action: PlanAction::RunCgsr {
                        max_rounds: 10,
                        initial_spec: None,
                    },
                    budget: 10,
                    precondition: None,
                    expected_outcome: "".into(),
                },
                outcome: StepOutcome::Failed,
                specs_produced: vec![],
                iterations_used: 8,
            },
            PlanStepResult {
                step: PlanStep {
                    action: PlanAction::QueryOracle {
                        prompt_hint: "".into(),
                    },
                    budget: 3,
                    precondition: None,
                    expected_outcome: "".into(),
                },
                outcome: StepOutcome::Failed,
                specs_produced: vec![],
                iterations_used: 2,
            },
        ];

        let analysis = PlanAnalyzer::analyze(&results);
        assert_eq!(
            analysis.bottleneck_step,
            Some(1),
            "CGSR step should be the bottleneck"
        );
        assert_eq!(analysis.wasted_budget, 10); // 8 + 2 from failed steps
    }

    // --- PlanAnalyzer suggests improvements ---

    #[test]
    fn test_plan_analyzer_suggests_improvements() {
        // All-failing plan.
        let results = vec![PlanStepResult {
            step: PlanStep {
                action: PlanAction::QueryOracle {
                    prompt_hint: "".into(),
                },
                budget: 10,
                precondition: None,
                expected_outcome: "".into(),
            },
            outcome: StepOutcome::Failed,
            specs_produced: vec![],
            iterations_used: 10,
        }];

        let analysis = PlanAnalyzer::analyze(&results);
        let suggestions = PlanAnalyzer::suggest_improvements(&analysis);

        assert!(!suggestions.is_empty());
        let has_fundamentally_different = suggestions
            .iter()
            .any(|s| s.contains("fundamentally different"));
        assert!(
            has_fundamentally_different,
            "should suggest a different strategy: {:?}",
            suggestions
        );
    }

    // --- Fallback strategy generation ---

    #[test]
    fn test_fallback_strategy_generated_for_non_easy() {
        let planner = StrategyPlanner::new();
        let tracker = ConvergenceTracker::new();

        // Medium difficulty function.
        let func = FunctionSignature {
            name: "process".into(),
            params: vec![
                ("a".into(), "u32".into()),
                ("b".into(), "u32".into()),
                ("c".into(), "u32".into()),
                ("d".into(), "u32".into()),
            ],
            return_type: Some("u32".into()),
            source: "fn process(a: u32, b: u32, c: u32, d: u32) -> u32 { a + b + c + d }".into(),
            ..Default::default()
        };

        let plan = planner.plan(&func, &tracker);
        assert!(
            plan.fallback_strategy.is_some(),
            "non-easy function should have a fallback strategy"
        );

        let fallback = plan.fallback_strategy.as_ref().unwrap();
        assert_eq!(fallback.function_name, "process");
        assert!(!fallback.steps.is_empty());
        // Fallback should not have its own fallback (prevents infinite nesting).
        assert!(fallback.fallback_strategy.is_none());
    }

    // --- No fallback for easy functions ---

    #[test]
    fn test_no_fallback_for_easy_function() {
        let planner = StrategyPlanner::new();
        let tracker = ConvergenceTracker::new();
        let func = simple_func("trivial");

        let plan = planner.plan(&func, &tracker);
        assert!(
            plan.fallback_strategy.is_none(),
            "easy function should not have a fallback"
        );
    }

    // --- Budget allocation across steps ---

    #[test]
    fn test_budget_allocation_across_steps() {
        let planner = StrategyPlanner::new();
        let tracker = ConvergenceTracker::new();
        let func = recursive_func();

        let plan = planner.plan(&func, &tracker);

        // Verify all steps have non-zero budget.
        for step in &plan.steps {
            assert!(step.budget > 0, "every step should have positive budget");
        }

        // Total budget should match estimated_iterations.
        let total: usize = plan.steps.iter().map(|s| s.budget).sum();
        assert_eq!(total, plan.estimated_iterations);
    }

    // --- DecomposeFunction step creation ---

    #[test]
    fn test_decompose_function_step_creation() {
        let planner = StrategyPlanner::new();
        let tracker = ConvergenceTracker::new();
        let func = complex_func();

        let plan = planner.plan(&func, &tracker);

        let decompose_steps: Vec<_> = plan
            .steps
            .iter()
            .filter(|s| matches!(&s.action, PlanAction::DecomposeFunction { .. }))
            .collect();
        assert!(
            !decompose_steps.is_empty(),
            "complex function plan should contain decomposition"
        );

        if let PlanAction::DecomposeFunction { sub_functions } = &decompose_steps[0].action {
            assert!(
                !sub_functions.is_empty(),
                "decomposition should suggest sub-functions"
            );
        }
    }

    // --- InductionScheme step creation ---

    #[test]
    fn test_induction_scheme_step_creation() {
        let planner = StrategyPlanner::new();
        let tracker = ConvergenceTracker::new();
        let func = recursive_func();

        let plan = planner.plan(&func, &tracker);

        let induction_steps: Vec<_> = plan
            .steps
            .iter()
            .filter(|s| matches!(&s.action, PlanAction::InductionScheme { .. }))
            .collect();
        assert!(!induction_steps.is_empty());

        if let PlanAction::InductionScheme { measure, base_case } = &induction_steps[0].action {
            assert_eq!(
                measure, "n",
                "should infer 'n' as the measure for factorial"
            );
            assert!(
                base_case.contains("0"),
                "base case should reference 0: got '{}'",
                base_case
            );
        }
    }

    // --- ApplyLemma step creation ---

    #[test]
    fn test_apply_lemma_step_creation() {
        let planner = StrategyPlanner::new();
        let mut tracker = ConvergenceTracker::new();
        let func = simple_func("hard_func");

        // Record failures to trigger prior-failure path.
        for _ in 0..3 {
            tracker.record("hard_func", &make_failed_feedback(), Difficulty::Medium);
        }

        let plan = planner.plan(&func, &tracker);

        let lemma_steps: Vec<_> = plan
            .steps
            .iter()
            .filter(|s| matches!(&s.action, PlanAction::ApplyLemma { .. }))
            .collect();
        assert!(
            !lemma_steps.is_empty(),
            "prior-failure plan should include lemma step"
        );

        if let PlanAction::ApplyLemma { lemma_name } = &lemma_steps[0].action {
            assert!(
                lemma_name.contains("hard_func"),
                "lemma name should reference the function: got '{}'",
                lemma_name
            );
        }
    }

    // --- Full plan-execute-analyze cycle ---

    #[test]
    fn test_full_plan_execute_analyze_cycle() {
        let planner = StrategyPlanner::new();
        let tracker = ConvergenceTracker::new();
        let func = loop_func();

        // Plan.
        let plan = planner.plan(&func, &tracker);
        assert!(!plan.steps.is_empty());

        // Execute all steps.
        let mut executor = PlanExecutor::new(plan);
        let mut step_count = 0;
        while let Some(_result) = executor.execute_next() {
            // Simulate: first step succeeds, rest fail.
            if step_count == 0 {
                executor.record_result(
                    StepOutcome::Success,
                    vec![MinedSpec::new(
                        "sum".into(),
                        "range".into(),
                        vec![],
                        vec!["result >= 0".into()],
                        true,
                        0,
                    )],
                );
            }
            step_count += 1;
        }
        assert!(executor.is_complete());
        assert!(step_count > 0);

        // Analyze.
        let analysis = PlanAnalyzer::analyze(executor.completed_steps());
        assert!(analysis.success_rate > 0.0, "at least one step succeeded");

        let suggestions = PlanAnalyzer::suggest_improvements(&analysis);
        assert!(
            !suggestions.is_empty(),
            "analyzer should produce suggestions"
        );
    }

    // --- PlanAnalyzer on empty results ---

    #[test]
    fn test_plan_analyzer_empty_results() {
        let analysis = PlanAnalyzer::analyze(&[]);
        assert!((analysis.success_rate - 0.0).abs() < f64::EPSILON);
        assert_eq!(analysis.wasted_budget, 0);
        assert!(analysis.bottleneck_step.is_none());
        assert!(analysis.recommendation.contains("empty"));
    }

    // --- Prior failure with errors triggers decomposition ---

    #[test]
    fn test_prior_failure_with_errors_triggers_decomposition() {
        let planner = StrategyPlanner::new();
        let mut tracker = ConvergenceTracker::new();
        let func = simple_func("erroring");

        // Record errors (not just failures).
        for _ in 0..3 {
            tracker.record("erroring", &make_error_feedback(), Difficulty::Medium);
        }

        let plan = planner.plan(&func, &tracker);

        let has_decompose = plan
            .steps
            .iter()
            .any(|s| matches!(&s.action, PlanAction::DecomposeFunction { .. }));
        assert!(
            has_decompose,
            "error-heavy history should trigger decomposition in retry plan"
        );
    }

    // --- ProofPlan total_budget ---

    #[test]
    fn test_proof_plan_total_budget() {
        let plan = ProofPlan {
            function_name: "f".into(),
            steps: vec![
                PlanStep {
                    action: PlanAction::MineTemplates { templates: vec![] },
                    budget: 3,
                    precondition: None,
                    expected_outcome: "".into(),
                },
                PlanStep {
                    action: PlanAction::RunCgsr {
                        max_rounds: 5,
                        initial_spec: None,
                    },
                    budget: 7,
                    precondition: None,
                    expected_outcome: "".into(),
                },
            ],
            estimated_difficulty: Difficulty::Medium,
            estimated_iterations: 10,
            fallback_strategy: None,
        };

        assert_eq!(plan.total_budget(), 10);
    }

    // --- Analyzer suggests high success rate improvement ---

    #[test]
    fn test_analyzer_suggests_reducing_budget_on_high_success() {
        let results = vec![
            PlanStepResult {
                step: PlanStep {
                    action: PlanAction::MineTemplates { templates: vec![] },
                    budget: 3,
                    precondition: None,
                    expected_outcome: "".into(),
                },
                outcome: StepOutcome::Success,
                specs_produced: vec![],
                iterations_used: 1,
            },
            PlanStepResult {
                step: PlanStep {
                    action: PlanAction::QueryOracle {
                        prompt_hint: "".into(),
                    },
                    budget: 3,
                    precondition: None,
                    expected_outcome: "".into(),
                },
                outcome: StepOutcome::Success,
                specs_produced: vec![],
                iterations_used: 2,
            },
        ];

        let analysis = PlanAnalyzer::analyze(&results);
        assert!((analysis.success_rate - 1.0).abs() < f64::EPSILON);

        let suggestions = PlanAnalyzer::suggest_improvements(&analysis);
        let has_reduce = suggestions.iter().any(|s| s.contains("reducing"));
        assert!(
            has_reduce,
            "high success rate should suggest reducing budget: {:?}",
            suggestions
        );
    }
}
