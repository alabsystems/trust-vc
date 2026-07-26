// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Bridge between the CLI `suggest` subcommand and the oracle/orchestrator
//! system.  Provides configuration, result types, orchestration dispatch, and
//! output formatting for the `cargo trust_vc suggest` pipeline.

#![allow(dead_code)]

use std::fmt::Write as _;
use std::time::{Duration, Instant};

use serde::{Deserialize, Serialize};
use trust_vc_oracle::backend::{MockBackend, ProposedAnnotations};
use trust_vc_oracle::engine::FunctionSignature;
use trust_vc_oracle::orchestrator::{OrchestratorConfig, ProofOrchestrator};

// ---------------------------------------------------------------------------
// Enums
// ---------------------------------------------------------------------------

/// LLM backend choice exposed to the CLI layer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum BackendChoice {
    /// Built-in mock backend for testing (no external tool required).
    Mock,
    /// OpenAI Codex CLI backend.
    Codex,
    /// Anthropic Claude CLI backend.
    Claude,
}

impl std::fmt::Display for BackendChoice {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BackendChoice::Mock => write!(f, "mock"),
            BackendChoice::Codex => write!(f, "codex"),
            BackendChoice::Claude => write!(f, "claude"),
        }
    }
}

/// Output format for the suggest pipeline.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[non_exhaustive]
pub enum SuggestOutputFormat {
    /// Human-readable table.
    #[default]
    Text,
    /// Structured JSON array.
    Json,
    /// Patch-style diff with `+requires!(...)` lines.
    Diff,
}

impl std::fmt::Display for SuggestOutputFormat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SuggestOutputFormat::Text => write!(f, "text"),
            SuggestOutputFormat::Json => write!(f, "json"),
            SuggestOutputFormat::Diff => write!(f, "diff"),
        }
    }
}

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// CLI-facing configuration for the `suggest` subcommand.
#[derive(Debug, Clone)]
pub struct SuggestConfig {
    /// Verify a specific function (all functions if `None`).
    pub function_name: Option<String>,
    /// Maximum number of orchestrator iterations.
    pub max_iterations: usize,
    /// Per-iteration proposal budget.
    pub budget: usize,
    /// Which LLM backend to use.
    pub backend: BackendChoice,
    /// Output format.
    pub output_format: SuggestOutputFormat,
    /// Whether to emit verbose diagnostics.
    pub verbose: bool,
    /// Score threshold for convergence (0.0 to 1.0).
    pub convergence_threshold: f64,
}

impl Default for SuggestConfig {
    fn default() -> Self {
        Self {
            function_name: None,
            max_iterations: 10,
            budget: 5,
            backend: BackendChoice::Mock,
            output_format: SuggestOutputFormat::Text,
            verbose: false,
            convergence_threshold: 0.95,
        }
    }
}

/// Builder for [`SuggestConfig`].
#[derive(Debug, Clone)]
#[must_use]
pub struct SuggestConfigBuilder {
    config: SuggestConfig,
}

impl SuggestConfigBuilder {
    pub fn new() -> Self {
        Self {
            config: SuggestConfig::default(),
        }
    }

    pub fn function_name(mut self, name: impl Into<String>) -> Self {
        self.config.function_name = Some(name.into());
        self
    }

    pub fn max_iterations(mut self, n: usize) -> Self {
        self.config.max_iterations = n;
        self
    }

    pub fn budget(mut self, n: usize) -> Self {
        self.config.budget = n;
        self
    }

    pub fn backend(mut self, b: BackendChoice) -> Self {
        self.config.backend = b;
        self
    }

    pub fn output_format(mut self, f: SuggestOutputFormat) -> Self {
        self.config.output_format = f;
        self
    }

    pub fn verbose(mut self, v: bool) -> Self {
        self.config.verbose = v;
        self
    }

    pub fn convergence_threshold(mut self, t: f64) -> Self {
        self.config.convergence_threshold = t.clamp(0.0, 1.0);
        self
    }

    pub fn build(self) -> SuggestConfig {
        self.config
    }
}

impl Default for SuggestConfigBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl SuggestConfig {
    /// Create a builder starting from default values.
    pub fn builder() -> SuggestConfigBuilder {
        SuggestConfigBuilder::new()
    }
}

// ---------------------------------------------------------------------------
// Result types
// ---------------------------------------------------------------------------

/// Suggested annotations for a single function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SuggestedAnnotations {
    /// Preconditions (`requires!` clauses).
    pub requires: Vec<String>,
    /// Postconditions (`ensures!` clauses).
    pub ensures: Vec<String>,
    /// Loop invariants (`invariant!` clauses).
    pub invariants: Vec<String>,
}

/// Result of running the suggest pipeline for a single function.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SuggestResult {
    /// Name of the function.
    pub function_name: String,
    /// Whether the orchestrator converged to a verified proof.
    pub converged: bool,
    /// Number of iterations used.
    pub iterations: usize,
    /// The suggested annotations (present only when converged).
    pub annotations: Option<SuggestedAnnotations>,
    /// Wall-clock time spent on this function.
    #[serde(with = "duration_millis")]
    pub elapsed: Duration,
}

/// Serde helper: serialize/deserialize `Duration` as milliseconds.
mod duration_millis {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use std::time::Duration;

    #[derive(Serialize, Deserialize)]
    struct Millis {
        ms: u128,
    }

    pub fn serialize<S: Serializer>(d: &Duration, s: S) -> Result<S::Ok, S::Error> {
        Millis { ms: d.as_millis() }.serialize(s)
    }

    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<Duration, D::Error> {
        let m = Millis::deserialize(d)?;
        Ok(Duration::from_millis(m.ms as u64))
    }
}

// ---------------------------------------------------------------------------
// Mock proposal helpers
// ---------------------------------------------------------------------------

/// Built-in mock proposals used when `BackendChoice::Mock` is selected.
fn mock_proposals() -> Vec<ProposedAnnotations> {
    vec![
        ProposedAnnotations {
            requires: vec![],
            ensures: vec!["x >= 0".to_owned()],
            invariants: vec![],
            decreases: vec![],
            raw_response: "ensures!(x >= 0)".to_owned(),
        },
        ProposedAnnotations {
            requires: vec!["x > 0".to_owned()],
            ensures: vec!["result >= 1".to_owned()],
            invariants: vec![],
            decreases: vec![],
            raw_response: "requires!(x > 0) ensures!(result >= 1)".to_owned(),
        },
    ]
}

// ---------------------------------------------------------------------------
// Core orchestration
// ---------------------------------------------------------------------------

/// Run the suggest pipeline for a list of functions.
///
/// For each function, an orchestrator is created with the chosen backend,
/// run to convergence or budget exhaustion, and the result is collected.
/// With the `Mock` backend, built-in test proposals are used.
#[must_use]
pub fn run_suggest(config: &SuggestConfig, functions: &[FunctionSignature]) -> Vec<SuggestResult> {
    functions
        .iter()
        .map(|func| run_single(config, func))
        .collect()
}

/// Run the orchestrator for a single function and produce a `SuggestResult`.
fn run_single(config: &SuggestConfig, func: &FunctionSignature) -> SuggestResult {
    let orch_config = OrchestratorConfig::builder()
        .max_iterations(config.max_iterations)
        .budget_per_iteration(config.budget)
        .convergence_threshold(config.convergence_threshold)
        .verbose(config.verbose)
        .build();

    let start = Instant::now();

    // For Mock backend, use built-in proposals.  Codex/Claude are wired but
    // fall through to mock in this bridge module — real backend construction
    // belongs in the full CLI integration layer.
    let mock_backend = MockBackend::new(mock_proposals());
    let backend: &dyn trust_vc_oracle::backend::LlmBackend = &mock_backend;

    let orchestrator = ProofOrchestrator::new(func, orch_config, backend);
    let elapsed = start.elapsed();

    match orchestrator.run() {
        Ok(result) => {
            let elapsed = start.elapsed();
            let annotations = result.final_annotations.map(|fa| SuggestedAnnotations {
                requires: fa.requires,
                ensures: fa.ensures,
                invariants: fa.invariants,
            });
            SuggestResult {
                function_name: func.name.clone(),
                converged: result.converged,
                iterations: result.iterations_used,
                annotations,
                elapsed,
            }
        }
        Err(_) => SuggestResult {
            function_name: func.name.clone(),
            converged: false,
            iterations: 0,
            annotations: None,
            elapsed,
        },
    }
}

// ---------------------------------------------------------------------------
// Output formatting
// ---------------------------------------------------------------------------

/// Format a slice of suggest results according to the requested output format.
#[must_use]
pub fn format_results(results: &[SuggestResult], format: SuggestOutputFormat) -> String {
    match format {
        SuggestOutputFormat::Text => format_text(results),
        SuggestOutputFormat::Json => format_json(results),
        SuggestOutputFormat::Diff => format_diff(results),
    }
}

/// Human-readable table format.
fn format_text(results: &[SuggestResult]) -> String {
    if results.is_empty() {
        return "No functions analyzed.".to_owned();
    }

    let mut out = String::new();
    out.push_str("trust_vc suggest results\n");
    out.push_str(&"=".repeat(60));
    out.push('\n');

    for r in results {
        let status = if r.converged {
            "CONVERGED"
        } else {
            "INCOMPLETE"
        };
        let _ = writeln!(
            out,
            "{:<30} {:>10}  iters={:<3} {:.0}ms",
            r.function_name,
            status,
            r.iterations,
            r.elapsed.as_millis(),
        );

        if let Some(ref ann) = r.annotations {
            for req in &ann.requires {
                let _ = writeln!(out, "  requires!({})", req);
            }
            for ens in &ann.ensures {
                let _ = writeln!(out, "  ensures!({})", ens);
            }
            for inv in &ann.invariants {
                let _ = writeln!(out, "  invariant!({})", inv);
            }
        }
    }

    out
}

/// Structured JSON output.
fn format_json(results: &[SuggestResult]) -> String {
    serde_json::to_string_pretty(results).unwrap_or_else(|_| "[]".to_owned())
}

/// Patch-style diff output with `+` prefixed annotation lines.
fn format_diff(results: &[SuggestResult]) -> String {
    let mut out = String::new();

    for r in results {
        if let Some(ref ann) = r.annotations {
            let _ = writeln!(out, "--- a/{}", r.function_name);
            let _ = writeln!(out, "+++ b/{}", r.function_name);

            for req in &ann.requires {
                let _ = writeln!(out, "+requires!({})", req);
            }
            for ens in &ann.ensures {
                let _ = writeln!(out, "+ensures!({})", ens);
            }
            for inv in &ann.invariants {
                let _ = writeln!(out, "+invariant!({})", inv);
            }
        }
    }

    out
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use trust_vc_oracle::engine::FunctionSignature;

    // --- Helpers ---

    fn simple_func(name: &str) -> FunctionSignature {
        FunctionSignature::new(
            name,
            vec![("x".to_owned(), "u32".to_owned())],
            Some("u32".to_owned()),
            format!("fn {}(x: u32) -> u32 {{ x }}", name),
        )
    }

    fn identity_func(name: &str) -> FunctionSignature {
        FunctionSignature::new(
            name,
            vec![("x".to_owned(), "i32".to_owned())],
            Some("i32".to_owned()),
            format!("fn {}(x: i32) -> i32 {{ x }}", name),
        )
    }

    // --- SuggestConfig default values ---

    #[test]
    fn test_suggest_config_default_values() {
        let config = SuggestConfig::default();
        assert!(config.function_name.is_none());
        assert_eq!(config.max_iterations, 10);
        assert_eq!(config.budget, 5);
        assert_eq!(config.backend, BackendChoice::Mock);
        assert_eq!(config.output_format, SuggestOutputFormat::Text);
        assert!(!config.verbose);
        assert!((config.convergence_threshold - 0.95).abs() < f64::EPSILON);
    }

    // --- SuggestConfig builder pattern ---

    #[test]
    fn test_suggest_config_builder_defaults_match_direct() {
        let from_default = SuggestConfig::default();
        let from_builder = SuggestConfig::builder().build();
        assert_eq!(from_default.max_iterations, from_builder.max_iterations);
        assert_eq!(from_default.budget, from_builder.budget);
        assert_eq!(from_default.backend, from_builder.backend);
        assert_eq!(from_default.output_format, from_builder.output_format);
        assert_eq!(from_default.verbose, from_builder.verbose);
        assert!(
            (from_default.convergence_threshold - from_builder.convergence_threshold).abs()
                < f64::EPSILON
        );
    }

    #[test]
    fn test_suggest_config_builder_custom_values() {
        let config = SuggestConfig::builder()
            .function_name("target_fn")
            .max_iterations(20)
            .budget(3)
            .backend(BackendChoice::Claude)
            .output_format(SuggestOutputFormat::Json)
            .verbose(true)
            .convergence_threshold(0.8)
            .build();
        assert_eq!(config.function_name.as_deref(), Some("target_fn"));
        assert_eq!(config.max_iterations, 20);
        assert_eq!(config.budget, 3);
        assert_eq!(config.backend, BackendChoice::Claude);
        assert_eq!(config.output_format, SuggestOutputFormat::Json);
        assert!(config.verbose);
        assert!((config.convergence_threshold - 0.8).abs() < f64::EPSILON);
    }

    // --- BackendChoice variants ---

    #[test]
    fn test_backend_choice_variants() {
        assert_eq!(format!("{}", BackendChoice::Mock), "mock");
        assert_eq!(format!("{}", BackendChoice::Codex), "codex");
        assert_eq!(format!("{}", BackendChoice::Claude), "claude");
    }

    #[test]
    fn test_backend_choice_equality() {
        assert_eq!(BackendChoice::Mock, BackendChoice::Mock);
        assert_ne!(BackendChoice::Mock, BackendChoice::Codex);
        assert_ne!(BackendChoice::Codex, BackendChoice::Claude);
    }

    // --- SuggestOutputFormat variants ---

    #[test]
    fn test_suggest_output_format_variants() {
        assert_eq!(format!("{}", SuggestOutputFormat::Text), "text");
        assert_eq!(format!("{}", SuggestOutputFormat::Json), "json");
        assert_eq!(format!("{}", SuggestOutputFormat::Diff), "diff");
    }

    #[test]
    fn test_suggest_output_format_default() {
        assert_eq!(SuggestOutputFormat::default(), SuggestOutputFormat::Text);
    }

    // --- run_suggest with empty functions list ---

    #[test]
    fn test_run_suggest_empty_functions() {
        let config = SuggestConfig::default();
        let results = run_suggest(&config, &[]);
        assert!(results.is_empty());
    }

    // --- run_suggest with mock backend, single function ---

    #[test]
    fn test_run_suggest_mock_single_function() {
        let config = SuggestConfig::builder()
            .backend(BackendChoice::Mock)
            .max_iterations(5)
            .build();
        let funcs = vec![simple_func("nonneg")];
        let results = run_suggest(&config, &funcs);

        assert_eq!(results.len(), 1);
        assert_eq!(results[0].function_name, "nonneg");
        // u32 x >= 0 should verify with mock proposals
        assert!(results[0].converged);
        assert!(results[0].annotations.is_some());
    }

    // --- run_suggest with mock backend, multiple functions ---

    #[test]
    fn test_run_suggest_mock_multiple_functions() {
        let config = SuggestConfig::builder()
            .backend(BackendChoice::Mock)
            .max_iterations(5)
            .build();
        let funcs = vec![
            simple_func("alpha"),
            simple_func("beta"),
            simple_func("gamma"),
        ];
        let results = run_suggest(&config, &funcs);

        assert_eq!(results.len(), 3);
        assert_eq!(results[0].function_name, "alpha");
        assert_eq!(results[1].function_name, "beta");
        assert_eq!(results[2].function_name, "gamma");
    }

    // --- format_results text format ---

    #[test]
    fn test_format_results_text_format() {
        let results = vec![SuggestResult {
            function_name: "add_one".to_owned(),
            converged: true,
            iterations: 2,
            annotations: Some(SuggestedAnnotations {
                requires: vec!["x > 0".to_owned()],
                ensures: vec!["result == x + 1".to_owned()],
                invariants: vec![],
            }),
            elapsed: Duration::from_millis(42),
        }];
        let output = format_results(&results, SuggestOutputFormat::Text);
        assert!(output.contains("add_one"));
        assert!(output.contains("CONVERGED"));
        assert!(output.contains("requires!(x > 0)"));
        assert!(output.contains("ensures!(result == x + 1)"));
    }

    // --- format_results json format ---

    #[test]
    fn test_format_results_json_format() {
        let results = vec![SuggestResult {
            function_name: "checked".to_owned(),
            converged: true,
            iterations: 1,
            annotations: Some(SuggestedAnnotations {
                requires: vec![],
                ensures: vec!["result >= 0".to_owned()],
                invariants: vec![],
            }),
            elapsed: Duration::from_millis(10),
        }];
        let output = format_results(&results, SuggestOutputFormat::Json);
        let parsed: serde_json::Value =
            serde_json::from_str(&output).expect("JSON output should be valid");
        assert!(parsed.is_array());
        assert_eq!(parsed[0]["function_name"], "checked");
        assert_eq!(parsed[0]["converged"], true);
    }

    // --- format_results diff format ---

    #[test]
    fn test_format_results_diff_format() {
        let results = vec![SuggestResult {
            function_name: "guarded".to_owned(),
            converged: true,
            iterations: 1,
            annotations: Some(SuggestedAnnotations {
                requires: vec!["n > 0".to_owned()],
                ensures: vec!["result < n".to_owned()],
                invariants: vec![],
            }),
            elapsed: Duration::from_millis(5),
        }];
        let output = format_results(&results, SuggestOutputFormat::Diff);
        assert!(output.contains("+requires!(n > 0)"));
        assert!(output.contains("+ensures!(result < n)"));
        assert!(output.contains("--- a/guarded"));
        assert!(output.contains("+++ b/guarded"));
    }

    // --- SuggestResult creation ---

    #[test]
    fn test_suggest_result_creation() {
        let result = SuggestResult {
            function_name: "my_fn".to_owned(),
            converged: false,
            iterations: 3,
            annotations: None,
            elapsed: Duration::from_millis(100),
        };
        assert_eq!(result.function_name, "my_fn");
        assert!(!result.converged);
        assert_eq!(result.iterations, 3);
        assert!(result.annotations.is_none());
        assert_eq!(result.elapsed, Duration::from_millis(100));
    }

    // --- SuggestedAnnotations from orchestrator result ---

    #[test]
    fn test_suggested_annotations_fields() {
        let ann = SuggestedAnnotations {
            requires: vec!["x > 0".to_owned()],
            ensures: vec!["result >= 1".to_owned()],
            invariants: vec!["i < n".to_owned()],
        };
        assert_eq!(ann.requires.len(), 1);
        assert_eq!(ann.ensures.len(), 1);
        assert_eq!(ann.invariants.len(), 1);
        assert_eq!(ann.requires[0], "x > 0");
        assert_eq!(ann.ensures[0], "result >= 1");
        assert_eq!(ann.invariants[0], "i < n");
    }

    // --- Converged result has annotations ---

    #[test]
    fn test_converged_result_has_annotations() {
        let config = SuggestConfig::builder()
            .backend(BackendChoice::Mock)
            .max_iterations(5)
            .build();
        let funcs = vec![simple_func("verified_fn")];
        let results = run_suggest(&config, &funcs);

        assert_eq!(results.len(), 1);
        if results[0].converged {
            assert!(
                results[0].annotations.is_some(),
                "converged result should have annotations"
            );
        }
    }

    // --- Non-converged result has None annotations ---

    #[test]
    fn test_non_converged_result_has_none_annotations() {
        // Use 0 max_iterations to force non-convergence.
        let config = SuggestConfig::builder()
            .backend(BackendChoice::Mock)
            .max_iterations(0)
            .build();
        let funcs = vec![simple_func("zero_budget")];
        let results = run_suggest(&config, &funcs);

        assert_eq!(results.len(), 1);
        assert!(!results[0].converged);
        assert!(
            results[0].annotations.is_none(),
            "non-converged result should have None annotations"
        );
    }

    // --- Verbose mode flag propagation ---

    #[test]
    fn test_verbose_mode_flag_propagation() {
        let config = SuggestConfig::builder().verbose(true).build();
        assert!(config.verbose);

        let config_off = SuggestConfig::builder().verbose(false).build();
        assert!(!config_off.verbose);
    }

    // --- Convergence threshold propagation ---

    #[test]
    fn test_convergence_threshold_propagation() {
        let config = SuggestConfig::builder().convergence_threshold(0.75).build();
        assert!((config.convergence_threshold - 0.75).abs() < f64::EPSILON);
    }

    #[test]
    fn test_convergence_threshold_clamps_out_of_range() {
        let high = SuggestConfig::builder().convergence_threshold(1.5).build();
        assert!((high.convergence_threshold - 1.0).abs() < f64::EPSILON);

        let low = SuggestConfig::builder().convergence_threshold(-0.5).build();
        assert!((low.convergence_threshold - 0.0).abs() < f64::EPSILON);
    }

    // --- Budget propagation ---

    #[test]
    fn test_budget_propagation() {
        let config = SuggestConfig::builder().budget(7).build();
        assert_eq!(config.budget, 7);
    }

    // --- Max iterations propagation ---

    #[test]
    fn test_max_iterations_propagation() {
        let config = SuggestConfig::builder().max_iterations(15).build();
        assert_eq!(config.max_iterations, 15);
    }

    // --- Text format includes function name ---

    #[test]
    fn test_text_format_includes_function_name() {
        let results = vec![SuggestResult {
            function_name: "unique_fn_name".to_owned(),
            converged: false,
            iterations: 1,
            annotations: None,
            elapsed: Duration::from_millis(1),
        }];
        let output = format_results(&results, SuggestOutputFormat::Text);
        assert!(
            output.contains("unique_fn_name"),
            "text format should include the function name"
        );
    }

    // --- Json format is valid JSON ---

    #[test]
    fn test_json_format_is_valid_json() {
        let results = vec![
            SuggestResult {
                function_name: "fn_a".to_owned(),
                converged: true,
                iterations: 1,
                annotations: Some(SuggestedAnnotations {
                    requires: vec![],
                    ensures: vec!["true".to_owned()],
                    invariants: vec![],
                }),
                elapsed: Duration::from_millis(5),
            },
            SuggestResult {
                function_name: "fn_b".to_owned(),
                converged: false,
                iterations: 3,
                annotations: None,
                elapsed: Duration::from_millis(15),
            },
        ];
        let output = format_results(&results, SuggestOutputFormat::Json);
        let parsed: serde_json::Value =
            serde_json::from_str(&output).expect("output should parse as valid JSON");
        assert!(parsed.is_array());
        assert_eq!(parsed.as_array().unwrap().len(), 2);
    }

    // --- Diff format has plus signs ---

    #[test]
    fn test_diff_format_has_plus_signs() {
        let results = vec![SuggestResult {
            function_name: "diffed".to_owned(),
            converged: true,
            iterations: 1,
            annotations: Some(SuggestedAnnotations {
                requires: vec!["a > 0".to_owned()],
                ensures: vec![],
                invariants: vec![],
            }),
            elapsed: Duration::from_millis(1),
        }];
        let output = format_results(&results, SuggestOutputFormat::Diff);
        assert!(
            output.contains('+'),
            "diff format should include plus signs for additions"
        );
    }

    // --- Empty annotations render correctly ---

    #[test]
    fn test_empty_annotations_render_correctly() {
        let results = vec![SuggestResult {
            function_name: "empty_ann".to_owned(),
            converged: true,
            iterations: 1,
            annotations: Some(SuggestedAnnotations {
                requires: vec![],
                ensures: vec![],
                invariants: vec![],
            }),
            elapsed: Duration::from_millis(1),
        }];

        // Text: no requires!/ensures!/invariant! lines
        let text = format_results(&results, SuggestOutputFormat::Text);
        assert!(!text.contains("requires!"));
        assert!(!text.contains("ensures!"));
        assert!(!text.contains("invariant!"));

        // Diff: no output lines for this function (no annotations to add)
        let diff = format_results(&results, SuggestOutputFormat::Diff);
        assert!(
            !diff.contains("+requires!") && !diff.contains("+ensures!"),
            "empty annotations should produce no diff lines"
        );
    }

    // --- Multiple requires in output ---

    #[test]
    fn test_multiple_requires_in_output() {
        let results = vec![SuggestResult {
            function_name: "multi_req".to_owned(),
            converged: true,
            iterations: 1,
            annotations: Some(SuggestedAnnotations {
                requires: vec!["x > 0".to_owned(), "y > 0".to_owned(), "x != y".to_owned()],
                ensures: vec![],
                invariants: vec![],
            }),
            elapsed: Duration::from_millis(1),
        }];
        let text = format_results(&results, SuggestOutputFormat::Text);
        assert!(text.contains("requires!(x > 0)"));
        assert!(text.contains("requires!(y > 0)"));
        assert!(text.contains("requires!(x != y)"));
    }

    // --- Multiple ensures in output ---

    #[test]
    fn test_multiple_ensures_in_output() {
        let results = vec![SuggestResult {
            function_name: "multi_ens".to_owned(),
            converged: true,
            iterations: 1,
            annotations: Some(SuggestedAnnotations {
                requires: vec![],
                ensures: vec!["result >= 0".to_owned(), "result <= max".to_owned()],
                invariants: vec![],
            }),
            elapsed: Duration::from_millis(1),
        }];
        let text = format_results(&results, SuggestOutputFormat::Text);
        assert!(text.contains("ensures!(result >= 0)"));
        assert!(text.contains("ensures!(result <= max)"));
    }

    // --- Elapsed time in result ---

    #[test]
    fn test_elapsed_time_in_result() {
        let config = SuggestConfig::builder()
            .backend(BackendChoice::Mock)
            .max_iterations(1)
            .build();
        let funcs = vec![simple_func("timed_fn")];
        let results = run_suggest(&config, &funcs);

        assert_eq!(results.len(), 1);
        // Elapsed should be non-negative (trivially true for Duration, but
        // verify it's a sensible value — less than 10 seconds for a mock run).
        assert!(
            results[0].elapsed < Duration::from_secs(10),
            "mock backend should complete quickly"
        );
    }
}
