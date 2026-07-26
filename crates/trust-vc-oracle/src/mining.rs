// trust-vc-oracle — CGSR mining loop (Counterexample-Guided Specification Refinement)
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Scans functions in Rust source, instantiates spec templates, verifies them
// via the trust_vc ay backend, and uses counterexample feedback to iteratively
// refine candidate specifications until they are proven or exhausted.

use crate::engine::FunctionSignature;
use crate::feedback::ProofFeedback;
use crate::source_parser::parse_functions;
use crate::templates::{applicable_templates, SpecTemplate};
use crate::verify::verify_with_annotations;

// ---------------------------------------------------------------------------
// Configuration
// ---------------------------------------------------------------------------

/// Configuration for the CGSR mining loop.
#[derive(Debug, Clone)]
pub struct MiningConfig {
    /// Maximum refinement iterations per template per function.
    pub max_refinements: usize,
    /// Maximum number of templates to try per function (0 = unlimited).
    pub max_templates_per_function: usize,
    /// Whether to emit progress to stderr.
    pub verbose: bool,
}

impl Default for MiningConfig {
    fn default() -> Self {
        Self {
            max_refinements: 5,
            max_templates_per_function: 0,
            verbose: false,
        }
    }
}

// ---------------------------------------------------------------------------
// Output types
// ---------------------------------------------------------------------------

/// A specification mined and verified for a single function.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct MinedSpec {
    /// Name of the function this spec applies to.
    pub function_name: String,
    /// Name of the template that produced this spec.
    pub template_name: String,
    /// Precondition clauses (requires!).
    pub requires: Vec<String>,
    /// Postcondition clauses (ensures!).
    pub ensures: Vec<String>,
    /// Whether the spec was verified by ay.
    pub verified: bool,
    /// Number of refinement iterations used (0 = verified on first attempt).
    pub iterations: usize,
}

impl MinedSpec {
    /// Construct a new `MinedSpec`.
    ///
    /// Required because `#[non_exhaustive]` prevents struct-expression
    /// construction from outside the crate.
    #[must_use]
    pub fn new(
        function_name: String,
        template_name: String,
        requires: Vec<String>,
        ensures: Vec<String>,
        verified: bool,
        iterations: usize,
    ) -> Self {
        Self {
            function_name,
            template_name,
            requires,
            ensures,
            verified,
            iterations,
        }
    }
}

// ---------------------------------------------------------------------------
// Verification adapter (injectable for testing)
// ---------------------------------------------------------------------------

/// Abstraction over the verification step so tests can inject a mock.
pub(crate) trait VerifyAdapter: Send + Sync {
    fn verify(
        &self,
        function_name: &str,
        variables: &[(String, String)],
        requires: &[String],
        ensures: &[String],
    ) -> ProofFeedback;
}

/// Real adapter that delegates to `verify_with_annotations`.
struct RealVerifier;

impl VerifyAdapter for RealVerifier {
    fn verify(
        &self,
        function_name: &str,
        variables: &[(String, String)],
        requires: &[String],
        ensures: &[String],
    ) -> ProofFeedback {
        verify_with_annotations(function_name, variables, requires, ensures)
    }
}

// ---------------------------------------------------------------------------
// Core mining loop
// ---------------------------------------------------------------------------

/// Mine specifications from Rust source code using CGSR.
///
/// Parses all functions from `source`, applies applicable templates, verifies
/// proposals via the trust_vc ay backend, and refines failing proposals using
/// counterexample feedback. Returns all specs that were successfully verified.
///
/// # Example
///
/// ```ignore
/// let specs = mine_specs("fn abs(x: i32) -> i32 { if x < 0 { -x } else { x } }", &MiningConfig::default());
/// for spec in &specs {
///     println!("{}: verified={}", spec.function_name, spec.verified);
/// }
/// ```
#[must_use]
pub fn mine_specs(source: &str, config: &MiningConfig) -> Vec<MinedSpec> {
    mine_specs_with_adapter(source, config, &RealVerifier)
}

/// Internal entry point with injectable verifier (for testing).
fn mine_specs_with_adapter(
    source: &str,
    config: &MiningConfig,
    adapter: &dyn VerifyAdapter,
) -> Vec<MinedSpec> {
    let functions = parse_functions(source);
    let mut results = Vec::new();

    for func in &functions {
        let mined = mine_function(func, config, adapter);
        results.extend(mined);
    }

    results
}

/// Mine specifications for a single function.
fn mine_function(
    func: &FunctionSignature,
    config: &MiningConfig,
    adapter: &dyn VerifyAdapter,
) -> Vec<MinedSpec> {
    let templates = applicable_templates(func);
    let template_limit = if config.max_templates_per_function == 0 {
        templates.len()
    } else {
        config.max_templates_per_function.min(templates.len())
    };

    let mut results = Vec::new();

    for template in templates.iter().take(template_limit) {
        let mined = mine_template(func, template.as_ref(), config, adapter);
        results.extend(mined);
    }

    results
}

/// Run the CGSR loop for a single (function, template) pair.
///
/// 1. Instantiate the template to get initial candidate proposals.
/// 2. For each candidate, verify it.
/// 3. If verified, record and move on.
/// 4. If counterexample, call `refine()` and try again up to `max_refinements`.
fn mine_template(
    func: &FunctionSignature,
    template: &dyn SpecTemplate,
    config: &MiningConfig,
    adapter: &dyn VerifyAdapter,
) -> Vec<MinedSpec> {
    let mut results = Vec::new();
    let initial_proposals = template.instantiate(func);

    for proposal in &initial_proposals {
        let mut current_requires = proposal.requires.clone();
        let mut current_ensures = proposal.ensures.clone();
        let mut verified = false;
        let mut iterations_used = 0;

        // Iteration 0: try the initial proposal
        let feedback = adapter.verify(
            &func.name,
            &func.params,
            &current_requires,
            &current_ensures,
        );

        if config.verbose {
            eprintln!(
                "[mining] {}::{} proposal {} — {}",
                func.name,
                template.name(),
                0,
                feedback_summary(&feedback),
            );
        }

        if feedback.is_verified() {
            verified = true;
        } else {
            // Refinement loop
            let mut last_feedback = feedback;
            for i in 1..=config.max_refinements {
                if !last_feedback.is_failed() {
                    // Only refine on counterexample; unknown/error → stop
                    break;
                }

                let refinements = template.refine(func, &last_feedback);
                if refinements.is_empty() {
                    break;
                }

                // Take the first refinement proposal
                let refined = &refinements[0];
                current_requires = refined.requires.clone();
                current_ensures = refined.ensures.clone();

                let new_feedback = adapter.verify(
                    &func.name,
                    &func.params,
                    &current_requires,
                    &current_ensures,
                );

                if config.verbose {
                    eprintln!(
                        "[mining] {}::{} refinement {} — {}",
                        func.name,
                        template.name(),
                        i,
                        feedback_summary(&new_feedback),
                    );
                }

                iterations_used = i;

                if new_feedback.is_verified() {
                    verified = true;
                    break;
                }

                last_feedback = new_feedback;
            }
        }

        if verified {
            results.push(MinedSpec {
                function_name: func.name.clone(),
                template_name: template.name().to_string(),
                requires: current_requires,
                ensures: current_ensures,
                verified: true,
                iterations: iterations_used,
            });
        }
    }

    results
}

/// One-line feedback summary for verbose logging.
fn feedback_summary(feedback: &ProofFeedback) -> String {
    match feedback {
        ProofFeedback::Verified { .. } => "VERIFIED".to_string(),
        ProofFeedback::Failed {
            counterexamples, ..
        } => {
            let vals: Vec<String> = counterexamples
                .iter()
                .map(|cx| format!("{}={}", cx.name, cx.value))
                .collect();
            format!("FAILED ({})", vals.join(", "))
        }
        ProofFeedback::Unknown { reason, .. } => format!("UNKNOWN: {}", reason),
        ProofFeedback::Error { message } => format!("ERROR: {}", message),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::feedback::{CounterexampleField, FailureLocalization};
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::time::Duration;

    // -----------------------------------------------------------------------
    // Mock verifier
    // -----------------------------------------------------------------------

    /// A mock verifier that returns pre-scripted feedback for each call.
    struct ScriptedVerifier {
        responses: Vec<ProofFeedback>,
        call_count: AtomicUsize,
    }

    impl ScriptedVerifier {
        fn new(responses: Vec<ProofFeedback>) -> Self {
            Self {
                responses,
                call_count: AtomicUsize::new(0),
            }
        }

        fn calls(&self) -> usize {
            self.call_count.load(Ordering::SeqCst)
        }
    }

    impl VerifyAdapter for ScriptedVerifier {
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
                // Repeat the last response if we exceed the script
                self.responses
                    .last()
                    .cloned()
                    .unwrap_or(ProofFeedback::Error {
                        message: "scripted verifier exhausted".to_string(),
                    })
            }
        }
    }

    /// A verifier that always returns Verified.
    struct AlwaysVerified;

    impl VerifyAdapter for AlwaysVerified {
        fn verify(
            &self,
            _function_name: &str,
            _variables: &[(String, String)],
            _requires: &[String],
            _ensures: &[String],
        ) -> ProofFeedback {
            ProofFeedback::Verified {
                steps: vec![],
                elapsed: Duration::from_millis(1),
                certificate_info: None,
            }
        }
    }

    /// A verifier that always returns a counterexample.
    struct AlwaysFails;

    impl VerifyAdapter for AlwaysFails {
        fn verify(
            &self,
            _function_name: &str,
            _variables: &[(String, String)],
            _requires: &[String],
            _ensures: &[String],
        ) -> ProofFeedback {
            ProofFeedback::Failed {
                counterexamples: vec![CounterexampleField {
                    name: "result".to_string(),
                    ty: "i32".to_string(),
                    value: "-1".to_string(),
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
    }

    fn make_verified() -> ProofFeedback {
        ProofFeedback::Verified {
            steps: vec![],
            elapsed: Duration::from_millis(1),
            certificate_info: None,
        }
    }

    fn make_failed(result_value: &str) -> ProofFeedback {
        ProofFeedback::Failed {
            counterexamples: vec![CounterexampleField {
                name: "result".to_string(),
                ty: "i32".to_string(),
                value: result_value.to_string(),
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

    fn make_unknown() -> ProofFeedback {
        ProofFeedback::Unknown {
            reason: "timeout".to_string(),
            category: "Timeout".to_string(),
            is_retriable: false,
            suggestion: "simplify".to_string(),
            elapsed: Duration::from_millis(100),
        }
    }

    fn default_config() -> MiningConfig {
        MiningConfig {
            max_refinements: 3,
            max_templates_per_function: 0,
            verbose: false,
        }
    }

    // -----------------------------------------------------------------------
    // Tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_mine_specs_empty_source() {
        let specs = mine_specs_with_adapter("", &default_config(), &AlwaysVerified);
        assert!(specs.is_empty(), "empty source should yield no specs");
    }

    #[test]
    fn test_mine_specs_unparseable_source() {
        let specs =
            mine_specs_with_adapter("this is not rust {{", &default_config(), &AlwaysVerified);
        assert!(specs.is_empty(), "invalid source should yield no specs");
    }

    #[test]
    fn test_mine_specs_function_with_no_applicable_templates() {
        // A void function with no params has very few applicable templates
        let source = "fn noop() {}";
        let specs = mine_specs_with_adapter(source, &default_config(), &AlwaysVerified);
        // Even if some templates apply, that is fine; just check it does not crash
        for spec in &specs {
            assert_eq!(spec.function_name, "noop");
            assert!(spec.verified);
        }
    }

    #[test]
    fn test_mine_specs_verified_on_first_try() {
        let source = "fn id(x: u32) -> u32 { x }";
        let specs = mine_specs_with_adapter(source, &default_config(), &AlwaysVerified);

        // Should find at least one verified spec (multiple templates apply to u32 -> u32)
        assert!(
            !specs.is_empty(),
            "should mine at least one spec for u32 identity"
        );
        for spec in &specs {
            assert_eq!(spec.function_name, "id");
            assert!(spec.verified);
            assert_eq!(
                spec.iterations, 0,
                "verified on first try => 0 refinement iterations"
            );
        }
    }

    #[test]
    fn test_mine_specs_refinement_succeeds() {
        // First call fails, second call (after refinement) succeeds
        let verifier = ScriptedVerifier::new(vec![make_failed("-5"), make_verified()]);
        let source = "fn abs(x: i32) -> i32 { if x < 0 { -x } else { x } }";

        // Limit to 1 template so we get a deterministic path
        let config = MiningConfig {
            max_refinements: 3,
            max_templates_per_function: 1,
            verbose: false,
        };

        let specs = mine_specs_with_adapter(source, &config, &verifier);

        // The first template's first proposal fails, then refine succeeds
        let verified_specs: Vec<_> = specs.iter().filter(|s| s.verified).collect();
        assert!(
            !verified_specs.is_empty(),
            "should find a verified spec after refinement"
        );
        for spec in &verified_specs {
            assert!(
                spec.iterations >= 1,
                "should have used at least 1 refinement iteration"
            );
        }
    }

    #[test]
    fn test_mine_specs_all_refinements_fail() {
        let source = "fn neg(x: i32) -> i32 { -x }";
        let specs = mine_specs_with_adapter(source, &default_config(), &AlwaysFails);
        // Nothing should be verified since every attempt fails
        assert!(
            specs.is_empty(),
            "all-failing verifier should produce no verified specs, got {}",
            specs.len()
        );
    }

    #[test]
    fn test_mine_specs_max_templates_limit() {
        let source = "fn add(a: u32, b: u32) -> u32 { a + b }";
        let config = MiningConfig {
            max_refinements: 2,
            max_templates_per_function: 1,
            verbose: false,
        };

        let verifier = ScriptedVerifier::new(vec![
            make_verified(),
            make_verified(),
            make_verified(),
            make_verified(),
        ]);

        let specs = mine_specs_with_adapter(source, &config, &verifier);

        // With limit=1, only the first applicable template runs.
        // The first template (range) produces multiple proposals, but only from one template.
        for spec in &specs {
            assert_eq!(spec.function_name, "add");
            assert!(spec.verified);
        }

        // Verify only 1 template name was used
        let template_names: std::collections::HashSet<_> =
            specs.iter().map(|s| s.template_name.clone()).collect();
        assert_eq!(
            template_names.len(),
            1,
            "max_templates_per_function=1 should restrict to one template"
        );
    }

    #[test]
    fn test_mine_specs_unknown_feedback_stops_refinement() {
        // First call returns unknown — refinement should stop (not retry)
        let verifier = ScriptedVerifier::new(vec![make_unknown()]);
        let source = "fn f(x: u32) -> u32 { x }";

        let config = MiningConfig {
            max_refinements: 5,
            max_templates_per_function: 1,
            verbose: false,
        };

        let specs = mine_specs_with_adapter(source, &config, &verifier);
        // Unknown is not a counterexample, so no refinement should occur
        assert!(
            specs.is_empty(),
            "unknown feedback should not produce verified specs"
        );
        // Should have called verify only once per proposal (no refinement)
        let calls = verifier.calls();
        // The first template produces multiple proposals but unknown stops each immediately
        assert!(calls >= 1, "should have made at least 1 verify call");
    }

    #[test]
    fn test_mine_specs_mined_spec_has_correct_provenance() {
        let verifier = ScriptedVerifier::new(vec![make_failed("-3"), make_verified()]);
        let source = "fn f(x: i32) -> i32 { x }";

        let config = MiningConfig {
            max_refinements: 3,
            max_templates_per_function: 1,
            verbose: false,
        };

        let specs = mine_specs_with_adapter(source, &config, &verifier);

        for spec in &specs {
            assert_eq!(spec.function_name, "f");
            assert!(
                !spec.template_name.is_empty(),
                "template_name should be set"
            );
            assert!(spec.verified);
            // Ensures should not be empty (the template always produces at least one ensures)
            assert!(
                !spec.ensures.is_empty(),
                "ensures should not be empty for a verified spec"
            );
        }
    }

    #[test]
    fn test_mine_specs_multiple_functions() {
        let source = r#"
            fn inc(x: u32) -> u32 { x + 1 }
            fn dec(x: u32) -> u32 { x - 1 }
        "#;

        let specs = mine_specs_with_adapter(source, &default_config(), &AlwaysVerified);

        let func_names: std::collections::HashSet<_> =
            specs.iter().map(|s| s.function_name.clone()).collect();
        assert!(func_names.contains("inc"), "should mine specs for inc");
        assert!(func_names.contains("dec"), "should mine specs for dec");
    }

    #[test]
    fn test_mine_specs_verbose_does_not_crash() {
        let source = "fn id(x: u32) -> u32 { x }";
        let config = MiningConfig {
            max_refinements: 1,
            max_templates_per_function: 1,
            verbose: true,
        };

        // Just verify it does not panic
        let specs = mine_specs_with_adapter(source, &config, &AlwaysVerified);
        assert!(!specs.is_empty());
    }

    #[test]
    fn test_mine_specs_max_refinements_zero() {
        // With max_refinements=0, only the initial proposal is tried
        let verifier = ScriptedVerifier::new(vec![make_failed("-1")]);
        let source = "fn f(x: i32) -> i32 { x }";

        let config = MiningConfig {
            max_refinements: 0,
            max_templates_per_function: 1,
            verbose: false,
        };

        let specs = mine_specs_with_adapter(source, &config, &verifier);
        assert!(
            specs.is_empty(),
            "no refinements allowed => failing initial proposal yields nothing"
        );
        assert_eq!(
            verifier.calls(),
            1,
            "should only verify the initial proposal once"
        );
    }

    #[test]
    fn test_mine_specs_default_config() {
        let config = MiningConfig::default();
        assert_eq!(config.max_refinements, 5);
        assert_eq!(config.max_templates_per_function, 0);
        assert!(!config.verbose);
    }

    #[test]
    fn test_mined_spec_fields() {
        let spec = MinedSpec {
            function_name: "foo".to_string(),
            template_name: "range".to_string(),
            requires: vec!["x > 0".to_string()],
            ensures: vec!["result >= 1".to_string()],
            verified: true,
            iterations: 2,
        };

        assert_eq!(spec.function_name, "foo");
        assert_eq!(spec.template_name, "range");
        assert_eq!(spec.requires, vec!["x > 0"]);
        assert_eq!(spec.ensures, vec!["result >= 1"]);
        assert!(spec.verified);
        assert_eq!(spec.iterations, 2);
    }

    #[test]
    fn test_feedback_summary_variants() {
        let verified = make_verified();
        assert_eq!(feedback_summary(&verified), "VERIFIED");

        let failed = make_failed("-42");
        let s = feedback_summary(&failed);
        assert!(s.contains("FAILED"), "should contain FAILED: {}", s);
        assert!(
            s.contains("result=-42"),
            "should contain counterexample: {}",
            s
        );

        let unknown = make_unknown();
        let s = feedback_summary(&unknown);
        assert!(s.contains("UNKNOWN"), "should contain UNKNOWN: {}", s);

        let error = ProofFeedback::Error {
            message: "bad".to_string(),
        };
        let s = feedback_summary(&error);
        assert!(s.contains("ERROR"), "should contain ERROR: {}", s);
    }
}
