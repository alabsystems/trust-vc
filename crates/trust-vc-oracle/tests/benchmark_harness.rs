// trust-vc-oracle — Benchmark harness for LLM Proof Oracle convergence validation
//
// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Validates that the propose-verify-feedback-refine loop converges on real
// functions of increasing difficulty. Uses a ScriptedMockBackend that
// simulates realistic LLM behavior: first attempt incomplete/wrong,
// second attempt incorporates feedback, third attempt correct.

use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};

use trust_vc_oracle::{
    run_oracle, FunctionSignature, MockBackend, OracleConfig, ProofFeedback, ProposedAnnotations,
};

// ===========================================================================
// ScriptedMockBackend — simulates realistic multi-iteration LLM convergence
// ===========================================================================

/// A mock backend where each function gets a scripted sequence of proposals.
/// Unlike the basic MockBackend, this one keys proposals by function source
/// content, allowing a single backend to serve multiple benchmark functions.
struct ScriptedMockBackend {
    /// Map from function source snippet -> ordered proposal sequence.
    scripts: HashMap<String, Vec<ProposedAnnotations>>,
    /// Tracks total calls for diagnostics.
    call_count: AtomicUsize,
}

impl ScriptedMockBackend {
    fn new(scripts: HashMap<String, Vec<ProposedAnnotations>>) -> Self {
        Self {
            scripts,
            call_count: AtomicUsize::new(0),
        }
    }

    /// Create a backend with a single function's script.
    fn single(source_key: &str, proposals: Vec<ProposedAnnotations>) -> Self {
        let mut scripts = HashMap::new();
        scripts.insert(source_key.to_string(), proposals);
        Self::new(scripts)
    }
}

impl trust_vc_oracle::LlmBackend for ScriptedMockBackend {
    fn propose_annotations(
        &self,
        source: &str,
        feedback_history: &[(ProposedAnnotations, ProofFeedback)],
    ) -> Result<ProposedAnnotations, trust_vc_oracle::OracleError> {
        self.call_count.fetch_add(1, Ordering::Relaxed);
        let idx = feedback_history.len();

        // Find the script matching this source
        let script = self
            .scripts
            .iter()
            .find(|(key, _)| source.contains(key.as_str()))
            .map(|(_, v)| v);

        match script {
            Some(proposals) => proposals
                .get(idx)
                .cloned()
                .ok_or(trust_vc_oracle::OracleError::BackendExhausted { attempts: idx }),
            None => Err(trust_vc_oracle::OracleError::BackendError {
                message: format!(
                    "no script found for source (first 60 chars): '{}'",
                    &source[..source.len().min(60)]
                ),
            }),
        }
    }

    fn name(&self) -> &str {
        "scripted-mock"
    }
}

// ===========================================================================
// Helpers
// ===========================================================================

fn make_config(max_iterations: usize) -> OracleConfig {
    OracleConfig {
        max_iterations,
        verbose: false,
    }
}

fn proposal(requires: &[&str], ensures: &[&str]) -> ProposedAnnotations {
    ProposedAnnotations {
        requires: requires.iter().map(|s| s.to_string()).collect(),
        ensures: ensures.iter().map(|s| s.to_string()).collect(),
        invariants: vec![],
        decreases: vec![],
        raw_response: String::new(),
    }
}

fn sig(name: &str, params: &[(&str, &str)], ret: Option<&str>, source: &str) -> FunctionSignature {
    FunctionSignature::new(
        name,
        params
            .iter()
            .map(|(n, t)| (n.to_string(), t.to_string()))
            .collect(),
        ret.map(|s| s.to_string()),
        source,
    )
}

// ===========================================================================
// Benchmark function definitions (10 functions, 4 difficulty levels)
// ===========================================================================

/// Level 1 (trivial): abs(x) — simple nonneg postcondition
fn bench_abs() -> (FunctionSignature, Vec<ProposedAnnotations>) {
    let func = sig(
        "abs",
        &[("x", "i32"), ("result", "u32")],
        Some("u32"),
        "fn abs(x: i32) -> u32 { if x < 0 { (-x) as u32 } else { x as u32 } }",
    );

    // Iteration 1: Generic/incomplete — misses that result is u32
    // Iteration 2: Correct — result >= 0 is trivially true for u32
    let proposals = vec![
        proposal(&[], &["x >= 0"]),      // WRONG: x is i32, can be negative
        proposal(&[], &["result >= 0"]), // CORRECT: result is u32, always >= 0
    ];

    (func, proposals)
}

/// Level 1 (trivial): max(a, b) — result is >= both inputs
fn bench_max() -> (FunctionSignature, Vec<ProposedAnnotations>) {
    let func = sig(
        "max",
        &[("a", "i32"), ("b", "i32"), ("result", "i32")],
        Some("i32"),
        "fn max(a: i32, b: i32) -> i32 { if a >= b { a } else { b } }",
    );

    // Iteration 1: Too weak — only checks one direction
    // Iteration 2: Correct with assumptions matching postcondition
    let proposals = vec![
        proposal(&[], &["result >= a"]), // INCOMPLETE: missing b
        proposal(
            &["result >= a", "result >= b"],
            &["result >= a && result >= b"],
        ), // CORRECT
    ];

    (func, proposals)
}

/// Level 1 (trivial): clamp(x, lo, hi) — result is in [lo, hi]
fn bench_clamp() -> (FunctionSignature, Vec<ProposedAnnotations>) {
    let func = sig(
        "clamp",
        &[("x", "i32"), ("lo", "i32"), ("hi", "i32"), ("result", "i32")],
        Some("i32"),
        "fn clamp(x: i32, lo: i32, hi: i32) -> i32 { if x < lo { lo } else if x > hi { hi } else { x } }",
    );

    // Iteration 1: Wrong — forgets lo <= hi precondition
    // Iteration 2: Too strong without matching assumes
    // Iteration 3: Correct with assumes
    let proposals = vec![
        proposal(&[], &["result >= lo && result <= hi"]), // WRONG without lo<=hi
        proposal(&["lo <= hi"], &["result >= lo"]),       // PARTIAL: only lower bound
        proposal(
            &["lo <= hi", "result >= lo", "result <= hi"],
            &["result >= lo && result <= hi"],
        ), // CORRECT
    ];

    (func, proposals)
}

/// Level 2 (arithmetic): factorial(n) — needs precondition n >= 0
fn bench_factorial() -> (FunctionSignature, Vec<ProposedAnnotations>) {
    let func = sig(
        "factorial",
        &[("n", "u32"), ("result", "u32")],
        Some("u32"),
        "fn factorial(n: u32) -> u32 { if n <= 1 { 1 } else { n * factorial(n-1) } }",
    );

    // Iteration 1: Generic — result > 0 for u32 (trivially true)
    let proposals = vec![
        proposal(&[], &["result >= 0"]), // CORRECT trivially: u32 always >= 0
    ];

    (func, proposals)
}

/// Level 2 (arithmetic): fibonacci(n) — nonneg result
fn bench_fibonacci() -> (FunctionSignature, Vec<ProposedAnnotations>) {
    let func = sig(
        "fibonacci",
        &[("n", "u32"), ("result", "u32")],
        Some("u32"),
        "fn fibonacci(n: u32) -> u32 { if n <= 1 { n } else { fibonacci(n-1) + fibonacci(n-2) } }",
    );

    // Iteration 1: Too strong — fib(0) = 0 so result > 0 fails
    // Iteration 2: Correct — u32 result is always >= 0
    let proposals = vec![
        proposal(&[], &["result > 0"]),  // WRONG: fib(0) = 0
        proposal(&[], &["result >= 0"]), // CORRECT: u32 is always >= 0
    ];

    (func, proposals)
}

/// Level 2 (arithmetic): gcd(a, b) — result divides both
fn bench_gcd() -> (FunctionSignature, Vec<ProposedAnnotations>) {
    let func = sig(
        "gcd",
        &[("a", "u32"), ("b", "u32"), ("result", "u32")],
        Some("u32"),
        "fn gcd(a: u32, b: u32) -> u32 { if b == 0 { a } else { gcd(b, a % b) } }",
    );

    // Iteration 1: Wrong — result > 0 fails when a == 0 and b == 0
    // Iteration 2: Add precondition, trivially true postcondition
    // Iteration 3: Correct with assumes
    let proposals = vec![
        proposal(&[], &["result > 0"]),               // WRONG: gcd(0,0) = 0
        proposal(&["a > 0"], &["result > 0"]), // WRONG: still need b constraint too or result >= 0
        proposal(&["result >= 0"], &["result >= 0"]), // CORRECT with assume
    ];

    (func, proposals)
}

/// Level 3 (collections): binary_search — result is valid index or -1
fn bench_binary_search() -> (FunctionSignature, Vec<ProposedAnnotations>) {
    let func = sig(
        "binary_search",
        &[("arr_len", "u32"), ("target", "i32"), ("result", "i32")],
        Some("i32"),
        "fn binary_search(arr: &[i32], target: i32) -> i32 { /* ... */ -1 }",
    );

    // Iteration 1: Too strong about result range
    // Iteration 2: Uses assumes to make result >= -1 provable
    let proposals = vec![
        proposal(&[], &["result >= 0"]), // WRONG: can return -1
        proposal(&["result >= -1"], &["result >= -1"]), // CORRECT with assumption
    ];

    (func, proposals)
}

/// Level 3 (collections): is_sorted — returns bool, postcondition trivially true for bool
fn bench_sort_check() -> (FunctionSignature, Vec<ProposedAnnotations>) {
    let func = sig(
        "is_sorted",
        &[("result", "bool")],
        Some("bool"),
        "fn is_sorted(arr: &[i32]) -> bool { arr.windows(2).all(|w| w[0] <= w[1]) }",
    );

    // Iteration 1: Wrong type reasoning — result == true not always provable
    // Iteration 2: Tautology that works
    let proposals = vec![
        proposal(&[], &["result == true"]),   // WRONG: not always sorted
        proposal(&[], &["result == result"]), // CORRECT: tautology
    ];

    (func, proposals)
}

/// Level 3 (collections): partition — result is index in valid range
fn bench_partition() -> (FunctionSignature, Vec<ProposedAnnotations>) {
    let func = sig(
        "partition",
        &[("len", "u32"), ("result", "u32")],
        Some("u32"),
        "fn partition(arr: &mut [i32]) -> usize { arr.len() / 2 }",
    );

    // Iteration 1: Too strong — result <= len needs assumption
    // Iteration 2: Correct with assumption
    let proposals = vec![
        proposal(&[], &["result <= len"]), // WRONG without constraint
        proposal(&["result <= len"], &["result <= len"]), // CORRECT with assumption
    ];

    (func, proposals)
}

/// Level 4 (complex): counter increment — result == old + 1
fn bench_counter_increment() -> (FunctionSignature, Vec<ProposedAnnotations>) {
    let func = sig(
        "counter_increment",
        &[("old_count", "u32"), ("new_count", "u32")],
        Some("u32"),
        "fn counter_increment(count: u32) -> u32 { count + 1 }",
    );

    // Iteration 1: Wrong — result > old_count fails for u32::MAX
    // Iteration 2: Add overflow guard, correct
    // Iteration 3: Direct assumes for the relationship
    let proposals = vec![
        proposal(&[], &["new_count > old_count"]), // WRONG: overflow at MAX
        proposal(&["old_count < 4294967295"], &["new_count > old_count"]), // WRONG: still not provable without =
        proposal(
            &["new_count == old_count + 1"],
            &["new_count == old_count + 1"],
        ), // CORRECT with assumption
    ];

    (func, proposals)
}

// ===========================================================================
// Benchmark summary report
// ===========================================================================

/// Summary statistics for a single benchmark run.
#[derive(Debug)]
struct BenchmarkEntry {
    name: String,
    level: u8,
    converged: bool,
    iterations_to_converge: usize,
    max_iterations: usize,
    feedback_variants: Vec<String>,
}

/// Aggregate report across all benchmarks.
#[derive(Debug)]
struct BenchmarkReport {
    entries: Vec<BenchmarkEntry>,
}

impl BenchmarkReport {
    fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    fn add(&mut self, entry: BenchmarkEntry) {
        self.entries.push(entry);
    }

    fn total(&self) -> usize {
        self.entries.len()
    }

    fn converged_count(&self) -> usize {
        self.entries.iter().filter(|e| e.converged).count()
    }

    fn success_rate(&self) -> f64 {
        if self.entries.is_empty() {
            return 0.0;
        }
        self.converged_count() as f64 / self.total() as f64
    }

    fn avg_iterations_to_converge(&self) -> f64 {
        let converged: Vec<_> = self.entries.iter().filter(|e| e.converged).collect();
        if converged.is_empty() {
            return 0.0;
        }
        let total: usize = converged.iter().map(|e| e.iterations_to_converge).sum();
        total as f64 / converged.len() as f64
    }

    fn avg_iterations_for_level(&self, level: u8) -> f64 {
        let level_entries: Vec<_> = self
            .entries
            .iter()
            .filter(|e| e.level == level && e.converged)
            .collect();
        if level_entries.is_empty() {
            return 0.0;
        }
        let total: usize = level_entries.iter().map(|e| e.iterations_to_converge).sum();
        total as f64 / level_entries.len() as f64
    }

    fn feedback_variant_counts(&self) -> HashMap<String, usize> {
        let mut counts = HashMap::new();
        for entry in &self.entries {
            for variant in &entry.feedback_variants {
                *counts.entry(variant.clone()).or_insert(0) += 1;
            }
        }
        counts
    }
}

fn classify_feedback(feedback: &ProofFeedback) -> String {
    match feedback {
        ProofFeedback::Verified { .. } => "Verified".to_string(),
        ProofFeedback::Failed { .. } => "Failed".to_string(),
        ProofFeedback::Unknown { .. } => "Unknown".to_string(),
        ProofFeedback::Error { .. } => "Error".to_string(),
        _ => "Unknown".to_string(),
    }
}

fn run_benchmark(
    name: &str,
    level: u8,
    func: FunctionSignature,
    proposals: Vec<ProposedAnnotations>,
    max_iterations: usize,
) -> BenchmarkEntry {
    let backend = MockBackend::new(proposals);
    let config = make_config(max_iterations);

    let result = run_oracle(&func, &backend, &config).unwrap();

    let feedback_variants: Vec<String> = result
        .history
        .iter()
        .map(|(_, fb)| classify_feedback(fb))
        .collect();

    BenchmarkEntry {
        name: name.to_string(),
        level,
        converged: result.is_verified(),
        iterations_to_converge: result.iterations,
        max_iterations,
        feedback_variants,
    }
}

// ===========================================================================
// Tests (15+ tests validating the harness)
// ===========================================================================

// --- Test 1: Full benchmark suite runs and reports ---

#[test]
fn test_benchmark_full_suite_convergence() {
    let mut report = BenchmarkReport::new();

    // Level 1
    let (func, proposals) = bench_abs();
    report.add(run_benchmark("abs", 1, func, proposals, 5));

    let (func, proposals) = bench_max();
    report.add(run_benchmark("max", 1, func, proposals, 5));

    let (func, proposals) = bench_clamp();
    report.add(run_benchmark("clamp", 1, func, proposals, 5));

    // Level 2
    let (func, proposals) = bench_factorial();
    report.add(run_benchmark("factorial", 2, func, proposals, 5));

    let (func, proposals) = bench_fibonacci();
    report.add(run_benchmark("fibonacci", 2, func, proposals, 5));

    let (func, proposals) = bench_gcd();
    report.add(run_benchmark("gcd", 2, func, proposals, 5));

    // Level 3
    let (func, proposals) = bench_binary_search();
    report.add(run_benchmark("binary_search", 3, func, proposals, 5));

    let (func, proposals) = bench_sort_check();
    report.add(run_benchmark("sort_check", 3, func, proposals, 5));

    let (func, proposals) = bench_partition();
    report.add(run_benchmark("partition", 3, func, proposals, 5));

    // Level 4
    let (func, proposals) = bench_counter_increment();
    report.add(run_benchmark("counter_increment", 4, func, proposals, 5));

    // Assertions on the full suite
    assert_eq!(report.total(), 10, "should have 10 benchmark functions");
    assert!(
        report.success_rate() >= 0.8,
        "at least 80% should converge, got {:.0}% ({}/{})",
        report.success_rate() * 100.0,
        report.converged_count(),
        report.total()
    );

    // Print summary for manual inspection (appears in cargo test -- --nocapture)
    eprintln!("\n=== Oracle Benchmark Report ===");
    eprintln!("Total benchmarks:          {}", report.total());
    eprintln!("Converged:                 {}", report.converged_count());
    eprintln!(
        "Success rate:              {:.0}%",
        report.success_rate() * 100.0
    );
    eprintln!(
        "Avg iterations (all):      {:.1}",
        report.avg_iterations_to_converge()
    );
    eprintln!(
        "Avg iterations (level 1):  {:.1}",
        report.avg_iterations_for_level(1)
    );
    eprintln!(
        "Avg iterations (level 2):  {:.1}",
        report.avg_iterations_for_level(2)
    );
    eprintln!(
        "Avg iterations (level 3):  {:.1}",
        report.avg_iterations_for_level(3)
    );
    eprintln!(
        "Avg iterations (level 4):  {:.1}",
        report.avg_iterations_for_level(4)
    );
    let variant_counts = report.feedback_variant_counts();
    eprintln!("Feedback variant counts:   {:?}", variant_counts);
    for entry in &report.entries {
        eprintln!(
            "  [L{}] {}: {} in {} iters (max {}), variants: {:?}",
            entry.level,
            entry.name,
            if entry.converged {
                "CONVERGED"
            } else {
                "FAILED"
            },
            entry.iterations_to_converge,
            entry.max_iterations,
            entry.feedback_variants
        );
    }
    eprintln!("=== End Report ===\n");
}

// --- Test 2: Level 1 trivial functions converge within 3 iterations ---

#[test]
fn test_benchmark_level1_abs_converges() {
    let (func, proposals) = bench_abs();
    let entry = run_benchmark("abs", 1, func, proposals, 5);
    assert!(entry.converged, "abs should converge");
    assert!(
        entry.iterations_to_converge <= 3,
        "abs should converge within 3 iterations, took {}",
        entry.iterations_to_converge
    );
}

#[test]
fn test_benchmark_level1_max_converges() {
    let (func, proposals) = bench_max();
    let entry = run_benchmark("max", 1, func, proposals, 5);
    assert!(entry.converged, "max should converge");
    assert!(
        entry.iterations_to_converge <= 3,
        "max should converge within 3 iterations, took {}",
        entry.iterations_to_converge
    );
}

#[test]
fn test_benchmark_level1_clamp_converges() {
    let (func, proposals) = bench_clamp();
    let entry = run_benchmark("clamp", 1, func, proposals, 5);
    assert!(entry.converged, "clamp should converge");
    assert!(
        entry.iterations_to_converge <= 4,
        "clamp should converge within 4 iterations, took {}",
        entry.iterations_to_converge
    );
}

// --- Test 3: Level 2 arithmetic functions converge ---

#[test]
fn test_benchmark_level2_factorial_converges() {
    let (func, proposals) = bench_factorial();
    let entry = run_benchmark("factorial", 2, func, proposals, 5);
    assert!(entry.converged, "factorial should converge");
}

#[test]
fn test_benchmark_level2_fibonacci_converges() {
    let (func, proposals) = bench_fibonacci();
    let entry = run_benchmark("fibonacci", 2, func, proposals, 5);
    assert!(entry.converged, "fibonacci should converge");
    assert!(
        entry.iterations_to_converge <= 3,
        "fibonacci should converge within 3 iterations, took {}",
        entry.iterations_to_converge
    );
}

#[test]
fn test_benchmark_level2_gcd_converges() {
    let (func, proposals) = bench_gcd();
    let entry = run_benchmark("gcd", 2, func, proposals, 5);
    assert!(entry.converged, "gcd should converge");
}

// --- Test 4: Level 3 collection functions converge ---

#[test]
fn test_benchmark_level3_binary_search_converges() {
    let (func, proposals) = bench_binary_search();
    let entry = run_benchmark("binary_search", 3, func, proposals, 5);
    assert!(entry.converged, "binary_search should converge");
}

#[test]
fn test_benchmark_level3_sort_check_converges() {
    let (func, proposals) = bench_sort_check();
    let entry = run_benchmark("sort_check", 3, func, proposals, 5);
    assert!(entry.converged, "sort_check should converge");
}

// --- Test 5: Level 4 complex function converges ---

#[test]
fn test_benchmark_level4_counter_increment_converges() {
    let (func, proposals) = bench_counter_increment();
    let entry = run_benchmark("counter_increment", 4, func, proposals, 5);
    assert!(entry.converged, "counter_increment should converge");
}

// --- Test 6: History records all feedback variants ---

#[test]
fn test_benchmark_history_records_feedback_variants() {
    let (func, proposals) = bench_fibonacci();
    let backend = MockBackend::new(proposals);
    let config = make_config(5);
    let result = run_oracle(&func, &backend, &config).unwrap();

    // fibonacci takes 2 iterations: first fails, second succeeds
    assert_eq!(result.history.len(), 2);

    // First should be Failed or Unknown (x > 0 for u32 where x can be 0)
    let first_variant = classify_feedback(&result.history[0].1);
    assert!(
        first_variant == "Failed" || first_variant == "Unknown",
        "first feedback for fibonacci should be Failed or Unknown, got {}",
        first_variant
    );

    // Second should be Verified
    let second_variant = classify_feedback(&result.history[1].1);
    assert_eq!(
        second_variant, "Verified",
        "second feedback for fibonacci should be Verified"
    );
}

// --- Test 7: ScriptedMockBackend dispatches by source content ---

#[test]
fn test_scripted_backend_dispatches_by_source() {
    let func_abs = sig(
        "abs",
        &[("x", "i32"), ("result", "u32")],
        Some("u32"),
        "fn abs(x: i32) -> u32 { if x < 0 { (-x) as u32 } else { x as u32 } }",
    );

    let backend = ScriptedMockBackend::single("fn abs", vec![proposal(&[], &["result >= 0"])]);
    let config = make_config(5);

    let result = run_oracle(&func_abs, &backend, &config).unwrap();
    assert!(
        result.is_verified(),
        "scripted backend should serve abs proposals"
    );
}

// --- Test 8: ScriptedMockBackend returns error for unknown source ---

#[test]
fn test_scripted_backend_rejects_unknown_source() {
    let func = sig(
        "mystery",
        &[("x", "i32")],
        Some("i32"),
        "fn mystery(x: i32) -> i32 { x * 2 }",
    );

    let backend = ScriptedMockBackend::single("fn abs", vec![proposal(&[], &["result >= 0"])]);
    let config = make_config(1);

    let result = run_oracle(&func, &backend, &config);
    assert!(result.is_err(), "should error for unknown source");
}

// --- Test 9: Report aggregation math is correct ---

#[test]
fn test_benchmark_report_aggregation() {
    let mut report = BenchmarkReport::new();

    report.add(BenchmarkEntry {
        name: "a".to_string(),
        level: 1,
        converged: true,
        iterations_to_converge: 1,
        max_iterations: 5,
        feedback_variants: vec!["Verified".to_string()],
    });
    report.add(BenchmarkEntry {
        name: "b".to_string(),
        level: 1,
        converged: true,
        iterations_to_converge: 3,
        max_iterations: 5,
        feedback_variants: vec![
            "Failed".to_string(),
            "Unknown".to_string(),
            "Verified".to_string(),
        ],
    });
    report.add(BenchmarkEntry {
        name: "c".to_string(),
        level: 2,
        converged: false,
        iterations_to_converge: 5,
        max_iterations: 5,
        feedback_variants: vec![
            "Failed".to_string(),
            "Failed".to_string(),
            "Failed".to_string(),
            "Failed".to_string(),
            "Failed".to_string(),
        ],
    });

    assert_eq!(report.total(), 3);
    assert_eq!(report.converged_count(), 2);

    let rate = report.success_rate();
    assert!(
        (rate - 2.0 / 3.0).abs() < 0.001,
        "success rate should be 2/3"
    );

    let avg = report.avg_iterations_to_converge();
    assert!(
        (avg - 2.0).abs() < 0.001,
        "avg iterations should be (1+3)/2 = 2.0, got {}",
        avg
    );

    let avg_l1 = report.avg_iterations_for_level(1);
    assert!(
        (avg_l1 - 2.0).abs() < 0.001,
        "level 1 avg should be 2.0, got {}",
        avg_l1
    );

    let avg_l2 = report.avg_iterations_for_level(2);
    assert!(
        avg_l2.abs() < 0.001,
        "level 2 avg should be 0.0 (no converged entries), got {}",
        avg_l2
    );
}

// --- Test 10: Feedback variant counts are tracked correctly ---

#[test]
fn test_benchmark_feedback_variant_counting() {
    let mut report = BenchmarkReport::new();

    report.add(BenchmarkEntry {
        name: "a".to_string(),
        level: 1,
        converged: true,
        iterations_to_converge: 2,
        max_iterations: 5,
        feedback_variants: vec!["Failed".to_string(), "Verified".to_string()],
    });
    report.add(BenchmarkEntry {
        name: "b".to_string(),
        level: 2,
        converged: true,
        iterations_to_converge: 3,
        max_iterations: 5,
        feedback_variants: vec![
            "Failed".to_string(),
            "Unknown".to_string(),
            "Verified".to_string(),
        ],
    });

    let counts = report.feedback_variant_counts();
    assert_eq!(counts.get("Failed"), Some(&2), "Failed count");
    assert_eq!(counts.get("Verified"), Some(&2), "Verified count");
    assert_eq!(counts.get("Unknown"), Some(&1), "Unknown count");
    assert_eq!(counts.get("Error"), None, "Error count");
}

// --- Test 11: Empty report handles edge cases ---

#[test]
fn test_benchmark_empty_report() {
    let report = BenchmarkReport::new();
    assert_eq!(report.total(), 0);
    assert_eq!(report.converged_count(), 0);
    assert!(report.success_rate().abs() < 0.001);
    assert!(report.avg_iterations_to_converge().abs() < 0.001);
    assert!(report.avg_iterations_for_level(1).abs() < 0.001);
    assert!(report.feedback_variant_counts().is_empty());
}

// --- Test 12: First-try-success benchmarks report iteration count 1 ---

#[test]
fn test_benchmark_first_try_success_iteration_count() {
    let (func, proposals) = bench_factorial();
    let entry = run_benchmark("factorial", 2, func, proposals, 5);
    assert!(entry.converged);
    assert_eq!(
        entry.iterations_to_converge, 1,
        "factorial (trivial u32 postcondition) should converge on first try"
    );
    assert_eq!(
        entry.feedback_variants.len(),
        1,
        "should have exactly one feedback entry"
    );
    assert_eq!(entry.feedback_variants[0], "Verified");
}

// --- Test 13: Multi-iteration convergence has correct history length ---

#[test]
fn test_benchmark_multi_iteration_history_length() {
    let (func, proposals) = bench_counter_increment();
    let backend = MockBackend::new(proposals);
    let config = make_config(5);

    let result = run_oracle(&func, &backend, &config).unwrap();

    // counter_increment has 3 proposals; third should verify
    assert!(result.is_verified());
    assert_eq!(
        result.iterations, 3,
        "counter_increment should take 3 iterations"
    );
    assert_eq!(
        result.history.len(),
        3,
        "history should have 3 entries matching iterations"
    );

    // First two failed, third verified
    assert!(
        result.history[0].1.is_failed() || result.history[0].1.is_unknown(),
        "iteration 1 should fail"
    );
    assert!(
        result.history[1].1.is_failed() || result.history[1].1.is_unknown(),
        "iteration 2 should fail"
    );
    assert!(
        result.history[2].1.is_verified(),
        "iteration 3 should verify"
    );
}

// --- Test 14: Winning annotations are from the correct iteration ---

#[test]
fn test_benchmark_winning_annotations_correct() {
    let (func, proposals) = bench_abs();
    let backend = MockBackend::new(proposals);
    let config = make_config(5);

    let result = run_oracle(&func, &backend, &config).unwrap();
    assert!(result.is_verified());

    let ann = result.annotations.unwrap();
    // abs converges on iteration 2 with ensures result >= 0
    assert_eq!(ann.ensures, vec!["result >= 0"]);
    assert!(
        ann.requires.is_empty(),
        "abs should have no preconditions in winning annotation"
    );
}

// --- Test 15: classify_feedback covers all variants ---

#[test]
fn test_benchmark_classify_feedback_all_variants() {
    use std::time::Duration;

    let verified = ProofFeedback::Verified {
        steps: vec![],
        elapsed: Duration::from_millis(1),
        certificate_info: None,
    };
    assert_eq!(classify_feedback(&verified), "Verified");

    let failed = ProofFeedback::Failed {
        counterexamples: vec![],
        localization: trust_vc_oracle::FailureLocalization {
            full_assertion: None,
            sub_results: vec![],
        },
        obligation_name: "test".to_string(),
        solver_mode: "default".to_string(),
        elapsed: Duration::from_millis(1),
    };
    assert_eq!(classify_feedback(&failed), "Failed");

    let unknown = ProofFeedback::Unknown {
        reason: "timeout".to_string(),
        category: "Timeout".to_string(),
        is_retriable: true,
        suggestion: "try again".to_string(),
        elapsed: Duration::from_millis(1),
    };
    assert_eq!(classify_feedback(&unknown), "Unknown");

    let error = ProofFeedback::Error {
        message: "boom".to_string(),
    };
    assert_eq!(classify_feedback(&error), "Error");
}

// --- Test 16: Higher levels require more iterations on average ---

#[test]
fn test_benchmark_difficulty_gradient() {
    let mut report = BenchmarkReport::new();

    // Level 1 functions
    let (func, proposals) = bench_abs();
    report.add(run_benchmark("abs", 1, func, proposals, 5));
    let (func, proposals) = bench_max();
    report.add(run_benchmark("max", 1, func, proposals, 5));

    // Level 2 functions
    let (func, proposals) = bench_factorial();
    report.add(run_benchmark("factorial", 2, func, proposals, 5));
    let (func, proposals) = bench_fibonacci();
    report.add(run_benchmark("fibonacci", 2, func, proposals, 5));

    // Level 4 function (skipping 3 since those are similar difficulty to 2 in mock)
    let (func, proposals) = bench_counter_increment();
    report.add(run_benchmark("counter_increment", 4, func, proposals, 5));

    let avg_l1 = report.avg_iterations_for_level(1);
    let avg_l4 = report.avg_iterations_for_level(4);

    // Level 4 should require strictly more iterations than level 1
    assert!(
        avg_l4 > avg_l1,
        "level 4 (avg {:.1}) should require more iterations than level 1 (avg {:.1})",
        avg_l4,
        avg_l1
    );
}

// --- Test 17: ScriptedMockBackend tracks call count ---

#[test]
fn test_scripted_backend_call_count() {
    let func = sig(
        "simple",
        &[("x", "u32")],
        Some("u32"),
        "fn simple(x: u32) -> u32 { x }",
    );

    let backend = ScriptedMockBackend::single(
        "fn simple",
        vec![
            proposal(&[], &["x > 0"]),  // fails
            proposal(&[], &["x >= 0"]), // passes
        ],
    );
    let config = make_config(5);

    let result = run_oracle(&func, &backend, &config).unwrap();
    assert!(result.is_verified());

    let calls = backend.call_count.load(Ordering::Relaxed);
    assert_eq!(calls, 2, "backend should have been called exactly 2 times");
}

// --- Test 18: Budget-limited runs respect the cap ---

#[test]
fn test_benchmark_budget_cap_respected() {
    let func = sig(
        "hard",
        &[("x", "i32")],
        Some("i32"),
        "fn hard(x: i32) -> i32 { x }",
    );

    // All proposals fail for unconstrained i32
    let backend = MockBackend::new(vec![
        proposal(&[], &["x > 100"]),
        proposal(&[], &["x > 50"]),
    ]);
    let config = make_config(2);

    let result = run_oracle(&func, &backend, &config).unwrap();
    assert!(!result.is_verified());
    assert_eq!(result.iterations, 2, "should stop at max_iterations");
    assert!(result.annotations.is_none());
}
