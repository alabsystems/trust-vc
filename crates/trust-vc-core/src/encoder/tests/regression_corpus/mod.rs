// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
// Locked regression corpus for issue #2738.
//
// The suite intentionally records exact verification outcomes and rounded-up
// timing baselines. Outcome changes always fail. Timing changes fail when a
// case exceeds its per-case budget multiplier (default 2x) of the recorded baseline.

use super::*;
use std::{
    collections::HashSet,
    sync::OnceLock,
    time::{Duration, Instant},
};

macro_rules! corpus_case_tests {
    ($($test_name:ident => $label:literal),+ $(,)?) => {
        $(
            #[test]
            fn $test_name() {
                run_locked_case($label);
            }
        )+
    };
}

mod collections_and_complex;
mod counterexample_and_edge;
mod simple_and_moderate;

const FAST_SAMPLE_RUNS: usize = 3;
const SLOW_CASE_THRESHOLD_MS: u64 = 250;
const MIN_EFFECTIVE_TIMING_BUDGET_MS: u64 = 100;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
enum CaseCategory {
    Simple,
    Moderate,
    CollectionHeavy,
    Complex,
    FalsePostcondition,
    Edge,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LockedOutcome {
    Verified,
    Counterexample,
    /// Model-less incompleteness FAILURE. Kept distinct from both
    /// `Counterexample` and `Unknown` so a locked entry states which of the two
    /// it really is (`docs/design-unknown-as-failure.md`).
    NotProved,
    Unknown,
    Error,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ProgramKind {
    Context,
    Pipeline,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ObligationKind {
    Assume,
    Assert,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TypeSpec {
    Bool,
    I32,
    U32,
    U64,
    Parsed(&'static str),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct VarSpec {
    name: &'static str,
    ty: TypeSpec,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ObligationSpec {
    kind: ObligationKind,
    name: &'static str,
    expr: &'static str,
    solver_mode: Option<crate::vc::SolverMode>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CaseSpec {
    label: &'static str,
    category: CaseCategory,
    description: &'static str,
    program: ProgramKind,
    expected: LockedOutcome,
    baseline_ms: u64,
    /// Budget multiplier applied to `baseline_ms` for the performance gate.
    /// Default is 2. Increase for cases that flake under parallel CPU contention.
    budget_multiplier: u64,
    vars: Vec<VarSpec>,
    obligations: Vec<ObligationSpec>,
    measures: Vec<&'static str>,
}

const fn var(name: &'static str, ty: TypeSpec) -> VarSpec {
    VarSpec { name, ty }
}

const fn assume(name: &'static str, expr: &'static str) -> ObligationSpec {
    ObligationSpec {
        kind: ObligationKind::Assume,
        name,
        expr,
        solver_mode: None,
    }
}

const fn assert(name: &'static str, expr: &'static str) -> ObligationSpec {
    ObligationSpec {
        kind: ObligationKind::Assert,
        name,
        expr,
        solver_mode: None,
    }
}

const fn assert_nonlinear(name: &'static str, expr: &'static str) -> ObligationSpec {
    ObligationSpec {
        kind: ObligationKind::Assert,
        name,
        expr,
        solver_mode: Some(crate::vc::SolverMode::NonlinearArith),
    }
}

#[allow(clippy::too_many_arguments)]
fn context_case(
    label: &'static str,
    category: CaseCategory,
    description: &'static str,
    expected: LockedOutcome,
    baseline_ms: u64,
    vars: Vec<VarSpec>,
    obligations: Vec<ObligationSpec>,
    measures: Vec<&'static str>,
) -> CaseSpec {
    CaseSpec {
        label,
        category,
        description,
        program: ProgramKind::Context,
        expected,
        baseline_ms,
        budget_multiplier: 2,
        vars,
        obligations,
        measures,
    }
}

fn pipeline_case(
    label: &'static str,
    category: CaseCategory,
    description: &'static str,
    expected: LockedOutcome,
    baseline_ms: u64,
    vars: Vec<VarSpec>,
    obligations: Vec<ObligationSpec>,
) -> CaseSpec {
    CaseSpec {
        label,
        category,
        description,
        program: ProgramKind::Pipeline,
        expected,
        baseline_ms,
        budget_multiplier: 2,
        vars,
        obligations,
        measures: Vec::new(),
    }
}

fn all_cases() -> &'static [CaseSpec] {
    static CASES: OnceLock<Vec<CaseSpec>> = OnceLock::new();
    CASES
        .get_or_init(|| {
            let mut cases = Vec::new();
            cases.extend(simple_and_moderate::cases());
            cases.extend(collections_and_complex::cases());
            cases.extend(counterexample_and_edge::cases());
            cases
        })
        .as_slice()
}

fn iter_cases() -> impl Iterator<Item = &'static CaseSpec> {
    all_cases().iter()
}

fn find_case(label: &str) -> &'static CaseSpec {
    iter_cases()
        .find(|case| case.label == label)
        .unwrap_or_else(|| panic!("unknown regression corpus case `{label}`"))
}

fn resolve_type(ty: TypeSpec) -> crate::ir::TrustVcType {
    match ty {
        TypeSpec::Bool => crate::ir::TrustVcType::Bool,
        TypeSpec::I32 => i32_ty(),
        TypeSpec::U32 => u32_ty(),
        TypeSpec::U64 => u64_ty(),
        TypeSpec::Parsed(spec) => crate::ir::TrustVcType::parse_or_opaque(spec),
    }
}

fn build_obligation(spec: ObligationSpec) -> ProofObligation {
    let obligation = match spec.kind {
        ObligationKind::Assume => ProofObligation::assume(spec.name, spec.expr),
        ObligationKind::Assert => ProofObligation::assert(spec.name, spec.expr),
    };
    match spec.solver_mode {
        Some(mode) => obligation.with_solver_mode(mode),
        None => obligation,
    }
}

fn run_once(case: &CaseSpec) -> VerifyResult {
    let _phase_observer = crate::encoder::verification::phase_observer::span("phase", "run_once");
    match case.program {
        ProgramKind::Context => {
            let mut ctx = VerificationContext::new();
            for spec in case.vars.iter().copied() {
                ctx.declare_var_typed(spec.name, resolve_type(spec.ty));
            }
            for spec in case.obligations.iter().copied() {
                ctx.push_obligation(build_obligation(spec));
            }
            for measure in case.measures.iter().copied() {
                ctx.add_measure_nonneg(measure);
            }
            AYEncoder::verify(&ctx)
        }
        ProgramKind::Pipeline => {
            let mut pipeline = crate::verification_bridge::VerificationPipeline::new();
            for spec in case.vars.iter().copied() {
                pipeline
                    .context_mut()
                    .declare_var_typed(spec.name, resolve_type(spec.ty));
            }
            for spec in case.obligations.iter().copied() {
                pipeline.add_obligation(build_obligation(spec));
            }
            for measure in case.measures.iter().copied() {
                pipeline.context_mut().add_measure_nonneg(measure);
            }
            pipeline.verify()
        }
    }
}

fn classify_outcome(result: &VerifyResult) -> LockedOutcome {
    match result {
        VerifyResult::Verified => LockedOutcome::Verified,
        VerifyResult::Counterexample { .. } => LockedOutcome::Counterexample,
        VerifyResult::NotProved { .. } => LockedOutcome::NotProved,
        VerifyResult::Unknown { .. } => LockedOutcome::Unknown,
        VerifyResult::Error { .. } => LockedOutcome::Error,
    }
}

fn measure_case(case: &CaseSpec) -> Duration {
    crate::encoder::verification::timeout::with_timing_solver_admission(|waited, admitted| {
        eprintln!(
            "[regression_corpus] {}: admission waited {:.1}ms, capacity_admitted={}",
            case.label,
            waited.as_secs_f64() * 1000.0,
            admitted,
        );
        let sample_runs = if case.baseline_ms >= SLOW_CASE_THRESHOLD_MS {
            1
        } else {
            FAST_SAMPLE_RUNS
        };
        let mut samples = [Duration::ZERO; FAST_SAMPLE_RUNS];
        let mut phase_reports = if case.label == "C31" {
            Vec::with_capacity(sample_runs)
        } else {
            Vec::new()
        };

        for sample in &mut samples[..sample_runs] {
            let capture = crate::encoder::verification::phase_observer::begin(case.label == "C31");
            let start = Instant::now();
            let result = run_once(case);
            let elapsed = start.elapsed();
            if let Some(report) = capture.finish() {
                phase_reports.push(report);
            }
            let actual = classify_outcome(&result);
            assert_eq!(
                actual, case.expected,
                "{} ({}) changed outcome: expected {:?}, got {:?} ({result:?})",
                case.label, case.description, case.expected, actual
            );
            *sample = elapsed;
        }

        samples[..sample_runs].sort_unstable();
        for (sample, report) in phase_reports.iter().enumerate() {
            report.emit(sample + 1);
        }
        samples[sample_runs / 2]
    })
}

fn run_locked_case(label: &str) {
    let case = find_case(label);
    let elapsed = measure_case(case);
    let elapsed_ms = elapsed.as_secs_f64() * 1000.0;
    let elapsed_us = elapsed.as_micros();
    let multiplier = case.budget_multiplier;
    let configured_threshold_us = u128::from(case.baseline_ms) * u128::from(multiplier) * 1_000;
    let threshold_us =
        configured_threshold_us.max(u128::from(MIN_EFFECTIVE_TIMING_BUDGET_MS) * 1_000);
    let threshold_ms = threshold_us / 1_000;

    eprintln!(
        "[regression_corpus] {}: {:?} in {:.1}ms (baseline {}ms, {}x budget, effective {}ms)",
        case.label, case.expected, elapsed_ms, case.baseline_ms, multiplier, threshold_ms,
    );

    assert!(
        elapsed_us <= threshold_us,
        "{} ({}) exceeded performance budget: {:.1}ms > {}ms ({}x baseline of {}ms, minimum effective budget {}ms)",
        case.label,
        case.description,
        elapsed_ms,
        threshold_ms,
        multiplier,
        case.baseline_ms,
        MIN_EFFECTIVE_TIMING_BUDGET_MS,
    );
}

#[test]
fn corpus_catalog_is_locked_and_complete() {
    let cases: Vec<&CaseSpec> = iter_cases().collect();
    assert!(
        cases.len() >= 50,
        "regression corpus must contain at least 50 locked programs, found {}",
        cases.len()
    );

    let mut labels = HashSet::new();
    let mut saw_simple = false;
    let mut saw_moderate = false;
    let mut saw_collection = false;
    let mut saw_complex = false;
    let mut saw_false_post = false;
    let mut saw_edge = false;

    for case in cases {
        assert!(
            labels.insert(case.label),
            "duplicate regression corpus label detected: {}",
            case.label
        );
        assert!(
            case.baseline_ms > 0,
            "{} must record a non-zero timing baseline",
            case.label
        );
        match case.category {
            CaseCategory::Simple => saw_simple = true,
            CaseCategory::Moderate => saw_moderate = true,
            CaseCategory::CollectionHeavy => saw_collection = true,
            CaseCategory::Complex => saw_complex = true,
            CaseCategory::FalsePostcondition => saw_false_post = true,
            CaseCategory::Edge => saw_edge = true,
        }
    }

    assert!(saw_simple, "corpus must include simple cases");
    assert!(saw_moderate, "corpus must include moderate cases");
    assert!(saw_collection, "corpus must include collection-heavy cases");
    assert!(saw_complex, "corpus must include complex cases");
    assert!(
        saw_false_post,
        "corpus must include false-postcondition/counterexample cases"
    );
    assert!(saw_edge, "corpus must include edge/error cases");
}
