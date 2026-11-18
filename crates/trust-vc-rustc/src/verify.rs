//! Verification of a read crate: VcIR checks answered by the solver and
//! reported the way Verus reports them.
//!
//! [`verify`] runs trust-vc-vcir's VC generator over the crate the reader
//! produced, answers every check with trust-vc-core's one-goal query API
//! (through `trust_vc_vcir::solve`), and turns the answers into
//! [`Report`]s for the caller to emit:
//!
//! * a proved check reports nothing;
//! * a refuted check is a Verus error with Verus's message, primary span
//!   and labels (see [`Failure`]);
//! * anything else (a refutation of an approximate query or of one missing a
//!   spec definition Verus may have, an unknown answer, a query the API did
//!   not admit, a construct the generator refused) is a refusal, and the
//!   function is not called verified.
//!
//! Verus's per-query error limit is kept: with `--multiple-errors m`
//! (default 2) Verus reports the first failure of a query and looks for at
//! most `m - 1` more, then notes that not all errors may have been
//! reported. A function is one query, plus one per isolated loop body,
//! which Verus runs first (see `QueryGroup`). The checks here are
//! independent, so every failing site is known; per query, the first
//! `max(m, 1)` in program order are reported. Which ones Verus finds first
//! depends on Z3's models; program order is what it finds when the models
//! expose the earliest failure first.
//!
//! After an actual failed function, a separate recommends followup reports
//! optional domain diagnostics as notes. It never changes the original
//! failure/sites or adds a recommends premise to a normal proof. Incomplete
//! auxiliary diagnostics are explicit notes, not a replacement verdict.
//!
//! Precondition clauses of one call form one Verus assertion: the first
//! refuted clause is reported, labelled, and the call's remaining clauses
//! are not checked.
//!
//! ay may write to standard error while it solves; the harness reads every
//! standard-error line as a JSON diagnostic, so file descriptor 2 is pointed
//! elsewhere while the solver runs (see [`StderrRedirect`]).

extern crate rustc_errors;

use std::collections::{HashMap, HashSet};
use std::os::fd::AsRawFd;

use rustc_errors::MultiSpan;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use trust_vc_vcir::solve::{self, Limits, Verdict as SolverVerdict};
use trust_vc_vcir::vcgen::{self, Check, CheckKind, FnVcs, InvariantAt, QueryGroup};
use trust_vc_vcir::{ClauseAttrs, FnDecl, FnId, InvariantKind, Rlimit, SiteId, SpanId};

use crate::reader::CrateRead;
use crate::verdict::{SiteCounts, Verdict};

mod unwind;

/// Verus's default `--rlimit`, in its "roughly seconds" unit.
const DEFAULT_RLIMIT_SECS: f32 = 10.0;
/// Wall-clock bound per query for `rlimit(infinity)`.
const INFINITE_WALL_MS: u64 = 120_000;
/// Smallest wall-clock bound per query.
const MIN_WALL_MS: u64 = 1_000;

/// Environment variable naming a file that receives the solver's standard
/// error output (appended). Without it the output is discarded.
pub const SOLVER_STDERR_ENV: &str = "TRUST_VC_SOLVER_STDERR";

/// Environment variable naming a file that receives every query and its
/// answer as text (appended), for debugging.
pub const DUMP_QUERIES_ENV: &str = "TRUST_VC_DUMP_QUERIES";

/// Command-line options that change verification.
#[derive(Debug, Clone, Copy)]
pub struct VerifyOptions {
    /// `--rlimit`: `None` is Verus's default, `Some(None)` is `infinity`.
    pub rlimit: Option<Option<f32>>,
    /// `--multiple-errors`.
    pub multiple_errors: u32,
    /// Verus's automatic recommends check (off with
    /// `--no-auto-recommends-check`).
    pub auto_recommends: bool,
}

impl Default for VerifyOptions {
    fn default() -> Self {
        Self {
            rlimit: None,
            multiple_errors: 2,
            auto_recommends: true,
        }
    }
}

/// A verification failure, laid out as Verus lays it out.
#[derive(Debug, Clone)]
pub struct Failure {
    /// The message (Verus's, or the user's `custom_err`).
    pub message: String,
    /// Primary spans.
    pub primary: Vec<Span>,
    /// Labels, in Verus's order.
    pub labels: Vec<(Span, String)>,
}

/// Something to emit, in order.
#[derive(Debug, Clone)]
pub enum Report {
    /// A Verus verification error.
    Failure(Failure),
    /// A refuted optional domain check, emitted at note severity.
    Recommendation(Failure),
    /// A refusal: `trust-vc refused: <tag>: <detail>`.
    Refusal {
        span: Span,
        tag: &'static str,
        detail: String,
    },
    /// A note (does not affect the harness).
    Note { span: Span, message: String },
}

/// What happened to one function.
#[derive(Debug, Clone)]
pub struct FnOutcome {
    pub verdict: Verdict,
    pub tag: Option<String>,
    pub sites: Option<SiteCounts>,
}

/// The result of verifying a crate.
#[derive(Debug, Default)]
pub struct Verification {
    /// One entry per function of the VcIR crate.
    pub fns: HashMap<FnId, FnOutcome>,
    /// In emission order.
    pub reports: Vec<Report>,
}

/// Verify every function of `read.krate`.
pub fn verify(read: &CrateRead, opts: VerifyOptions) -> Verification {
    let policy = if read.read_options.no_bv_simplify {
        vcgen::BitvectorPolicy::PreserveOperations
    } else {
        vcgen::BitvectorPolicy::VerusSyntactic
    };
    let session = vcgen::GenerationSession::with_spec_definitions_and_bv_policy(
        &read.krate,
        &read.spec_definitions,
        policy,
    );
    let failed_admission;
    let vcs = match &session {
        Ok(session) => session.vcs(),
        Err(problem) => {
            failed_admission = vcgen::CrateVcs {
                fns: read
                    .krate
                    .fns
                    .iter()
                    .map(|decl| (decl.id, FnVcs::Refused(problem.clone())))
                    .collect(),
            };
            &failed_admission
        }
    };
    let span = |id: SpanId| read.span(id).unwrap_or(rustc_span::DUMMY_SP);
    let mut out = Verification::default();

    let redirect = match StderrRedirect::start() {
        Ok(redirect) => redirect,
        Err(problem) => {
            // Without the redirect the solver could corrupt the harness's
            // input; nothing is verified.
            for (id, _) in &vcs.fns {
                out.fns.insert(
                    *id,
                    FnOutcome {
                        verdict: Verdict::Refused,
                        tag: Some("stderr-redirect".to_string()),
                        sites: None,
                    },
                );
            }
            out.reports.push(Report::Refusal {
                span: rustc_span::DUMMY_SP,
                tag: "stderr-redirect",
                detail: problem,
            });
            return out;
        }
    };

    // Optional diagnostics borrow the same live width contexts and completed
    // normal generation. No compiler/context or generation is repeated.
    for (id, fn_vcs) in &vcs.fns {
        let Some(decl) = read.krate.fn_decl(*id) else {
            continue;
        };
        let outcome = match fn_vcs {
            FnVcs::Spec => FnOutcome {
                verdict: Verdict::Verified,
                tag: None,
                sites: Some(SiteCounts::default()),
            },
            FnVcs::Trusted => FnOutcome {
                verdict: Verdict::Trusted,
                tag: None,
                sites: None,
            },
            // An instance has no record of its own; its generic function has.
            // A `decreases_by` function is checked inside the termination
            // check of the spec function that names it.
            FnVcs::Declared | FnVcs::Instance | FnVcs::Inlined => FnOutcome {
                verdict: Verdict::Declared,
                tag: None,
                sites: None,
            },
            FnVcs::Refused(refusal) => {
                out.reports.push(Report::Refusal {
                    span: span(refusal.span),
                    tag: refusal.tag,
                    detail: refusal.detail.clone(),
                });
                FnOutcome {
                    verdict: Verdict::Refused,
                    tag: Some(refusal.tag.to_string()),
                    sites: None,
                }
            }
            FnVcs::Checks(checks) => {
                let limits = limits(decl, opts);
                check_function(read, decl, checks, &limits, opts, &mut out.reports)
            }
        };
        // A timeout/refusal is not an actual invalid proof query. Preserve
        // the already demonstrated failure before optional diagnostics.
        if outcome.verdict == Verdict::Failed && opts.auto_recommends {
            let checks = session
                .as_ref()
                .map_err(Clone::clone)
                .and_then(|session| session.recommendations(decl.id));
            check_recommendations(
                read,
                decl,
                checks,
                &limits(decl, opts),
                opts,
                &mut out.reports,
            );
        }
        out.fns.insert(*id, outcome);
    }
    drop(redirect);
    out
}

/// The per-query limits of `decl`.
fn limits(decl: &FnDecl, opts: VerifyOptions) -> Limits {
    let secs = match (decl.attrs.rlimit, opts.rlimit) {
        (Some(Rlimit::Infinite), _) | (None, Some(None)) => None,
        // `rlimit(n)` is an integer attribute argument; the cast is exact
        // for every value a test uses and only scales a time bound.
        (Some(Rlimit::Finite(n)), _) => Some(n as f32),
        (None, Some(Some(secs))) => Some(secs),
        (None, None) => Some(DEFAULT_RLIMIT_SECS),
    };
    let wall_ms = match secs {
        None => INFINITE_WALL_MS,
        Some(secs) => {
            let ms = (secs * 1000.0).clamp(MIN_WALL_MS as f32, INFINITE_WALL_MS as f32);
            // In range after the clamp.
            ms as u64
        }
    };
    Limits {
        wall_ms,
        ..Limits::default()
    }
}

/// How one check ended.
enum Answer {
    Proved,
    Refuted { architecture: Option<u32> },
    Refused { tag: &'static str, detail: String },
}

fn answer(check: &Check, label: &str, limits: &Limits) -> Answer {
    let result = solve::check_detailed(&check.query, label, limits);
    answer_result(check, label, result)
}

fn answer_result(check: &Check, label: &str, result: solve::DetailedVerdict) -> Answer {
    let solve::DetailedVerdict {
        verdict,
        refuted_architecture,
    } = result;
    if let Some(path) = std::env::var_os(DUMP_QUERIES_ENV) {
        use std::io::Write;
        // A dump that cannot be written only loses the dump.
        if let Ok(mut file) = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
        {
            let _ = writeln!(
                file,
                ";; {label} {:?} approximate={} order_unknown={}\n{};; => {verdict:?}\n",
                check.kind, check.approximate, check.order_unknown, check.query
            );
        }
    }
    match verdict {
        SolverVerdict::Proved { .. } => Answer::Proved,
        SolverVerdict::Refuted { .. } if check.approximate => Answer::Refused {
            tag: "nonlinear-arith",
            detail: "not proved with nonlinear arithmetic left uninterpreted".to_string(),
        },
        SolverVerdict::Refuted { .. } if check.order_unknown => Answer::Refused {
            tag: "definition-order",
            detail: "not proved without a spec definition that Verus may have emitted before \
                     checking this function"
                .to_string(),
        },
        SolverVerdict::Refuted { .. }
            if matches!(
                &check.kind,
                CheckKind::BitvectorAssert {
                    architecture_specialized: true,
                    ..
                }
            ) && !matches!(refuted_architecture, Some(32 | 64)) =>
        {
            Answer::Refused {
                tag: "query-error",
                detail: "a specialized BV refutation lost its native architecture".into(),
            }
        }
        SolverVerdict::Refuted { .. } => Answer::Refuted {
            architecture: refuted_architecture,
        },
        SolverVerdict::Unknown { reason, category } => Answer::Refused {
            tag: "solver-unknown",
            detail: format!("{category:?}: {reason}"),
        },
        SolverVerdict::Error { message } => Answer::Refused {
            tag: "query-error",
            detail: message,
        },
    }
}

fn check_function(
    read: &CrateRead,
    decl: &FnDecl,
    checks: &[Check],
    limits: &Limits,
    opts: VerifyOptions,
    reports: &mut Vec<Report>,
) -> FnOutcome {
    let span = |id: SpanId| read.span(id).unwrap_or(rustc_span::DUMMY_SP);
    let mut counts = SiteCounts::default();
    let mut failures: Vec<(QueryGroup, Option<u32>, Failure)> = Vec::new();
    let mut refusals = Vec::new();
    // Call sites whose preconditions are decided in a query (a clause
    // failed or was refused); their later clauses are not checked there.
    let mut decided_calls: HashSet<(QueryGroup, SiteId)> = HashSet::new();
    let mut next = 0;
    while next < checks.len() {
        let check = &checks[next];
        let is_pre = matches!(check.kind, CheckKind::Precondition { .. });
        if is_pre && decided_calls.contains(&(check.group, check.site)) {
            next += 1;
            continue;
        }
        let answers = if matches!(&check.kind, CheckKind::BitvectorAssert { .. }) {
            let start = next;
            while next < checks.len()
                && checks[next].group == check.group
                && matches!(&checks[next].kind, CheckKind::BitvectorAssert { .. })
            {
                next += 1
            }
            let labels: Vec<_> = (start..next)
                .map(|index| format!("{}#{}", decl.name, index))
                .collect();
            let clauses: Vec<_> = checks[start..next]
                .iter()
                .zip(&labels)
                .map(|(check, label)| (&check.query, label.as_str()))
                .collect();
            // The live producer ORs actual consumption over the WHOLE
            // assertion before constructing its clauses. Preserve that invariant
            // defensively: mixed metadata could otherwise reorder base errors
            // across the two genuine per-width diagnostic buckets.
            let results = if checks[start..next]
                .iter()
                .any(|other| other.kind != check.kind)
            {
                Err("inconsistent source provenance within an isolated BV assertion group".into())
            } else {
                solve::check_bitvector_group(&clauses, limits)
            };
            match results {
                Ok(results) => results
                    .into_iter()
                    .map(|(offset, result)| {
                        (
                            start + offset,
                            answer_result(&checks[start + offset], &labels[offset], result),
                        )
                    })
                    .collect::<Vec<_>>(),
                Err(detail) => (start..next)
                    .map(|index| {
                        (
                            index,
                            Answer::Refused {
                                tag: "query-error",
                                detail: detail.clone(),
                            },
                        )
                    })
                    .collect(),
            }
        } else {
            let index = next;
            next += 1;
            vec![(
                index,
                answer(check, &format!("{}#{}", decl.name, index), limits),
            )]
        };
        // Case answers remain in native width-major execution order. Count a
        // source clause exactly once after all its cases, while preserving all
        // per-width failures/refusals. Independent clauses use the same single
        // base diagnostic even though complete contexts still both execute.
        let mut source_states: HashMap<usize, (bool, bool)> = HashMap::new();
        let mut base_reported = HashSet::new();
        for (index, result) in answers {
            let state = source_states.entry(index).or_insert((false, false));
            let check = &checks[index];
            let is_pre = matches!(check.kind, CheckKind::Precondition { .. });
            let call = (check.group, check.site);
            match result {
                Answer::Proved => {}
                Answer::Refuted { architecture } => {
                    if is_pre {
                        decided_calls.insert(call);
                    }
                    let specialized = matches!(
                        &check.kind,
                        CheckKind::BitvectorAssert {
                            architecture_specialized: true,
                            ..
                        }
                    );
                    if specialized || !base_reported.contains(&index) {
                        match failure(read, decl, check, architecture) {
                            Ok(failure) => {
                                state.0 = true;
                                if !specialized {
                                    base_reported.insert(index);
                                }
                                failures.push((
                                    check.group,
                                    if specialized { architecture } else { None },
                                    failure,
                                ));
                            }
                            Err(error) => {
                                state.1 = true;
                                refusals.push(Report::Refusal {
                                    span: unwind::source_anchor(read, decl, check),
                                    tag: unwind::SOURCE_TAG,
                                    detail: error.0.into(),
                                });
                            }
                        }
                    } else {
                        state.0 = true;
                    }
                }
                Answer::Refused { tag, detail } => {
                    state.1 = true;
                    if is_pre {
                        decided_calls.insert(call);
                    }
                    refusals.push(Report::Refusal {
                        span: span(check_span(check)),
                        tag,
                        detail,
                    });
                }
            }
        }
        for (_, (failed, refused)) in source_states {
            if failed {
                counts.failed += 1;
            } else if !refused {
                counts.proved += 1;
            }
        }
    }

    // Per query, in the order Verus runs the queries.
    let limit = opts.multiple_errors.max(1) as usize;
    let mut groups: Vec<QueryGroup> = failures.iter().map(|(group, _, _)| *group).collect();
    groups.sort();
    groups.dedup();
    for group in groups {
        // Each specialized architecture is a real upstream query with its own
        // --multiple-errors allowance. Width-independent source assertions keep
        // one base diagnostic bucket despite complete-context execution.
        let mut widths = Vec::new();
        for (g, width, _) in &failures {
            if *g == group && !widths.contains(width) {
                widths.push(*width);
            }
        }
        for width in widths {
            let of_group: Vec<Failure> = failures
                .iter()
                .filter(|(g, w, _)| *g == group && *w == width)
                .map(|(_, _, f)| f.clone())
                .collect();
            let truncated = opts.multiple_errors > 0 && of_group.len() >= limit;
            reports.extend(of_group.into_iter().take(limit).map(Report::Failure));
            if truncated {
                let (what, at) = match group {
                    QueryGroup::Loop { span: at, .. } => ("while loop", at),
                    QueryGroup::Bitvector { span: at, .. } => ("bit-vector assertion", at),
                    QueryGroup::Body => ("function body check", decl.span),
                };
                reports.push(Report::Note {
                    span: span(at),
                    message: format!(
                        "{what}: not all errors may have been reported; rerun with a higher value \
                         for --multiple-errors to find other potential errors in this function"
                    ),
                });
            }
        }
    }

    let refused = !refusals.is_empty();
    let tag = refusals.iter().find_map(|r| match r {
        Report::Refusal { tag, .. } => Some(tag.to_string()),
        _ => None,
    });
    reports.extend(refusals);
    FnOutcome {
        verdict: if refused {
            Verdict::Refused
        } else if counts.failed > 0 {
            Verdict::Failed
        } else {
            Verdict::Verified
        },
        tag,
        sites: Some(counts),
    }
}

fn check_recommendations(
    read: &CrateRead,
    decl: &FnDecl,
    checks: Result<Vec<Check>, vcgen::VcRefusal>,
    limits: &Limits,
    opts: VerifyOptions,
    reports: &mut Vec<Report>,
) {
    let span = |id| read.span(id).unwrap_or(rustc_span::DUMMY_SP);
    let checks = match checks {
        Ok(checks) => checks,
        Err(problem) => {
            reports.push(Report::Note {
                span: span(problem.span),
                message: format!(
                    "trust-vc could not complete recommends diagnostics: {}: {}",
                    problem.tag, problem.detail
                ),
            });
            return;
        }
    };
    let mut reported: HashMap<QueryGroup, usize> = HashMap::new();
    let mut calls = HashSet::new();
    let limit = opts.multiple_errors.max(1) as usize;
    for check in checks {
        let (call, callee) = match &check.kind {
            CheckKind::Recommendation { call, callee, .. } => (*call, Some(*callee)),
            CheckKind::ChoiceRecommendation { span } => (*span, None),
            _ => {
                reports.push(Report::Note { span: span(decl.span),
                    message: "trust-vc could not complete recommends diagnostics: a non-diagnostic obligation".into() });
                return;
            }
        };
        if reported.get(&check.group).copied().unwrap_or(0) >= limit
            || calls.contains(&(call, callee))
        {
            continue;
        }
        match answer(&check, &format!("recommends {}", decl.name), limits) {
            Answer::Proved => {}
            Answer::Refuted { architecture } => match failure(read, decl, &check, architecture) {
                Ok(failure) => {
                    calls.insert((call, callee));
                    *reported.entry(check.group).or_default() += 1;
                    reports.push(Report::Recommendation(failure));
                }
                Err(error) => reports.push(Report::Note {
                    span: unwind::source_anchor(read, decl, &check),
                    message: format!(
                        "trust-vc could not complete recommends diagnostics: {}: {}",
                        unwind::SOURCE_TAG,
                        error.0
                    ),
                }),
            },
            Answer::Refused { tag, detail } => {
                reports.push(Report::Note {
                    span: span(call),
                    message: format!(
                        "trust-vc could not complete recommends diagnostics: {tag}: {detail}"
                    ),
                });
            }
        }
    }
}

/// The span a check is reported at.
fn check_span(check: &Check) -> SpanId {
    match &check.kind {
        CheckKind::Assert { span, .. }
        | CheckKind::BitvectorAssert { span, .. }
        | CheckKind::BitvectorRequires { span }
        | CheckKind::Overflow { span }
        | CheckKind::DivByZero { span }
        | CheckKind::ChoiceRecommendation { span } => *span,
        CheckKind::Precondition { call, .. }
        | CheckKind::Recommendation { call, .. }
        | CheckKind::Unwind { call, .. } => *call,
        CheckKind::Postcondition { exit, .. } => *exit,
        CheckKind::LoopInvariant { at, invariant, .. } => match at {
            InvariantAt::Entry | InvariantAt::End => *invariant,
            InvariantAt::Break(at) | InvariantAt::Continue(at) => *at,
        },
        CheckKind::LoopDecreases { span, .. } => *span,
        CheckKind::Termination { call, .. } => *call,
    }
}

/// The proof note (with Verus's `note: ` prefix) and custom error of a
/// clause.
fn notes(attrs: &ClauseAttrs) -> (Option<String>, Option<String>) {
    (
        attrs
            .proof_notes
            .first()
            .map(|text| format!("note: {text}")),
        attrs.custom_errs.first().cloned(),
    )
}

/// Verus's diagnostic for a refuted check (`vir/src/sst_to_air.rs`,
/// `ast_to_sst.rs`, `sst_to_air_func.rs`; rendered by
/// `rust_verify/src/verifier.rs`, `report_as`).
fn failure(
    read: &CrateRead,
    decl: &FnDecl,
    check: &Check,
    refuted_architecture: Option<u32>,
) -> Result<Failure, unwind::SourceError> {
    let span = |id: SpanId| read.span(id).unwrap_or(rustc_span::DUMMY_SP);
    Ok(match &check.kind {
        CheckKind::Unwind { call, callee } => {
            return unwind::failure(read, decl, *call, *callee);
        }
        CheckKind::Assert { span: at, attrs } => {
            let at = span(*at);
            let (note, custom) = notes(attrs);
            let mut labels = vec![(at, "assertion failed".to_string())];
            if let Some(note) = note {
                labels.push((at, note));
            }
            Failure {
                message: custom.unwrap_or_else(|| "assertion failed".to_string()),
                primary: vec![at],
                labels,
            }
        }
        CheckKind::Precondition {
            call,
            callee,
            clause,
        } => {
            let clause = read
                .krate
                .fn_decl(*callee)
                .and_then(|callee| callee.requires.get(*clause));
            let mut labels = Vec::new();
            let mut custom = None;
            if let Some(clause) = clause {
                let (note, custom_err) = notes(&clause.attrs);
                if custom_err.is_none() {
                    labels.push((span(clause.span), "failed precondition".to_string()));
                }
                if let Some(note) = note {
                    labels.push((span(clause.span), note));
                }
                custom = custom_err;
            }
            Failure {
                message: custom.unwrap_or_else(|| "precondition not satisfied".to_string()),
                primary: vec![span(*call)],
                labels,
            }
        }
        CheckKind::Recommendation { call, callee, clause } => Failure {
            message: "recommendation not met".to_string(),
            primary: vec![span(*call)],
            labels: read.krate.fn_decl(*callee).and_then(|callee| callee.recommends.get(*clause))
                .map(|clause| vec![(span(clause.span), "failed recommendation".to_string())])
                .unwrap_or_default(),
        },
        CheckKind::ChoiceRecommendation { span: at } => Failure {
            message: "recommendation not met: cannot prove that there exists values that satisfy the condition of the choose expression".to_string(),
            primary: vec![span(*at)],
            labels: Vec::new(),
        },
        CheckKind::Postcondition { exit, clause } => {
            let exit_label = if read.explicit_returns.contains(exit) {
                "at this exit"
            } else {
                "at the end of the function body"
            };
            let mut labels = vec![(span(*exit), exit_label.to_string())];
            let mut primary = Vec::new();
            let mut custom = None;
            if let Some(clause) = decl.ensures.get(*clause) {
                let at = span(clause.span);
                primary.push(at);
                labels.push((at, "failed this postcondition".to_string()));
                let (note, custom_err) = notes(&clause.attrs);
                if let Some(note) = note {
                    labels.push((at, note));
                }
                custom = custom_err;
            }
            Failure {
                message: custom.unwrap_or_else(|| "postcondition not satisfied".to_string()),
                primary,
                labels,
            }
        }
        CheckKind::BitvectorAssert {
            span: at,
            architecture_specialized,
        } => Failure {
            message: bitvector_failure_message(*architecture_specialized, refuted_architecture),
            primary: vec![span(*at)],
            labels: Vec::new(),
        },
        CheckKind::BitvectorRequires { span: at } => Failure {
            message: "requires not satisfied".to_string(),
            primary: vec![span(*at)],
            labels: Vec::new(),
        },
        CheckKind::Overflow { span: at } => Failure {
            message: "possible arithmetic underflow/overflow".to_string(),
            primary: vec![span(*at)],
            labels: Vec::new(),
        },
        CheckKind::DivByZero { span: at } => Failure {
            message: "possible division by zero".to_string(),
            primary: vec![span(*at)],
            labels: Vec::new(),
        },
        // `sst_to_air.rs`, `StmX::Loop` and `StmX::BreakOrContinue`.
        CheckKind::LoopInvariant {
            at,
            invariant,
            kind,
        } => {
            let inv = span(*invariant);
            let (message, primary, labels) = match at {
                InvariantAt::Entry => ("invariant not satisfied before loop", inv, Vec::new()),
                InvariantAt::End => (
                    "invariant not satisfied at end of loop body",
                    inv,
                    Vec::new(),
                ),
                InvariantAt::Break(exit) => {
                    let exit = span(*exit);
                    let mut labels = vec![
                        (exit, "at this loop exit".to_string()),
                        (inv, "failed this invariant".to_string()),
                    ];
                    if *kind == InvariantKind::Always {
                        labels.push((inv, BREAK_HINT.to_string()));
                    }
                    ("loop invariant not satisfied", exit, labels)
                }
                InvariantAt::Continue(at) => {
                    let at = span(*at);
                    let labels = vec![
                        (at, "at this continue".to_string()),
                        (inv, "failed this invariant".to_string()),
                    ];
                    ("loop invariant not satisfied", at, labels)
                }
            };
            Failure {
                message: message.to_string(),
                primary: vec![primary],
                labels,
            }
        }
        // `recursion.rs`, `check_termination`: an assertion at the call.
        CheckKind::Termination { call, .. } => Failure {
            message: "could not prove termination".to_string(),
            primary: vec![span(*call)],
            labels: Vec::new(),
        },
        CheckKind::LoopDecreases {
            span: at,
            at_continue,
        } => Failure {
            message: if *at_continue {
                "decreases not satisfied at continue"
            } else {
                "decreases not satisfied at end of loop"
            }
            .to_string(),
            primary: vec![span(*at)],
            labels: Vec::new(),
        },
    })
}

/// Verus's hint on an `invariant` that fails at a `break`.
const BREAK_HINT: &str = "(hint: if this is not supposed to be true at the break, use \
    'invariant_except_break' for it instead of 'invariant', and use 'ensures' for what is true \
    at the break)";

/// Emit a failure as rustc emits Verus's messages.
pub fn emit_failure(tcx: TyCtxt<'_>, failure: &Failure) {
    let mut multispan = MultiSpan::from_spans(failure.primary.clone());
    for (span, label) in &failure.labels {
        multispan.push_span_label(*span, label.clone());
    }
    let mut diag = tcx.dcx().struct_err(failure.message.clone());
    diag.span(multispan);
    diag.emit();
}

/// Emit an optional recommendation diagnostic with its real source labels.
pub fn emit_recommendation(tcx: TyCtxt<'_>, failure: &Failure) {
    let mut diagnostic = tcx
        .dcx()
        .struct_span_note(failure.primary.clone(), failure.message.clone());
    for (span, message) in &failure.labels {
        diagnostic.span_label(*span, message.clone());
    }
    diagnostic.emit();
}

/// Emit a note.
pub fn emit_note(tcx: TyCtxt<'_>, span: Span, message: &str) {
    tcx.dcx().struct_span_note(span, message.to_string()).emit();
}

/// Points file descriptor 2 away from the harness while the solver runs,
/// and back when dropped.
struct StderrRedirect {
    saved: i32,
}

impl StderrRedirect {
    fn start() -> Result<Self, String> {
        let target = match std::env::var_os(SOLVER_STDERR_ENV) {
            Some(path) => std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(&path)
                .map_err(|e| format!("cannot open {}: {e}", path.to_string_lossy()))?,
            None => std::fs::OpenOptions::new()
                .write(true)
                .open("/dev/null")
                .map_err(|e| format!("cannot open /dev/null: {e}"))?,
        };
        // SAFETY: dup and dup2 only duplicate descriptors this process owns;
        // `target` stays open for the duration of the calls.
        let saved = unsafe { libc::dup(2) };
        if saved < 0 {
            return Err("cannot duplicate standard error".to_string());
        }
        // SAFETY: as above.
        if unsafe { libc::dup2(target.as_raw_fd(), 2) } < 0 {
            // SAFETY: `saved` was returned by dup above.
            unsafe { libc::close(saved) };
            return Err("cannot redirect standard error".to_string());
        }
        Ok(Self { saved })
    }
}

impl Drop for StderrRedirect {
    fn drop(&mut self) {
        // SAFETY: `saved` is the descriptor dup returned in `start`.
        unsafe {
            libc::dup2(self.saved, 2);
            libc::close(self.saved);
        }
    }
}

/// Specialization comes from actual source translation; width comes from the
/// real native refutation. Neither source type inventory nor envelope length
/// is evidence for either half of this diagnostic.
fn bitvector_failure_message(specialized: bool, width: Option<u32>) -> String {
    if specialized {
        if let Some(width @ (32 | 64)) = width {
            return format!(
                "bitvector assertion not satisfied (with arch-size set to {width} bits)"
            );
        }
    }
    "bitvector assertion not satisfied".into()
}

#[cfg(test)]
mod bitvector_failure_tests {
    use super::bitvector_failure_message;
    #[test]
    fn specialization_and_actual_failed_width_are_independent() {
        for width in [None, Some(32), Some(64)] {
            assert_eq!(
                bitvector_failure_message(false, width),
                "bitvector assertion not satisfied"
            );
        }
        assert_eq!(
            bitvector_failure_message(true, Some(32)),
            "bitvector assertion not satisfied (with arch-size set to 32 bits)"
        );
        assert_eq!(
            bitvector_failure_message(true, Some(64)),
            "bitvector assertion not satisfied (with arch-size set to 64 bits)"
        );
    }
}
