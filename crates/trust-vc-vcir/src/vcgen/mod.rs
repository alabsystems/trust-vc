//! The VC generator: VcIR functions to one solver query per checked site.
//!
//! Copyright 2026 Andrew Yates
//! SPDX-License-Identifier: Apache-2.0
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! [`generate`] takes a crate that [`crate::check_crate`] accepted and
//! produces, for every exec and proof function with a body and every
//! recursive spec function, the list of its [`Check`]s in program order. A
//! check is one [`Query`]: the facts known at the site, and the site's
//! condition as the goal. The sites are
//!
//! * `assert` statements;
//! * each `requires` clause of a callee, at the call (the callee's
//!   `ensures` are assumed after it, except clauses carrying a proof note
//!   or custom error, which Verus never lets a caller assume; its body is
//!   never looked at);
//! * each `ensures` clause, at every exit;
//! * loop invariants on entry to a loop, at the end of its body, at
//!   `continue` and at `break`, and a loop's `decreases` at the end of its
//!   body and at `continue`;
//! * exec arithmetic: overflow of `+ - *` and negation, division by zero;
//! * each recursive call (a call of a member of the caller's
//!   [`crate::RecGroup`]): the callee's measure at the arguments is below
//!   the caller's measure at entry. A recursive spec function's checks are
//!   only these, over its body flattened as Verus flattens it.
//!
//! The semantics follow Verus: preconditions are assumed on entry, an
//! assertion or an exec check is assumed after its site, a parameter in a
//! postcondition means its entry value, integers are mathematical with
//! explicit ranges, `as` is Verus's clip, and spec functions are definitions
//! visible unless opaque (until revealed), hidden, or not yet emitted where
//! Verus checks the function ([`crate::VcCrate::def_order`]). See `body` for
//! how values and paths are tracked and `spec` for the shared vocabulary.
//!
//! Whatever the generator does not handle, it refuses, per function, with a
//! [`VcRefusal`]: nothing is dropped or weakened silently. Two cases are
//! weaker than Verus by design and are marked instead: a query that uses an
//! uninterpreted stand-in for nonlinear arithmetic is
//! [`Check::approximate`], and a refutation of it is not a verdict; the same
//! holds for a query that leaves uninterpreted a spec function whose
//! definition Verus may already have emitted ([`Check::order_unknown`]).
//!
//! The crate stays solver-free. [`Query`] mirrors trust-vc-core's one-goal
//! query API; `crate::solve` (feature `solve`) translates and answers it.

mod aux_work;
mod bitvector;
mod bitwise;
mod body;
mod call_identity;
mod closed_templates;
mod expr;
mod inline_body;
mod inline_work;
mod loops;
mod quant;
mod query;
mod relevance;
mod resolution;
mod spec;
mod static_schedule;
mod substitution;
pub mod term;
mod trigger_pattern;
mod type_encoding;
mod val;
mod witness;

use std::collections::{BTreeSet, HashMap};

pub use query::{
    Check, CheckKind, CrateVcs, Definition, FnVcs, Function, Hypothesis, InvariantAt, Query,
    QueryGroup, Source, Symbol, VcRefusal,
};

use crate::expr::{BinOp, Expr, ExprKind};
use crate::ids::FnId;
use crate::item::{Body, FnDecl, FnRole, Mode, VcCrate};
use crate::stmt::{Block, Stmt, StmtKind};
use crate::ty::IntRange;
use crate::CheckedSpecDefinitions;

/// Generate the checks of every function of `krate`.
///
/// `krate` must be well formed ([`crate::check_crate`] returned nothing).
/// A malformed crate does not make this panic; the affected functions are
/// refused with the tag `vcgen-internal`.
#[must_use]
pub fn generate(krate: &VcCrate) -> CrateVcs {
    generate_with_spec_definitions(krate, &CheckedSpecDefinitions::default())
}

/// Generate checks using separately checked, client-matched Spec definitions.
///
/// The collection supplies no native provenance and does not change imported
/// declarations or count them as verified. Its complete signature join is
/// rechecked at every consumption before any defining equation is translated.
#[must_use]
pub fn generate_with_spec_definitions(
    krate: &VcCrate,
    definitions: &CheckedSpecDefinitions,
) -> CrateVcs {
    generate_with_spec_definitions_and_bv_policy(krate, definitions, BitvectorPolicy::default())
}

/// The preprocessing phase selected by a source invocation. Rich typed IR
/// keeps independent undefined-operation occurrences unless explicitly opted in.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum BitvectorPolicy {
    #[default]
    PreserveOperations,
    /// Verus's typed syntactic preprocessing before finite BV conversion.
    VerusSyntactic,
}

/// Generate checks under an explicit BV preprocessing policy. This changes
/// neither source/WF admission nor the supplied checked definition collection.
#[must_use]
pub fn generate_with_spec_definitions_and_bv_policy(
    krate: &VcCrate,
    definitions: &CheckedSpecDefinitions,
    bitvector_policy: BitvectorPolicy,
) -> CrateVcs {
    match GenerationSession::with_spec_definitions_and_bv_policy(
        krate,
        definitions,
        bitvector_policy,
    ) {
        Ok(session) => session.into_vcs(),
        Err(problem) => refused_crate(krate, problem),
    }
}

fn refused_crate(krate: &VcCrate, problem: VcRefusal) -> CrateVcs {
    CrateVcs {
        fns: krate
            .fns
            .iter()
            .map(|decl| (decl.id, FnVcs::Refused(problem.clone())))
            .collect(),
    }
}

fn admission(krate: &VcCrate, definitions: &CheckedSpecDefinitions) -> Result<Vec<u32>, VcRefusal> {
    if crate::projection_types::Definitions::checked(krate, &mut crate::copy_context::WF_WORK).is_none() {
        return Err(val::refusal("projection-definition", "invalid closed associated implementation semantics", crate::SpanId(0)));
    }
    if let Some(problem) = crate::prophecy::check_crate(krate).first() {
        return Err(val::refusal("prophecy", &problem.message, problem.span));
    }
    if let Err(errors) = definitions.validate_for_crate(krate) {
        let problem = &errors[0];
        return Err(val::refusal(
            "imported-definition",
            &problem.message,
            problem.span,
        ));
    }
    let widths = krate
        .architecture
        .cases()
        .map_err(|detail| val::refusal("architecture", detail, crate::SpanId(0)))?;
    if let Some(span) = krate.fns.iter().find_map(incomplete_source_binder) {
        return Err(val::refusal(
            "source-construction",
            "a binder without successfully inferred triggers",
            span,
        ));
    }
    Ok(widths.to_vec())
}

/// A live generation of exactly one immutable source crate. Normal results,
/// width contexts, tables and completed Static admission stay together through
/// optional diagnostics; none is reconstructed from a result report.
pub struct GenerationSession<'a> {
    krate: &'a VcCrate,
    widths: Vec<(
        val::Ctx<'a>,
        spec::Tables,
        Option<static_schedule::Plan<'a>>,
    )>,
    normal: CrateVcs,
}

impl<'a> GenerationSession<'a> {
    /// Generate each declaration once per width using the ordinary policy.
    pub fn new(krate: &'a VcCrate) -> Result<Self, VcRefusal> {
        Self::with_spec_definitions(krate, &CheckedSpecDefinitions::default())
    }

    /// Retain the separately checked definition join in this same live context.
    pub fn with_spec_definitions(
        krate: &'a VcCrate,
        definitions: &CheckedSpecDefinitions,
    ) -> Result<Self, VcRefusal> {
        Self::with_spec_definitions_and_bv_policy(krate, definitions, BitvectorPolicy::default())
    }

    /// Individual backend refusals remain normal per-function results. Only
    /// the preexisting global source/definition/architecture gates return Err.
    pub fn with_spec_definitions_and_bv_policy(
        krate: &'a VcCrate,
        definitions: &CheckedSpecDefinitions,
        policy: BitvectorPolicy,
    ) -> Result<Self, VcRefusal> {
        let cases = admission(krate, definitions)?;
        let mut widths = Vec::new();
        let mut generated = Vec::new();
        for width in cases {
            let mut ctx = val::Ctx::for_width_with_checked_spec(krate, width, definitions);
            ctx.bitvector_policy = policy;
            let tables = spec::Tables::build_with_spec_definitions(&ctx, krate, definitions);
            let (normal, plan) = generate_width(&ctx, &tables, krate);
            generated.push(normal);
            widths.push((ctx, tables, plan));
        }
        let mut generated = generated.into_iter();
        let first = generated.next().expect("admitted architecture has a width");
        let normal = match generated.next() {
            None => first,
            Some(second) => merge_widths(first, second),
        };
        Ok(Self {
            krate,
            widths,
            normal,
        })
    }

    /// The actual normal results, in original declaration/check order.
    pub fn vcs(&self) -> &CrateVcs {
        &self.normal
    }

    /// Consume the session without generating anything again.
    pub fn into_vcs(self) -> CrateVcs {
        self.normal
    }

    /// Optional body diagnostics in the actual retained width contexts. A
    /// diagnostic never changes the original normal results or proof verdict.
    pub fn recommendations(&self, function: FnId) -> Result<Vec<Check>, VcRefusal> {
        let decl = self.krate.fn_decl(function).ok_or_else(|| {
            val::refusal(
                "vcgen-internal",
                "unknown recommendation owner",
                crate::SpanId(0),
            )
        })?;
        if matches!(decl.role, FnRole::Imported | FnRole::Instance) || decl.attrs.external_body {
            return Err(val::refusal(
                "recommends-owner",
                "no checked source body",
                decl.span,
            ));
        }
        let generate =
            |ctx: &val::Ctx<'_>,
             tables: &spec::Tables,
             plan: Option<&static_schedule::Plan<'_>>| match &decl.body {
                Body::Stmts(block) => {
                    refused_anywhere(ctx, block)?;
                    body::Gen::new(ctx, tables, decl)
                        .with_static_plan(plan)
                        .for_recommendations()
                        .run()
                }
                Body::Constant(_) => body::Gen::new(ctx, tables, decl)
                    .with_static_plan(plan)
                    .for_recommendations()
                    .run_constant(),
                Body::Spec(_) => body::Gen::new(ctx, tables, decl)
                    .with_static_plan(plan)
                    .for_recommendations()
                    .run_spec_recommendations(),
                _ => Err(val::refusal(
                    "recommends-owner",
                    "no checked diagnostic body",
                    decl.span,
                )),
            };
        let (ctx, tables, plan) = &self.widths[0];
        let first = generate(ctx, tables, plan.as_ref())?;
        if self.widths.len() == 1 {
            return Ok(first);
        }
        let (ctx, tables, plan) = &self.widths[1];
        merge_architectures(first, generate(ctx, tables, plan.as_ref())?)
    }
}

fn merge_widths(first: CrateVcs, second: CrateVcs) -> CrateVcs {
    let fns = first
        .fns
        .into_iter()
        .zip(second.fns)
        .map(|((id, left), (other, right))| {
            let value = if id != other {
                FnVcs::Refused(val::refusal(
                    "architecture",
                    "architecture function identities differ",
                    crate::SpanId(0),
                ))
            } else {
                match (left, right) {
                    (FnVcs::Refused(problem), _) | (_, FnVcs::Refused(problem)) => {
                        FnVcs::Refused(problem)
                    }
                    (FnVcs::Checks(left), FnVcs::Checks(right)) => merge_architectures(left, right)
                        .map(FnVcs::Checks)
                        .unwrap_or_else(FnVcs::Refused),
                    (left, right) if left == right => left,
                    _ => FnVcs::Refused(val::refusal(
                        "architecture",
                        "different declaration status across architectures",
                        crate::SpanId(0),
                    )),
                }
            };
            (id, value)
        })
        .collect();
    CrateVcs { fns }
}

/// Find an intrinsic diagnostic node in every source position, without
/// consulting spans as permissions or relying on executable reachability.
fn incomplete_source_binder(decl: &FnDecl) -> Option<crate::SpanId> {
    fn in_expr(expr: &Expr) -> Option<crate::SpanId> {
        match &expr.kind {
            ExprKind::UntriggeredQuant { .. } | ExprKind::UntriggeredChoose { .. } => {
                return Some(expr.span)
            }
            ExprKind::ProofInSpec(block) => return in_block(block),
            ExprKind::ProofInSpecTail { block, tail } => {
                return in_block(block).or_else(|| in_expr(tail))
            }
            _ => {}
        }
        let mut found = None;
        expr.for_each_child(&mut |child| {
            if found.is_none() {
                found = in_expr(child);
            }
        });
        found
    }
    fn in_block(block: &Block) -> Option<crate::SpanId> {
        let mut found = None;
        visit_stmts(block, &mut |stmt| {
            if found.is_none() {
                found = stmt_exprs(stmt).into_iter().find_map(in_expr);
            }
        });
        found
    }
    decl.requires
        .iter()
        .chain(&decl.ensures)
        .chain(&decl.recommends)
        .map(|clause| &clause.expr)
        .chain(&decl.decreases)
        .chain(&decl.decreases_when)
        .chain(decl.unwind_spec().condition())
        .find_map(in_expr)
        .or_else(|| match &decl.body {
            Body::None => None,
            Body::Spec(expr) | Body::Constant(expr) => in_expr(expr),
            Body::Stmts(block) => in_block(block),
        })
}

/// Two complete contexts keep source nominal/type-argument identity unchanged;
/// only their mathematical bounds, clips and native BV widths differ.
fn generate_width<'a>(
    ctx: &val::Ctx<'a>,
    tables: &spec::Tables,
    krate: &'a VcCrate,
) -> (CrateVcs, Option<static_schedule::Plan<'a>>) {
    static_schedule::generate(ctx, tables, krate)
}

fn generate_declaration(
    ctx: &val::Ctx<'_>,
    tables: &spec::Tables,
    decl: &FnDecl,
    uncovered: &HashMap<FnId, VcRefusal>,
    plan: Option<&static_schedule::Plan<'_>>,
) -> FnVcs {
    if let Some(problem) = plan.and_then(static_schedule::Plan::problem) {
        return FnVcs::Refused(val::refusal("static-schedule", problem, decl.span));
    }
    match decl.mode {
        _ if decl.role == FnRole::Imported => {
            let problem = decl
                .imported_problem()
                .map(|detail| val::refusal("imported-declaration", detail, decl.span))
                .or_else(|| {
                    ctx.group(decl.id).map(|_| {
                        val::refusal(
                            "imported-declaration",
                            "an imported recursive declaration",
                            decl.span,
                        )
                    })
                })
                .or_else(|| {
                    tables
                        .sigs
                        .get(&decl.id)
                        .and_then(|sig| sig.problem.clone())
                });
            problem.map_or(FnVcs::Declared, FnVcs::Refused)
        }
        _ if decl.role == FnRole::Instance => FnVcs::Instance,
        _ if decl.role == FnRole::TraitDecl && decl.body == Body::None => FnVcs::Declared,
        _ if uncovered.contains_key(&decl.id) => FnVcs::Refused(uncovered[&decl.id].clone()),
        _ if matches!(decl.body, Body::Constant(_)) => {
            match body::Gen::new(ctx, tables, decl)
                .with_static_plan(plan)
                .run_constant()
            {
                Ok(checks) => FnVcs::Checks(checks),
                Err(problem) => FnVcs::Refused(problem),
            }
        }
        Mode::Spec => match tables
            .sigs
            .get(&decl.id)
            .and_then(|sig| sig.problem.clone())
        {
            Some(problem) => FnVcs::Refused(problem),
            None if ctx.group(decl.id).is_some() && matches!(decl.body, Body::Spec(_)) => {
                spec_termination(ctx, tables, decl, plan)
            }
            None => FnVcs::Spec,
        },
        Mode::Exec | Mode::Proof if decl.attrs.external_body => FnVcs::Trusted,
        Mode::Proof if decl.attrs.is_decreases_by => FnVcs::Inlined,
        Mode::Exec | Mode::Proof => match &decl.body {
            Body::Stmts(block) => {
                match refused_anywhere(&ctx, block).and_then(|()| {
                    body::Gen::new(ctx, tables, decl)
                        .with_static_plan(plan)
                        .run()
                }) {
                    Ok(checks) => FnVcs::Checks(checks),
                    Err(problem) => FnVcs::Refused(problem),
                }
            }
            _ => FnVcs::Refused(val::refusal(
                "no-body",
                format!("`{}` has no body to check", decl.name),
                decl.span,
            )),
        },
    }
}

/// Stable source event identity, without hashing user diagnostic strings or
/// solver terms. Occurrence distinguishes same-site multi-clause obligations.
fn architecture_event(check: &Check) -> (crate::SiteId, u8, usize) {
    let (kind, clause) = match &check.kind {
        CheckKind::Assert { .. } => (0, 0),
        CheckKind::BitvectorRequires { .. } => (1, 0),
        CheckKind::Precondition { clause, .. } => (2, *clause),
        CheckKind::Postcondition { clause, .. } => (3, *clause),
        CheckKind::Overflow { .. } => (4, 0),
        CheckKind::DivByZero { .. } => (5, 0),
        CheckKind::LoopInvariant { .. } => (6, 0),
        CheckKind::Termination { .. } => (7, 0),
        CheckKind::LoopDecreases { .. } => (8, 0),
        CheckKind::BitvectorAssert { .. } => (9, 0),
        CheckKind::Recommendation { clause, .. } => (10, *clause),
        CheckKind::ChoiceRecommendation { .. } => (11, 0),
        CheckKind::Unwind { .. } => (12, 0),
    };
    (check.site, kind, clause)
}

fn empty_architecture_case() -> Query {
    Query {
        architectures: None,
        bitvector: None,
        nominal_types: Vec::new(),
        symbols: Vec::new(),
        functions: Vec::new(),
        definitions: Vec::new(),
        hypotheses: Vec::new(),
        goal: term::Term::Bool(true),
    }
}

fn merge_architectures(left: Vec<Check>, right: Vec<Check>) -> Result<Vec<Check>, VcRefusal> {
    let mut work = 200_000usize;
    let mut output: Vec<Check> = Vec::new();
    let mut indices: HashMap<_, usize> = HashMap::new();
    for (case, checks) in [left, right].into_iter().enumerate() {
        let mut occurrences = HashMap::new();
        for mut check in checks {
            let mut cost = 1usize;
            if let CheckKind::Assert { attrs, .. } = &check.kind {
                for text in attrs.proof_notes.iter().chain(&attrs.custom_errs) {
                    cost = cost.checked_add(text.len()).ok_or_else(|| {
                        val::refusal(
                            "architecture-budget",
                            "architecture event size overflow",
                            crate::SpanId(0),
                        )
                    })?;
                }
            }
            work = work.checked_sub(cost).ok_or_else(|| {
                val::refusal(
                    "architecture-budget",
                    "architecture event comparison exhausted",
                    crate::SpanId(0),
                )
            })?;
            let event = architecture_event(&check);
            let occurrence = occurrences.entry(event).or_insert(0usize);
            let key = (event, *occurrence);
            *occurrence += 1;
            if let Some(&index) = indices.get(&key) {
                let prior = &mut output[index];
                if prior.kind != check.kind || prior.group != check.group {
                    return Err(val::refusal(
                        "architecture",
                        "a source event changes kind or query group across architectures",
                        crate::SpanId(0),
                    ));
                }
                let Some(cases) = &mut prior.query.architectures else {
                    return Err(val::refusal(
                        "architecture",
                        "a missing complete architecture batch",
                        crate::SpanId(0),
                    ));
                };
                cases[case].1 = check.query;
                prior.approximate |= check.approximate;
                prior.order_unknown |= check.order_unknown;
            } else {
                let mut cases = vec![
                    (32, empty_architecture_case()),
                    (64, empty_architecture_case()),
                ];
                cases[case].1 = check.query;
                check.query = Query {
                    architectures: Some(cases),
                    bitvector: None,
                    nominal_types: Vec::new(),
                    symbols: Vec::new(),
                    functions: Vec::new(),
                    definitions: Vec::new(),
                    hypotheses: Vec::new(),
                    goal: term::Term::Bool(false),
                };
                indices.insert(key, output.len());
                output.push(check);
            }
        }
    }
    for check in &output {
        if let CheckKind::BitvectorAssert { span, .. } = &check.kind {
            let complete = check.query.architectures.as_ref().is_some_and(|cases| {
                cases.len() == 2
                    && cases.iter().all(|(width, query)| {
                        query.bitvector.as_ref().is_some_and(|questions| {
                            questions.len() == 1 && questions[0].architecture == *width
                        })
                    })
            });
            if !complete {
                return Err(val::refusal("architecture",
                    "an isolated BV source event is missing an actual required architecture question", *span));
            }
        }
    }
    Ok(output)
}

/// The termination check of a recursive spec function.
fn spec_termination(
    ctx: &val::Ctx<'_>,
    tables: &spec::Tables,
    decl: &FnDecl,
    plan: Option<&static_schedule::Plan<'_>>,
) -> FnVcs {
    let walked = match decl.decreases_by {
        Some(via) => match ctx.fns.get(&via) {
            Some(via) => *via,
            None => {
                return FnVcs::Refused(val::refusal(
                    "vcgen-internal",
                    "an unknown decreases_by function",
                    decl.span,
                ))
            }
        },
        None => decl,
    };
    match body::Gen::new(ctx, tables, walked)
        .with_static_plan(plan)
        .run_termination(decl)
    {
        Ok(checks) => FnVcs::Checks(checks),
        Err(problem) => FnVcs::Refused(problem),
    }
}

/// The functions on a cycle of calls that no group of recursive functions
/// covers (the cycle leaves its group, or there is no group), each with its
/// refusal. Every call counts: in clauses, measures and bodies, unreachable
/// ones included, and a spec function's `decreases_by` function.
fn uncovered_cycles(ctx: &val::Ctx<'_>, krate: &VcCrate) -> HashMap<FnId, VcRefusal> {
    let graph: HashMap<FnId, BTreeSet<FnId>> = krate
        .fns
        .iter()
        .map(|decl| (decl.id, all_callees(decl)))
        .collect();
    uncovered_cycles_components(ctx, &graph, &strongly_connected(&graph))
}

fn uncovered_cycles_components(
    ctx: &val::Ctx<'_>,
    graph: &HashMap<FnId, BTreeSet<FnId>>,
    components: &[Vec<FnId>],
) -> HashMap<FnId, VcRefusal> {
    let mut out = HashMap::new();
    for component in components {
        let cyclic = component.len() > 1
            || graph
                .get(&component[0])
                .is_some_and(|next| next.contains(&component[0]));
        if !cyclic {
            continue;
        }
        if component.iter().any(|id| {
            ctx.fns
                .get(id)
                .is_some_and(|decl| decl.attrs.broadcast_triggers.is_some())
        }) {
            for id in component {
                let span = ctx
                    .fns
                    .get(id)
                    .map_or(crate::ids::SpanId(0), |decl| decl.span);
                out.insert(
                    *id,
                    val::refusal(
                        "broadcast-recursion",
                        "a cycle through a broadcast proof contract",
                        span,
                    ),
                );
            }
            continue;
        }
        let first = component[0];
        let covered = ctx
            .group(first)
            .is_some_and(|group| component.iter().all(|id| group.contains(*id)));
        if covered {
            continue;
        }
        let names: Vec<String> = component
            .iter()
            .map(|id| format!("`{}`", ctx.fns.get(id).map_or("?", |f| f.name.as_str())))
            .collect();
        for id in component {
            let span = ctx.fns.get(id).map_or(crate::ids::SpanId(0), |f| f.span);
            out.insert(
                *id,
                val::refusal(
                    "recursion",
                    format!(
                        "a cycle of calls outside a group of recursive functions: {}",
                        names.join(", ")
                    ),
                    span,
                ),
            );
        }
    }
    out
}

/// Every function `decl` calls: in its clauses, measure and body,
/// unreachable code included, and its `decreases_by` function.
fn all_callees(decl: &FnDecl) -> BTreeSet<FnId> {
    let mut out = BTreeSet::new();
    let mut add = |e: &Expr| collect_calls(e, &mut out);
    for hint in decl.broadcast_hints() {
        add(hint);
    }
    for clause in decl
        .requires
        .iter()
        .chain(&decl.ensures)
        .chain(&decl.recommends)
    {
        add(&clause.expr);
    }
    for measure in &decl.decreases {
        add(measure);
    }
    if let Some(when) = &decl.decreases_when {
        add(when);
    }
    if let Some(condition) = decl.unwind_spec().condition() {
        add(condition);
    }
    match &decl.body {
        Body::None => {}
        Body::Spec(expr) | Body::Constant(expr) => add(expr),
        Body::Stmts(block) => visit_stmts(block, &mut |stmt| {
            if let StmtKind::Call { callee, .. } | StmtKind::BroadcastUse { callee } = &stmt.kind {
                out.insert(*callee);
            }
            for e in stmt_exprs(stmt) {
                collect_calls(e, &mut out);
            }
        }),
    }
    out.extend(decl.decreases_by);
    out
}

/// Add the callee of every call in `e` to `out`.
fn collect_calls(e: &Expr, out: &mut BTreeSet<FnId>) {
    match &e.kind {
        ExprKind::Call { callee, .. } => {
            out.insert(*callee);
        }
        ExprKind::ProofInSpec(block) | ExprKind::ProofInSpecTail { block, .. } => {
            visit_stmts(block, &mut |stmt| {
                if let StmtKind::Call { callee, .. } | StmtKind::BroadcastUse { callee } =
                    &stmt.kind
                {
                    out.insert(*callee);
                }
                for e in stmt_exprs(stmt) {
                    collect_calls(e, out);
                }
            })
        }
        _ => {}
    }
    e.for_each_child(&mut |child| collect_calls(child, out));
}

/// The strongly connected components of `graph` (Tarjan), each listed
/// once; nodes without entries have no edges.
pub(crate) fn strongly_connected(graph: &HashMap<FnId, BTreeSet<FnId>>) -> Vec<Vec<FnId>> {
    struct State<'g> {
        graph: &'g HashMap<FnId, BTreeSet<FnId>>,
        index: HashMap<FnId, usize>,
        low: HashMap<FnId, usize>,
        stack: Vec<FnId>,
        on_stack: BTreeSet<FnId>,
        out: Vec<Vec<FnId>>,
    }
    // Iterative, so a long chain of calls cannot exhaust the stack.
    fn visit(state: &mut State<'_>, root: FnId) {
        let mut work: Vec<(FnId, Vec<FnId>)> = Vec::new();
        let enter = |state: &mut State<'_>, node: FnId| -> (FnId, Vec<FnId>) {
            let n = state.index.len();
            state.index.insert(node, n);
            state.low.insert(node, n);
            state.stack.push(node);
            state.on_stack.insert(node);
            let succ: Vec<FnId> = state
                .graph
                .get(&node)
                .into_iter()
                .flatten()
                .rev()
                .copied()
                .collect();
            (node, succ)
        };
        let first = enter(state, root);
        work.push(first);
        while let Some((node, mut succ)) = work.pop() {
            if let Some(next) = succ.pop() {
                work.push((node, succ));
                if !state.index.contains_key(&next) {
                    let frame = enter(state, next);
                    work.push(frame);
                } else if state.on_stack.contains(&next) {
                    let low = state.low[&node].min(state.index[&next]);
                    state.low.insert(node, low);
                }
                continue;
            }
            if let Some((parent, _)) = work.last() {
                let low = state.low[parent].min(state.low[&node]);
                state.low.insert(*parent, low);
            }
            if state.low[&node] == state.index[&node] {
                let mut component = Vec::new();
                while let Some(top) = state.stack.pop() {
                    state.on_stack.remove(&top);
                    component.push(top);
                    if top == node {
                        break;
                    }
                }
                component.sort();
                state.out.push(component);
            }
        }
    }
    let mut state = State {
        graph,
        index: HashMap::new(),
        low: HashMap::new(),
        stack: Vec::new(),
        on_stack: BTreeSet::new(),
        out: Vec::new(),
    };
    let mut nodes: Vec<FnId> = graph.keys().copied().collect();
    nodes.sort();
    for node in nodes {
        if !state.index.contains_key(&node) {
            visit(&mut state, node);
        }
    }
    state.out
}

/// Does `block` call a function anywhere, unreachable statements included?
#[must_use]
pub fn calls_anything(block: &Block) -> bool {
    let mut found = false;
    visit_stmts(block, &mut |stmt| {
        found |= matches!(stmt.kind, StmtKind::Call { .. });
        if let StmtKind::GhostTail { tail, .. } = &stmt.kind {
            let mut callees = BTreeSet::new();
            collect_calls(tail, &mut callees);
            found |= !callees.is_empty();
        }
    });
    found
}

/// Call `f` on every statement of `block`, nested ones and unreachable
/// ones included, in program order.
fn visit_stmts<'b>(block: &'b Block, f: &mut dyn FnMut(&'b Stmt)) {
    for stmt in &block.stmts {
        if let StmtKind::GhostTail { block, .. } = &stmt.kind {
            // This statement's own expression is its final value, so its
            // prefix precedes the callback in actual evaluation order.
            visit_stmts(block, f);
            f(stmt);
            continue;
        }
        f(stmt);
        match &stmt.kind {
            StmtKind::If {
                then_block,
                else_block,
                ..
            }
            | StmtKind::IfSpec {
                then_block,
                else_block,
                ..
            } => {
                visit_stmts(then_block, f);
                visit_stmts(else_block, f);
            }
            StmtKind::Ghost(inner) | StmtKind::Block(inner) => visit_stmts(inner, f),
            StmtKind::Loop(lp) => {
                if let Some(cond) = &lp.cond {
                    visit_stmts(&cond.block, f);
                }
                visit_stmts(&lp.body, f);
            }
            _ => {}
        }
    }
}

/// The expressions `stmt` itself holds (not those of nested statements).
fn stmt_exprs(stmt: &Stmt) -> Vec<&Expr> {
    match &stmt.kind {
        StmtKind::Let { init, .. } => init.iter().collect(),
        StmtKind::LetChecked { init, .. } => vec![init],
        StmtKind::Assign { value, .. } | StmtKind::AssignSpec { value, .. } => vec![value],
        StmtKind::Call { args, .. } => args.iter().collect(),
        StmtKind::Assert { expr, .. } | StmtKind::Assume { expr, .. } => vec![expr],
        StmtKind::AssertBitVector {
            requires, ensures, ..
        } => requires
            .iter()
            .chain(ensures)
            .map(|clause| &clause.expr)
            .collect(),
        StmtKind::If { cond, .. } | StmtKind::IfSpec { cond, .. } => vec![cond],
        StmtKind::GhostTail { tail, .. } => vec![tail],
        StmtKind::Return { value, .. } => value.iter().collect(),
        StmtKind::Loop(lp) => lp
            .cond
            .iter()
            .map(|cond| &cond.expr)
            .chain(lp.invariants.iter().map(|inv| &inv.expr))
            .chain(&lp.decreases)
            .collect(),
        StmtKind::BorrowMut { .. }
        | StmtKind::BroadcastUse { .. }
        | StmtKind::Reveal { .. }
        | StmtKind::Hide { .. }
        | StmtKind::Ghost(_)
        | StmtKind::Block(_)
        | StmtKind::Break { .. }
        | StmtKind::Continue { .. }
        | StmtKind::Unreachable => Vec::new(),
    }
}

/// Refuse unsupported syntax independently of reachability. The body walk
/// visits only reachable statements, so a separate structural walk checks
/// imported body visibility and signed machine division or remainder.
fn refused_anywhere(ctx: &val::Ctx<'_>, block: &Block) -> Result<(), VcRefusal> {
    let mut problem = None;
    visit_stmts(block, &mut |stmt| {
        if problem.is_some() {
            return;
        }
        if let StmtKind::Reveal { callee, .. } | StmtKind::Hide { callee } = &stmt.kind {
            if ctx
                .fns
                .get(callee)
                .is_some_and(|decl| decl.role == FnRole::Imported)
            {
                problem = Some(val::refusal(
                    "imported-reveal",
                    "reveal or hide of an imported signature without body authority",
                    stmt.span,
                ));
                return;
            }
        }
        let signed_div = |e: &Expr| {
            matches!(
                e.kind,
                ExprKind::Binary {
                    op: BinOp::Div | BinOp::Rem,
                    check: Some(_),
                    ..
                }
            ) && e.ty.int_range().is_some_and(IntRange::is_signed_machine)
        };
        if let Some(e) = stmt_exprs(stmt)
            .into_iter()
            .find_map(|e| find_expr(e, &signed_div))
        {
            problem = Some(val::refusal(
                "signed-div",
                "division or remainder of signed machine integers",
                e.span,
            ));
        }
    });
    problem.map_or(Ok(()), Err)
}

/// The first of `e` and its subexpressions, outermost first, that `pred`
/// holds for. Proof blocks in spec code are not searched: they only occur
/// in spec bodies, which hold no exec arithmetic.
fn find_expr<'e>(e: &'e Expr, pred: &dyn Fn(&Expr) -> bool) -> Option<&'e Expr> {
    if pred(e) {
        return Some(e);
    }
    let mut found = None;
    e.for_each_child(&mut |child| {
        if found.is_none() {
            found = find_expr(child, pred);
        }
    });
    found
}
