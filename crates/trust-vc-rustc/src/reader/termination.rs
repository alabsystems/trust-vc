//! Verus's rules on recursion that need the whole crate: the links between
//! spec functions and their `decreases_by` functions, calls of those
//! functions, explicit returns in them, and fuel above 1 for a function
//! that is not recursive.

use std::collections::{HashMap, HashSet};

use rustc_hir::def::DefKind;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::TyCtxt;

use trust_vc_vcir::{Block, Body, Expr, ExprKind, FnDecl, FnId, Mode, Stmt, StmtKind, VcCrate};

use super::{Cx, UserError};
use crate::messages::{termination as msg, Phase};

/// Verus's errors on recursion that the functions' own reading cannot
/// find, each with the phase that reports it.
/// A link Verus rejects is taken out of `krate`: the crate is rejected, and
/// VcIR holds only well-formed links.
pub(crate) fn crate_errors(
    cx: &Cx<'_>,
    krate: &mut VcCrate,
    fn_defs: &HashMap<FnId, LocalDefId>,
    default_bodies: &HashSet<FnId>,
) -> Vec<UserError> {
    let tcx = cx.tcx;
    let mut out = Vec::new();
    let span_of = |def: LocalDefId| tcx.def_span(def);
    let error = |phase: Phase, span, message: &str, function: Option<LocalDefId>| {
        let mut error = UserError::new(phase, span, message);
        error.function = function;
        error
    };

    // `well_formed.rs`, `check_crate`: each `decreases_by` link, then the
    // `decreases_by` functions no link uses. Verus stops at the first.
    let mut used: HashMap<FnId, FnId> = HashMap::new();
    let mut link_errors = Vec::new();
    let mut rejected_links: HashSet<FnId> = HashSet::new();
    for decl in &krate.fns {
        if let Some(via) = decl.decreases_by {
            if let Some((function, span, message)) =
                link_problem(tcx, krate, fn_defs, decl, via, &used)
            {
                rejected_links.insert(decl.id);
                link_errors.push(error(Phase::WellFormedCrate, span, &message, function));
            }
            used.insert(via, decl.id);
        }
        // A default method with a measure.
        if default_bodies.contains(&decl.id) && !decl.decreases.is_empty() {
            if let Some(def) = fn_defs.get(&decl.id) {
                link_errors.push(error(
                    Phase::WellFormedCrate,
                    span_of(*def),
                    msg::DEFAULT_METHOD_DECREASES,
                    Some(*def),
                ));
            }
        }
    }
    if link_errors.is_empty() {
        for decl in &krate.fns {
            if decl.attrs.is_decreases_by && !used.contains_key(&decl.id) {
                if let Some(def) = fn_defs.get(&decl.id) {
                    link_errors.push(error(
                        Phase::WellFormedCrate,
                        span_of(*def),
                        msg::BY_UNUSED,
                        Some(*def),
                    ));
                }
            }
        }
    }
    out.extend(link_errors);
    for decl in &mut krate.fns {
        if rejected_links.contains(&decl.id) {
            decl.decreases_by = None;
        }
    }
    let krate: &VcCrate = krate;

    let by_fns: HashSet<FnId> = krate
        .fns
        .iter()
        .filter(|d| d.attrs.is_decreases_by)
        .map(|d| d.id)
        .collect();
    let explicit = cx.explicit_returns.borrow();
    for decl in &krate.fns {
        let function = fn_defs.get(&decl.id).copied();
        // `well_formed.rs`, `check_expr`: a call of a `decreases_by`
        // function, anywhere.
        let mut calls = Vec::new();
        for_each_call(decl, &mut |callee, span| {
            if by_fns.contains(&callee) {
                calls.push(span);
            }
        });
        for span in calls {
            if let Some(span) = cx.span_of(span) {
                out.push(error(Phase::WellFormed, span, msg::BY_CALLED, function));
            }
        }
        // `ast_to_sst.rs`, `ExprX::Fuel`: fuel above 1 for a function that
        // is not recursive.
        if let Body::Stmts(block) = &decl.body {
            visit(block, &mut |stmt| {
                if let StmtKind::Reveal {
                    callee,
                    fuel: Some(fuel),
                } = &stmt.kind
                {
                    if *fuel > 1 && krate.rec_group(*callee).is_none() {
                        if let Some(span) = cx.span_of(stmt.span) {
                            out.push(error(Phase::Sst, span, msg::FUEL_NOT_RECURSIVE, function));
                        }
                    }
                }
            });
        }
        // `ast_to_sst_func.rs`, `func_body_to_sst`: a proof block in a spec
        // function with a measure that is not recursive.
        if let (Body::Spec(body), false, None) = (
            &decl.body,
            decl.decreases.is_empty(),
            krate.rec_group(decl.id),
        ) {
            if let Some(span) = first_proof_in_spec(body).and_then(|s| cx.span_of(s)) {
                out.push(error(
                    Phase::Sst,
                    span,
                    msg::PROOF_IN_SPEC_NOT_RECURSIVE,
                    function,
                ));
            }
        }
        // `ast_to_sst_func.rs`, `func_body_to_sst`: an explicit `return` in
        // the `decreases_by` function of a recursive spec function.
        if let (Some(via), Some(_)) = (decl.decreases_by, krate.rec_group(decl.id)) {
            if let Some(Body::Stmts(block)) = krate.fn_decl(via).map(|p| &p.body) {
                visit(block, &mut |stmt| {
                    if matches!(stmt.kind, StmtKind::Return { .. }) && explicit.contains(&stmt.span)
                    {
                        if let Some(span) = cx.span_of(stmt.span) {
                            out.push(error(Phase::Sst, span, msg::BY_RETURN, function));
                        }
                    }
                });
            }
        }
    }
    out
}

/// Verus's warnings from its well-formedness check: an exec function with a
/// measure (or a `decreases_by`) whose termination is not guaranteed
/// because it allows loops without one (`check_function`).
pub(crate) fn crate_warnings(
    cx: &Cx<'_>,
    krate: &VcCrate,
    fn_defs: &HashMap<FnId, LocalDefId>,
) -> Vec<UserError> {
    let mut out = Vec::new();
    for decl in &krate.fns {
        let warned = decl.mode == Mode::Exec
            && (!decl.decreases.is_empty() || decl.decreases_by.is_some())
            && decl.attrs.exec_allows_no_decreases;
        if let (true, Some(def)) = (warned, fn_defs.get(&decl.id)) {
            let mut warning = UserError::new(
                Phase::WellFormed,
                cx.tcx.def_span(*def),
                msg::EXEC_DECREASES_WARNING,
            );
            warning.function = Some(*def);
            out.push(warning);
        }
    }
    out
}

/// The span of the first `proof { .. }` block in a spec expression.
fn first_proof_in_spec(e: &Expr) -> Option<trust_vc_vcir::SpanId> {
    if matches!(
        e.kind,
        ExprKind::ProofInSpec(_) | ExprKind::ProofInSpecTail { .. }
    ) {
        return Some(e.span);
    }
    let mut found = None;
    e.for_each_child(&mut |child| {
        if found.is_none() {
            found = first_proof_in_spec(child);
        }
    });
    found
}

/// What Verus rejects in the link from spec function `decl` to its
/// `decreases_by` function `via` (`check_crate`), with the function the
/// error belongs to and where it is reported.
fn link_problem(
    tcx: TyCtxt<'_>,
    krate: &VcCrate,
    fn_defs: &HashMap<FnId, LocalDefId>,
    decl: &FnDecl,
    via: FnId,
    used: &HashMap<FnId, FnId>,
) -> Option<(Option<LocalDefId>, rustc_span::Span, String)> {
    let spec_def = *fn_defs.get(&decl.id)?;
    let proof = krate.fn_decl(via)?;
    let proof_def = *fn_defs.get(&via)?;
    let proof_span = tcx.def_span(proof_def);
    let (span, message) = if !proof.attrs.is_decreases_by {
        (proof_span, msg::BY_NOT_MARKED.to_string())
    } else if used.contains_key(&via) {
        (proof_span, msg::BY_USED_TWICE.to_string())
    } else if !same_container(tcx, spec_def, proof_def) {
        (proof_span, msg::BY_OTHER_MODULE.to_string())
    } else if proof.mode != Mode::Proof {
        (proof_span, msg::BY_NOT_PROOF.to_string())
    } else {
        let (what, at) = functions_match(tcx, proof, proof_def, decl, spec_def)?;
        (at, msg::by_mismatch(what))
    };
    Some((Some(spec_def), span, message))
}

/// Are the two functions in one module, or methods of one type, as Verus
/// compares their paths without the last segment?
fn same_container(tcx: TyCtxt<'_>, a: LocalDefId, b: LocalDefId) -> bool {
    let container = |def: LocalDefId| {
        let parent = tcx.local_parent(def);
        match tcx.def_kind(parent) {
            DefKind::Impl { of_trait: false } => Err(tcx
                .type_of(parent)
                .instantiate_identity()
                .skip_normalization()),
            _ => Ok(tcx.parent_module_from_def_id(def).to_local_def_id()),
        }
    };
    match (container(a), container(b)) {
        (Ok(x), Ok(y)) => x == y,
        (Err(x), Err(y)) => x == y,
        _ => false,
    }
}

/// `check_functions_match` between a `decreases_by` function and its spec
/// function: the first difference, and where Verus reports it.
fn functions_match(
    tcx: TyCtxt<'_>,
    proof: &FnDecl,
    proof_def: LocalDefId,
    spec: &FnDecl,
    spec_def: LocalDefId,
) -> Option<(&'static str, rustc_span::Span)> {
    let at = tcx.def_span(proof_def);
    if proof.type_params.len() != spec.type_params.len() {
        return Some(("type parameters", at));
    }
    let bounds = |def: LocalDefId| tcx.clauses_of(def).clauses.len();
    if bounds(proof_def) != bounds(spec_def) || proof.type_params != spec.type_params {
        return Some(("type bounds", at));
    }
    if proof.params.len() != spec.params.len() {
        return Some(("number of parameters", at));
    }
    for (p, s) in proof.params.iter().zip(&spec.params) {
        let (Some(p), Some(s)) = (proof.local(*p), spec.local(*s)) else {
            return Some(("parameters", at));
        };
        if p.name != s.name || p.ty != s.ty || p.mode != s.mode || p.mutable != s.mutable {
            return Some(("parameters", at));
        }
    }
    None
}

/// Call `f` on every call in `decl`'s clauses, measure and body.
fn for_each_call(decl: &FnDecl, f: &mut dyn FnMut(FnId, trust_vc_vcir::SpanId)) {
    let mut exprs: Vec<&Expr> = decl
        .requires
        .iter()
        .chain(&decl.ensures)
        .chain(&decl.recommends)
        .map(|c| &c.expr)
        .collect();
    exprs.extend(&decl.decreases);
    exprs.extend(&decl.decreases_when);
    exprs.extend(
        decl.unwind
            .as_ref()
            .and_then(trust_vc_vcir::UnwindSpec::condition),
    );
    for e in exprs {
        expr_calls(e, f);
    }
    match &decl.body {
        Body::None => {}
        Body::Spec(e) | Body::Constant(e) => expr_calls(e, f),
        Body::Stmts(block) => visit(block, &mut |stmt| {
            if let StmtKind::Call { callee, .. } = &stmt.kind {
                f(*callee, stmt.span);
            }
            stmt_exprs(stmt, &mut |e| expr_calls(e, f));
        }),
    }
}

/// Call `f` on every statement of `block`, nested ones included.
fn visit<'b>(block: &'b Block, f: &mut dyn FnMut(&'b Stmt)) {
    for stmt in &block.stmts {
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
                visit(then_block, f);
                visit(else_block, f);
            }
            StmtKind::Ghost(inner)
            | StmtKind::Block(inner)
            | StmtKind::GhostTail { block: inner, .. } => visit(inner, f),
            StmtKind::Loop(lp) => {
                if let Some(cond) = &lp.cond {
                    visit(&cond.block, f);
                }
                visit(&lp.body, f);
            }
            _ => {}
        }
    }
}

/// Call `f` on the expressions `stmt` itself holds.
fn stmt_exprs(stmt: &Stmt, f: &mut dyn FnMut(&Expr)) {
    match &stmt.kind {
        StmtKind::Let { init, .. } => init.iter().for_each(f),
        StmtKind::LetChecked { init, .. } => f(init),
        StmtKind::Assign { value, .. } | StmtKind::AssignSpec { value, .. } => f(value),
        StmtKind::Call { args, .. } => args.iter().for_each(f),
        StmtKind::Assert { expr, .. } | StmtKind::Assume { expr, .. } => f(expr),
        StmtKind::AssertBitVector {
            requires, ensures, ..
        } => {
            for clause in requires.iter().chain(ensures) {
                f(&clause.expr);
            }
        }
        StmtKind::If { cond, .. } | StmtKind::IfSpec { cond, .. } => f(cond),
        StmtKind::Return { value, .. } => value.iter().for_each(f),
        StmtKind::GhostTail { tail, .. } => f(tail),
        StmtKind::Loop(lp) => {
            if let Some(cond) = &lp.cond {
                f(&cond.expr);
            }
            lp.invariants.iter().for_each(|inv| f(&inv.expr));
            lp.decreases.iter().for_each(f);
        }
        StmtKind::BroadcastUse { .. }
        | StmtKind::Reveal { .. }
        | StmtKind::BorrowMut { .. }
        | StmtKind::Hide { .. }
        | StmtKind::Ghost(_)
        | StmtKind::Block(_)
        | StmtKind::Break { .. }
        | StmtKind::Continue { .. }
        | StmtKind::Unreachable => {}
    }
}

/// Call `f` on every call in `e`.
fn expr_calls(e: &Expr, f: &mut dyn FnMut(FnId, trust_vc_vcir::SpanId)) {
    match &e.kind {
        ExprKind::Call { callee, .. } => f(*callee, e.span),
        ExprKind::ProofInSpec(block) | ExprKind::ProofInSpecTail { block, .. } => {
            visit(block, &mut |stmt| {
                if let StmtKind::Call { callee, .. } = &stmt.kind {
                    f(*callee, stmt.span);
                }
                stmt_exprs(stmt, &mut |e| expr_calls(e, f));
            })
        }
        _ => {}
    }
    e.for_each_child(&mut |child| expr_calls(child, f));
}
