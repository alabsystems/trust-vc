// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Real AY refutations retain the pinned reference's complete source diagnostics.

use super::*;
use crate::verdict::{SiteCounts, Verdict};
use crate::verify::{self, Report, VerifyOptions};
use rustc_hir as hir;
use rustc_hir::def::Res;
use rustc_hir::def_id::DefId;
use rustc_hir::intravisit::{self, Visitor};
use rustc_span::{Span, Symbol};
use trust_vc_vcir::vcgen::{CheckKind, FnVcs};
use trust_vc_vcir::{FnId, StmtKind};

const MESSAGE: &str = "cannot show this call will not unwind, in function marked 'no_unwind'";
const CONDITIONAL_NOTE: &str =
    "this conditition needs to hold to show that the callee will not unwind";
const MAY_NOTE: &str = "perhaps you need to mark this function as 'no_unwind'?";

fn original_call<'tcx>(tcx: TyCtxt<'tcx>, caller: &str, target: DefId) -> &'tcx hir::Expr<'tcx> {
    struct Calls<'tcx> {
        tcx: TyCtxt<'tcx>,
        owner: rustc_hir::def_id::LocalDefId,
        target: DefId,
        found: Vec<&'tcx hir::Expr<'tcx>>,
    }
    impl<'tcx> Visitor<'tcx> for Calls<'tcx> {
        fn visit_expr(&mut self, expression: &'tcx hir::Expr<'tcx>) {
            if matches!(&expression.kind, hir::ExprKind::Call(function, _)
                if matches!(&function.kind, hir::ExprKind::Path(path)
                    if matches!(self.tcx.typeck(self.owner).qpath_res(path, function.hir_id),
                        Res::Def(_, definition) if definition == self.target)))
            {
                self.found.push(expression);
            }
            intravisit::walk_expr(self, expression);
        }
    }
    let owner = named(tcx, caller);
    let mut calls = Calls {
        tcx,
        owner,
        target,
        found: Vec::new(),
    };
    calls.visit_body(tcx.hir_body_owned_by(owner));
    assert_eq!(
        calls.found.len(),
        1,
        "{caller} must contain one actual selected call"
    );
    let expression = calls.found[0];
    assert!(
        matches!(tcx.hir_node(expression.hir_id), hir::Node::Expr(original)
        if std::ptr::eq(original, expression))
    );
    expression
}

fn callee_condition_span(tcx: TyCtxt<'_>, read: &CrateRead) -> Span {
    let marker = tcx
        .get_diagnostic_item(Symbol::intern("verus::verus_builtin::no_unwind_when"))
        .unwrap();
    let call = original_call(tcx, "Conditional", marker);
    let hir::ExprKind::Call(_, arguments) = call.kind else {
        unreachable!()
    };
    assert_eq!(arguments.len(), 1);
    let native = arguments[0].span;
    assert_eq!(
        tcx.sess.source_map().span_to_snippet(native).unwrap(),
        "callee_guard"
    );
    let declaration = function(tcx, read, "Conditional");
    let Some(UnwindSpec::NoUnwindWhen(condition)) = &declaration.unwind else {
        panic!("the selected callee must retain its actual conditional header")
    };
    assert_eq!(read.span(condition.span), Some(native));
    native
}

fn require_unwind_event(
    tcx: TyCtxt<'_>,
    read: &CrateRead,
    generated: &trust_vc_vcir::vcgen::CrateVcs,
    caller: &str,
    callee: &str,
    expected: usize,
) -> Span {
    let declaration = function(tcx, read, caller);
    let target = function(tcx, read, callee);
    let native = original_call(tcx, caller, named(tcx, callee).to_def_id()).span;
    let Body::Stmts(body) = &declaration.body else {
        panic!("the real caller has a body")
    };
    let calls = body
        .stmts
        .iter()
        .filter_map(|statement| match &statement.kind {
            StmtKind::Call { callee, site, .. } => Some((*callee, *site, statement.span)),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(calls.len(), 1, "{caller}: {calls:?}");
    assert_eq!(calls[0].0, target.id);
    assert_eq!(read.span(calls[0].2), Some(native));
    let Some(FnVcs::Checks(checks)) = generated.get(declaration.id) else {
        panic!("{caller} must reach real VC generation: {generated:?}")
    };
    assert_eq!(checks.len(), expected, "{caller}: {checks:?}");
    for check in checks {
        assert!(!check.approximate && !check.order_unknown);
        assert_eq!(check.site, calls[0].1);
        assert!(matches!(&check.kind, CheckKind::Unwind { call, callee }
            if read.span(*call) == Some(native) && *callee == target.id));
    }
    native
}

fn outcome(
    verification: &verify::Verification,
    id: FnId,
    expected: Verdict,
    proved: usize,
    failed: usize,
) {
    let outcome = verification.fns.get(&id).unwrap();
    assert_eq!(outcome.verdict, expected, "{outcome:?}");
    assert_eq!(outcome.tag, None);
    assert_eq!(outcome.sites, Some(SiteCounts { proved, failed }));
}

fn inspect(tcx: TyCtxt<'_>, read: &CrateRead) {
    clean(read);
    let generated = trust_vc_vcir::vcgen::generate(&read.krate);
    assert_eq!(read.krate.fns.len(), 11);
    for declaration in &read.krate.fns {
        assert_eq!(declaration.role, FnRole::Item);
        assert!(declaration.attrs.instance.is_none());
        assert!(
            matches!(generated.get(declaration.id), Some(FnVcs::Checks(_))),
            "{generated:?}"
        );
    }
    let negatives = [
        ("NoToMay", "May", false),
        ("NoToConditional", "Conditional", false),
        ("WhenToMay", "May", true),
        ("WhenToConditional", "Conditional", true),
    ];
    let positives = [
        ("NoToNever", "Never", 0),
        ("NoToConditionalTrue", "Conditional", 0),
        ("WhenToNever", "Never", 0),
        ("WhenToConditionalSame", "Conditional", 1),
    ];
    for (caller, callee, _) in negatives {
        require_unwind_event(tcx, read, &generated, caller, callee, 1);
    }
    for (caller, callee, checks) in positives {
        require_unwind_event(tcx, read, &generated, caller, callee, checks);
    }
    let condition_span = callee_condition_span(tcx, read);
    let may_span = tcx.def_span(named(tcx, "May"));
    assert_eq!(read.span(function(tcx, read, "May").span), Some(may_span));
    assert_ne!(condition_span, may_span);

    let verification = verify::verify(read, VerifyOptions::default());
    for (caller, _, checks) in positives {
        outcome(
            &verification,
            function(tcx, read, caller).id,
            Verdict::Verified,
            checks,
            0,
        );
    }
    for name in ["May", "Never", "Conditional"] {
        outcome(
            &verification,
            function(tcx, read, name).id,
            Verdict::Verified,
            0,
            0,
        );
    }
    for (caller, _, _) in negatives {
        outcome(
            &verification,
            function(tcx, read, caller).id,
            Verdict::Failed,
            0,
            1,
        );
    }
    assert_eq!(verification.fns.len(), 11);
    assert_eq!(verification.reports.len(), 4, "{:?}", verification.reports);
    let failures = verification
        .reports
        .iter()
        .map(|report| match report {
            Report::Failure(failure) => failure,
            other => panic!("the normal dispatcher must report actual refutations: {other:?}"),
        })
        .collect::<Vec<_>>();
    for (caller, callee, conditional_caller) in negatives {
        let call = original_call(tcx, caller, named(tcx, callee).to_def_id()).span;
        let selected = failures
            .iter()
            .copied()
            .filter(|failure| failure.primary == vec![call])
            .collect::<Vec<_>>();
        assert_eq!(selected.len(), 1, "{caller}: {failures:?}");
        let failure = selected[0];
        assert_eq!(failure.message, MESSAGE, "{caller}");
        assert_eq!(failure.primary, vec![call]);
        let first = if conditional_caller {
            assert!(matches!(
                function(tcx, read, caller).unwind,
                Some(UnwindSpec::NoUnwindWhen(_))
            ));
            "this call might unwind".to_string()
        } else {
            assert_eq!(
                function(tcx, read, caller).unwind,
                Some(UnwindSpec::NoUnwind)
            );
            format!("call to unwind_native_client::{callee} might unwind")
        };
        let second = if callee == "Conditional" {
            (condition_span, CONDITIONAL_NOTE.to_string())
        } else {
            assert_eq!(callee, "May");
            (may_span, MAY_NOTE.to_string())
        };
        assert_eq!(failure.labels, vec![(call, first), second], "{caller}");
    }
}

#[test]
fn native_unwind_diagnostics_preserve_primary_and_secondary_source_spans() {
    native::run(
        r#"
#[verus::internal(verus_macro)]
fn May() {}
#[verus::internal(verus_macro)]
fn Never() { unwind_builtin_fixture::no_unwind(); }
#[verus::internal(verus_macro)]
fn Conditional(callee_guard: bool) {
    unwind_builtin_fixture::no_unwind_when(callee_guard);
}
#[verus::internal(verus_macro)]
fn NoToMay() { unwind_builtin_fixture::no_unwind(); May(); }
#[verus::internal(verus_macro)]
fn NoToConditional() { unwind_builtin_fixture::no_unwind(); Conditional(false); }
#[verus::internal(verus_macro)]
fn WhenToMay(caller_guard: bool) {
    unwind_builtin_fixture::no_unwind_when(caller_guard);
    May();
}
#[verus::internal(verus_macro)]
fn WhenToConditional(caller_guard: bool) {
    unwind_builtin_fixture::no_unwind_when(caller_guard);
    Conditional(!caller_guard);
}
#[verus::internal(verus_macro)]
fn NoToNever() { unwind_builtin_fixture::no_unwind(); Never(); }
#[verus::internal(verus_macro)]
fn NoToConditionalTrue() { unwind_builtin_fixture::no_unwind(); Conditional(true); }
#[verus::internal(verus_macro)]
fn WhenToNever(caller_guard: bool) {
    unwind_builtin_fixture::no_unwind_when(caller_guard);
    Never();
}
#[verus::internal(verus_macro)]
fn WhenToConditionalSame(caller_guard: bool) {
    unwind_builtin_fixture::no_unwind_when(caller_guard);
    Conditional(caller_guard);
}
"#,
        inspect,
    );
}
