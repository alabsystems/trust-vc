// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Real compiler shadow/tie mechanics, without SDK or admission authority.
use super::*;
use rustc_hir::{self as hir, def::Res, def_id::DefId};
use rustc_middle::{thir, ty};
use rustc_span::{Ident, Symbol};
use std::collections::{HashMap, HashSet};

#[path = "shadow_availability_ast.rs"]
mod allocation;
#[path = "shadow_availability_expr.rs"]
mod expressions;
#[path = "shadow_availability_hooks.rs"]
mod hooks;
#[path = "shadow_availability_mir.rs"]
mod mir_check;
#[path = "shadow_availability_modes.rs"]
mod modes;
#[path = "shadow_availability_projections.rs"]
mod projections;
#[path = "shadow_availability_runner.rs"]
mod runner;
#[path = "shadow_availability_sites.rs"]
mod sites;
#[path = "shadow_availability_transform.rs"]
mod transform;
use runner::run;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Case {
    Moved,
    ErasedReads,
    FullKeep,
    LastRead,
    FutureRead,
    ExecMove,
    ExecBorrow,
    Reset,
    ResetOrder,
    Unrelated,
    ImplicitLastRead,
    ImplicitFutureRead,
    ImplicitProof,
    Projected(projections::Case),
}
impl Case {
    fn error(self) -> Option<&'static str> {
        match self {
            Self::Projected(case) => case.error(),
            Self::FullKeep | Self::ExecMove | Self::Unrelated => Some("E0382"),
            Self::FutureRead | Self::ResetOrder | Self::ImplicitFutureRead => Some("E0502"),
            Self::ExecBorrow => Some("E0499"),
            _ => None,
        }
    }
}

#[derive(Clone, Copy)]
struct Helpers {
    erased: DefId,
    shadow: DefId,
    tie: DefId,
}
#[derive(Clone, Copy, Debug, Default)]
struct Counts {
    seeds: usize,
    reads: usize,
    erased_reads: usize,
    ties: usize,
    resets: usize,
    adjusted_ties: usize,
    proof_reborrows: usize,
    projected_reads: usize,
    projected_ties: usize,
    projected_resets: usize,
    aggregate_resets: usize,
}

#[derive(Debug)]
struct Diagnostic {
    code: Option<String>,
    detail: String,
    primary: Vec<Span>,
}
struct Capture(Arc<Mutex<Vec<Diagnostic>>>);
impl Emitter for Capture {
    fn emit_diagnostic(&mut self, diagnostic: DiagInner) {
        if diagnostic.is_error() {
            self.0.lock().unwrap().push(Diagnostic {
                code: diagnostic.code.map(|code| code.to_string()),
                detail: format!("{:?} {:?}", diagnostic.messages, diagnostic.args),
                primary: diagnostic.span.primary_spans().to_vec(),
            });
        }
    }
    fn source_map(&self) -> Option<&SourceMap> {
        None
    }
}

struct Run {
    case: Case,
    diagnostics: Arc<Mutex<Vec<Diagnostic>>>,
    reached: bool,
    target_ok: Option<bool>,
    roots: usize,
    analysis: bool,
}
impl Callbacks for Run {
    fn config(&mut self, config: &mut Config) {
        assert!(
            config.override_queries.is_none()
                && config.track_state.is_none()
                && config.psess_created.is_none()
        );
        config.override_queries = Some(hooks::install);
        let case = self.case;
        config.track_state = Some(Box::new(move |session| {
            session.with_trust_compiler_state::<hooks::State, _>(|state| state.case = Some(case));
        }));
        let diagnostics = Arc::clone(&self.diagnostics);
        config.psess_created = Some(Box::new(move |parse| {
            parse.dcx().set_emitter(Box::new(Capture(diagnostics)))
        }));
    }
    fn after_expansion<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        self.reached = true;
        let target = hooks::arm(tcx);
        assert!(tcx.dcx().has_errors().is_none());
        let (body, root) = tcx
            .thir_body(target)
            .expect("a complete checked shadow transaction");
        assert!(!body.is_stolen());
        let counts = hooks::counts(tcx);
        assert!(counts.seeds > 0);
        if matches!(self.case, Case::Reset | Case::ResetOrder) {
            assert!(counts.resets > 0 && counts.ties >= 2);
        }
        if matches!(
            self.case,
            Case::Moved
                | Case::ErasedReads
                | Case::LastRead
                | Case::FutureRead
                | Case::ResetOrder
                | Case::Unrelated
        ) {
            assert!(counts.reads > 0);
        }
        if self.case == Case::ErasedReads {
            assert_eq!(counts.erased_reads, 2);
        }
        if self.case == Case::FullKeep {
            assert_eq!(counts.reads, 0);
        }
        if matches!(
            self.case,
            Case::ImplicitLastRead | Case::ImplicitFutureRead | Case::ImplicitProof
        ) {
            assert_eq!(counts.adjusted_ties, 1);
            assert!(counts.ties >= 2);
            assert_eq!(
                counts.proof_reborrows,
                usize::from(self.case == Case::ImplicitProof)
            );
        }
        if let Case::Projected(case) = self.case {
            projections::check(case, counts);
        }
        assert_eq!(body.borrow()[root].ty, tcx.types.unit);
        mir_check::calls(tcx, target, hooks::helpers(tcx), counts);
        self.target_ok = Some(tcx.mir_borrowck(target).is_ok());
        self.roots += 1;
        for owner in tcx.hir_body_owners() {
            if owner != target && !tcx.is_typeck_child(owner.to_def_id()) {
                let _ = tcx.mir_borrowck(owner);
                self.roots += 1;
            }
        }
        Compilation::Continue
    }
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        assert!(tcx.dcx().has_errors().is_none());
        self.analysis = true;
        Compilation::Stop
    }
}

#[test]
fn shadow_read_of_moved_generic_storage_is_accepted() {
    run(Case::Moved);
}
#[test]
fn erased_spec_reads_do_not_move_generic_storage() {
    run(Case::ErasedReads);
}
#[test]
fn full_keep_rejects_same_moved_generic_read() {
    run(Case::FullKeep);
}
#[test]
fn shadow_read_after_last_mutation_is_accepted() {
    run(Case::LastRead);
}
#[test]
fn shadow_read_before_later_mutation_is_rejected() {
    run(Case::FutureRead);
}
#[test]
fn shadow_transform_retains_original_exec_move_error() {
    run(Case::ExecMove);
}
#[test]
fn shadow_transform_retains_original_exec_borrow_error() {
    run(Case::ExecBorrow);
}
#[test]
fn shadow_reset_allows_local_reference_reborrow() {
    run(Case::Reset);
}
#[test]
fn shadow_reset_does_not_precede_assignment_rhs() {
    run(Case::ResetOrder);
}
#[test]
fn shadow_transform_cannot_hide_unrelated_root_error() {
    run(Case::Unrelated);
}
#[test]
fn implicit_reborrow_shadow_read_after_last_mutation_is_accepted() {
    run(Case::ImplicitLastRead);
}
#[test]
fn implicit_reborrow_shadow_read_before_later_mutation_is_rejected() {
    run(Case::ImplicitFutureRead);
}
#[test]
fn implicit_reborrow_preserves_proof_carrier_and_exec_pointee_modes() {
    run(Case::ImplicitProof);
}
