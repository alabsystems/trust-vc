// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Allocation-only compiler transactions, with no reader or SDK capability.
extern crate rustc_data_structures;
extern crate rustc_driver;

use rustc_ast as ast;
use rustc_driver::{Callbacks, Compilation};
use rustc_errors::emitter::Emitter;
use rustc_errors::DiagInner;
use rustc_hir::def_id::LocalDefId;
use rustc_interface::interface::{Compiler, Config};
use rustc_middle::ty::TyCtxt;
use rustc_span::source_map::SourceMap;
use rustc_span::Span;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};

#[path = "local_allocation/inspect.rs"]
mod inspect;
#[path = "local_allocation/provider.rs"]
mod provider;

#[path = "local_allocation/typed_initializer.rs"]
mod typed_initializer;

#[path = "local_allocation/shadow_availability.rs"]
mod shadow_availability;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Plan {
    Move,
    BorrowEarly,
    BorrowLate,
}

#[derive(Default)]
struct Transaction {
    original: Option<provider::ResolverProvider>,
    plan: Option<Plan>,
    installs: usize,
    expansions: usize,
    target: Option<LocalDefId>,
    allocated: Vec<ast::NodeId>,
    initial_next: Option<ast::NodeId>,
    final_next: Option<ast::NodeId>,
}

#[derive(Debug)]
struct Error {
    code: Option<String>,
    primary: Vec<Span>,
}

struct CaptureErrors(Arc<Mutex<Vec<Error>>>);
impl Emitter for CaptureErrors {
    fn emit_diagnostic(&mut self, diagnostic: DiagInner) {
        if diagnostic.is_error() {
            self.0.lock().unwrap().push(Error {
                code: diagnostic.code.map(|code| code.to_string()),
                primary: diagnostic.span.primary_spans().to_vec(),
            });
        }
    }
    fn source_map(&self) -> Option<&SourceMap> {
        None
    }
}

struct Run {
    plan: Plan,
    errors: Arc<Mutex<Vec<Error>>>,
    expansion_reached: bool,
    typeck_clean: bool,
    root_borrowck_queries: usize,
    root_borrowck_ok: Option<bool>,
    borrowck_failed: bool,
    analysis_reached: bool,
}

impl Callbacks for Run {
    fn config(&mut self, config: &mut Config) {
        assert!(config.override_queries.is_none());
        assert!(config.track_state.is_none());
        assert!(config.psess_created.is_none());
        config.override_queries = Some(provider::install);
        let plan = self.plan;
        config.track_state = Some(Box::new(move |session| {
            session.with_trust_compiler_state::<Transaction, _>(|state| {
                assert!(state.plan.replace(plan).is_none());
            });
        }));
        let errors = Arc::clone(&self.errors);
        config.psess_created = Some(Box::new(move |parse| {
            parse.dcx().set_emitter(Box::new(CaptureErrors(errors)));
        }));
    }

    fn after_expansion<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        self.expansion_reached = true;
        assert!(tcx.dcx().has_errors().is_none());
        let target = inspect::published_local(tcx, self.plan);
        self.typeck_clean = tcx.dcx().has_errors().is_none();
        assert!(
            self.typeck_clean,
            "allocation must reach clean real type checking"
        );
        self.root_borrowck_queries += 1;
        let result = tcx.mir_borrowck(target);
        self.root_borrowck_ok = Some(result.is_ok());
        self.borrowck_failed = tcx.dcx().has_errors().is_some();
        // Continue into canonical analysis/error termination. A negative may
        // never reach after_analysis, and is never relabelled as success.
        Compilation::Continue
    }

    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        assert!(tcx.dcx().has_errors().is_none());
        self.analysis_reached = true;
        Compilation::Stop
    }
}

static NEXT: AtomicU64 = AtomicU64::new(0);
struct Temp(PathBuf);
impl Drop for Temp {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            std::fs::remove_dir_all(&self.0).unwrap();
        }
    }
}

fn source(plan: Plan, reuse: bool) -> String {
    let function = match plan {
        Plan::Move => format!(
            "pub fn target<T>(original: T) {{ {} }}",
            if reuse { "original;" } else { "" }
        ),
        Plan::BorrowEarly | Plan::BorrowLate => {
            "pub fn target(mut original: u64) { let loan = &mut original; *loan = 3; }".into()
        }
    };
    // The requested function does not exist in the parsed root. A hook which
    // runs before canonical macro expansion cannot allocate the requested local.
    format!("#![allow(dead_code, unused_variables, unused_mut, path_statements)]\nmacro_rules! make_target {{ () => {{ {function} }}; }}\nmake_target!();\n")
}

fn run(plan: Plan, reuse: bool, expected_error: Option<&str>) {
    let directory = Temp(std::env::temp_dir().join(format!(
        "trust-vc-local-allocation-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed),
    )));
    std::fs::create_dir(&directory.0).unwrap();
    let input = directory.0.join("control.rs");
    std::fs::write(&input, source(plan, reuse)).unwrap();
    let arguments = vec![
        "native-local-allocation-control".into(),
        "-Ztrust-verify=off".into(),
        "--sysroot".into(),
        env!("VC_SHIM_COMPILER_SYSROOT").into(),
        "--crate-type=lib".into(),
        "--crate-name=local_allocation_control".into(),
        "--edition=2021".into(),
        "--emit=metadata".into(),
        "--out-dir".into(),
        directory.0.to_str().unwrap().into(),
        input.to_str().unwrap().into(),
    ];
    let errors = Arc::new(Mutex::new(Vec::new()));
    let mut callback = Run {
        plan,
        errors: Arc::clone(&errors),
        expansion_reached: false,
        typeck_clean: false,
        root_borrowck_queries: 0,
        root_borrowck_ok: None,
        borrowck_failed: false,
        analysis_reached: false,
    };
    let result =
        rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&arguments, &mut callback));
    assert!(callback.expansion_reached && callback.typeck_clean);
    assert_eq!(callback.root_borrowck_queries, 1);
    assert_eq!(callback.root_borrowck_ok, Some(expected_error.is_none()));
    assert_eq!(callback.borrowck_failed, expected_error.is_some());
    assert_eq!(result.is_err(), expected_error.is_some());
    assert_eq!(callback.analysis_reached, expected_error.is_none());
    let errors = errors.lock().unwrap();
    let coded = errors
        .iter()
        .filter_map(|error| error.code.as_deref())
        .collect::<Vec<_>>();
    assert_eq!(
        coded,
        expected_error.into_iter().collect::<Vec<_>>(),
        "{errors:?}"
    );
    for error in errors.iter().filter(|error| error.code.is_some()) {
        assert!(
            !error.primary.is_empty() && error.primary.iter().all(|span| !span.is_dummy()),
            "{error:?}"
        );
    }
    if expected_error.is_none() {
        assert!(errors.is_empty(), "{errors:?}");
    }
}

#[test]
fn compiler_allocates_a_real_generic_noncopy_shadow_local() {
    run(Plan::Move, false, None);
}

#[test]
fn compiler_borrowck_rejects_original_use_after_the_synthetic_noncopy_move() {
    run(Plan::Move, true, Some("E0382"));
}

#[test]
fn compiler_allocated_shadow_borrow_after_last_use_is_accepted() {
    run(Plan::BorrowLate, false, None);
}

#[test]
fn compiler_borrowck_rejects_an_overlapping_synthetic_shadow_borrow() {
    run(Plan::BorrowEarly, false, Some("E0499"));
}
