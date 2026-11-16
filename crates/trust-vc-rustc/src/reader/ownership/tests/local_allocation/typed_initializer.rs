// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Typed THIR replacement mechanics; no SDK or availability permission.
use super::*;
use rustc_hir::def_id::DefId;
use rustc_hir::{
    self as hir,
    def::{DefKind, Res},
};

#[path = "typed_initializer_hooks.rs"]
mod hooks;
#[path = "typed_initializer_mir.rs"]
mod mir_check;
#[path = "typed_initializer_thir.rs"]
mod transform;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Case {
    Generic,
    DoubleMove,
    Reference,
    Overlap,
    Unrelated,
    WrongType,
    MissingSeed,
    Early,
}
impl Case {
    fn plan(self) -> Plan {
        if matches!(self, Self::Reference | Self::Overlap) {
            Plan::BorrowEarly
        } else {
            Plan::Move
        }
    }
    fn error(self) -> Option<&'static str> {
        match self {
            Self::DoubleMove | Self::Unrelated => Some("E0382"),
            Self::Overlap => Some("E0499"),
            _ => None,
        }
    }
    fn refusal(self) -> Option<&'static str> {
        match self {
            Self::WrongType => Some("typed-initializer-result-type"),
            Self::MissingSeed => Some("typed-initializer-missing-seed"),
            Self::Early => Some("typed-initializer-unarmed"),
            _ => None,
        }
    }
}

#[derive(Debug)]
struct Diagnostic {
    code: Option<String>,
    message: String,
    primary: Vec<Span>,
}
struct Capture(Arc<Mutex<Vec<Diagnostic>>>);
impl Emitter for Capture {
    fn emit_diagnostic(&mut self, diagnostic: DiagInner) {
        if diagnostic.is_error() {
            self.0.lock().unwrap().push(Diagnostic {
                code: diagnostic.code.map(|code| code.to_string()),
                message: format!("{:?}", diagnostic.messages),
                primary: diagnostic.span.primary_spans().to_vec(),
            });
        }
    }
    fn source_map(&self) -> Option<&SourceMap> {
        None
    }
}

struct TypedRun {
    case: Case,
    diagnostics: Arc<Mutex<Vec<Diagnostic>>>,
    reached: bool,
    typeck_clean: bool,
    thir_returned: bool,
    target_borrowck: Option<bool>,
    roots_checked: usize,
    analysis: bool,
}
impl Callbacks for TypedRun {
    fn config(&mut self, config: &mut Config) {
        assert!(
            config.override_queries.is_none()
                && config.track_state.is_none()
                && config.psess_created.is_none()
        );
        config.override_queries = Some(hooks::install);
        let case = self.case;
        config.track_state = Some(Box::new(move |session| {
            session.with_trust_compiler_state::<Transaction, _>(|state| {
                assert!(state.plan.replace(case.plan()).is_none());
            });
            session.with_trust_compiler_state::<hooks::State, _>(|state| {
                assert!(state.case.replace(case).is_none());
            });
        }));
        let diagnostics = Arc::clone(&self.diagnostics);
        config.psess_created = Some(Box::new(move |parse| {
            parse.dcx().set_emitter(Box::new(Capture(diagnostics)));
        }));
    }
    fn after_expansion<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        self.reached = true;
        let target = inspect::published_local(tcx, self.case.plan());
        self.typeck_clean = tcx.dcx().has_errors().is_none();
        assert!(self.typeck_clean);
        let helper = helper(tcx);
        if self.case != Case::Early {
            hooks::arm(tcx, target, helper, self.case);
        }
        let thir = tcx.thir_body(target);
        hooks::check(tcx, self.case);
        self.thir_returned = thir.is_ok();
        if self.case.refusal().is_some() {
            assert!(
                thir.is_err(),
                "an invalid transaction must refuse before MIR"
            );
            return Compilation::Continue;
        }
        let (thir, root) = thir.expect("the typed transaction must return a real body");
        assert!(!thir.is_stolen());
        transform::inspect_call(tcx, target, helper, &thir.borrow(), root);
        // Release THIR before canonical MIR construction steals it.
        mir_check::call(tcx, target, helper);
        self.target_borrowck = Some(tcx.mir_borrowck(target).is_ok());
        self.roots_checked += 1;
        // An unrelated invalid source root cannot be hidden by a successful
        // transformation of the selected target.
        for owner in tcx.hir_body_owners() {
            if owner != target && !tcx.is_typeck_child(owner.to_def_id()) {
                let _ = tcx.mir_borrowck(owner);
                self.roots_checked += 1;
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

fn helper(tcx: TyCtxt<'_>) -> DefId {
    let owner = tcx
        .hir_body_owners()
        .find(|owner| {
            tcx.opt_item_name(owner.to_def_id())
                .is_some_and(|name| name.as_str() == "helper_anchor")
        })
        .unwrap();
    let body = tcx.hir_body_owned_by(owner);
    let hir::ExprKind::Block(block, None) = body.value.kind else {
        panic!("anchor block");
    };
    let hir::StmtKind::Semi(call) = block.stmts[0].kind else {
        panic!("anchor call");
    };
    let hir::ExprKind::Call(function, _) = call.kind else {
        panic!("actual authored call");
    };
    let hir::ExprKind::Path(ref path) = function.kind else {
        panic!("actual helper path");
    };
    let Res::Def(DefKind::Fn, helper) = tcx.typeck(owner).qpath_res(path, function.hir_id) else {
        panic!("actual helper definition");
    };
    assert!(!helper.is_local());
    assert_eq!(tcx.crate_name(helper.krate).as_str(), "allocation_helper");
    assert_eq!(tcx.item_name(helper).as_str(), "component_value");
    helper
}

fn client(case: Case) -> String {
    let body = match case {
        Case::Reference => "let loan = &mut original; *loan = 3;",
        Case::Overlap => {
            "let loan = &mut original; let other = &mut original; *loan = 3; *other = 4;"
        }
        Case::DoubleMove => "original; original;",
        _ => "original;",
    };
    let signature = if case.plan() == Plan::BorrowEarly {
        "pub fn target(mut original: u64)"
    } else {
        "pub fn target<T>(original: T)"
    };
    let unrelated = if case == Case::Unrelated {
        "fn untouched<T>(value: T) { value; value; }"
    } else {
        ""
    };
    format!("#![allow(dead_code, unused_variables, unused_mut, path_statements)]\nmacro_rules! make_target {{ () => {{ {signature} {{ {body} }} }}; }}\nmake_target!();\nfn helper_anchor() {{ allocation_helper::component_value::<u8>(); }}\n{unrelated}\n")
}

struct Emit;
impl Callbacks for Emit {}
fn arguments(input: &std::path::Path, output: &std::path::Path, name: &str) -> Vec<String> {
    vec![
        "native-typed-initializer-control".into(),
        "-Ztrust-verify=off".into(),
        "--sysroot".into(),
        env!("VC_SHIM_COMPILER_SYSROOT").into(),
        "--crate-type=lib".into(),
        format!("--crate-name={name}"),
        "--edition=2021".into(),
        "--emit=metadata".into(),
        "--out-dir".into(),
        output.to_str().unwrap().into(),
        input.to_str().unwrap().into(),
    ]
}

fn run(case: Case) {
    let directory = Temp(std::env::temp_dir().join(format!(
        "trust-vc-typed-initializer-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    )));
    std::fs::create_dir(&directory.0).unwrap();
    let foreign = directory.0.join("helper.rs");
    std::fs::write(&foreign, "pub fn component_value<T>() -> T { loop {} }\n").unwrap();
    let compiled = rustc_driver::catch_fatal_errors(|| {
        rustc_driver::run_compiler(
            &arguments(&foreign, &directory.0, "allocation_helper"),
            &mut Emit,
        )
    });
    assert!(
        compiled.is_ok(),
        "the ordinary generic helper must actually compile"
    );
    let input = directory.0.join("client.rs");
    std::fs::write(&input, client(case)).unwrap();
    let mut args = arguments(&input, &directory.0, "typed_initializer_client");
    args.extend([
        "--extern".into(),
        format!(
            "allocation_helper={}",
            directory.0.join("liballocation_helper.rmeta").display()
        ),
    ]);
    let diagnostics = Arc::new(Mutex::new(Vec::new()));
    let mut callback = TypedRun {
        case,
        diagnostics: Arc::clone(&diagnostics),
        reached: false,
        typeck_clean: false,
        thir_returned: false,
        target_borrowck: None,
        roots_checked: 0,
        analysis: false,
    };
    let result =
        rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&args, &mut callback));
    assert!(callback.reached && callback.typeck_clean);
    let rejected = case.error().is_some() || case.refusal().is_some();
    assert_eq!(result.is_err(), rejected);
    assert_eq!(callback.analysis, !rejected);
    assert_eq!(callback.thir_returned, case.refusal().is_none());
    if case.refusal().is_none() {
        assert_eq!(
            callback.target_borrowck,
            Some(!matches!(case, Case::DoubleMove | Case::Overlap))
        );
        assert_eq!(
            callback.roots_checked,
            if case == Case::Unrelated { 3 } else { 2 }
        );
    } else {
        assert!(callback.target_borrowck.is_none() && callback.roots_checked == 0);
    }
    let diagnostics = diagnostics.lock().unwrap();
    let codes = diagnostics
        .iter()
        .filter_map(|diagnostic| diagnostic.code.as_deref())
        .collect::<Vec<_>>();
    assert_eq!(
        codes,
        case.error().into_iter().collect::<Vec<_>>(),
        "{diagnostics:?}"
    );
    if let Some(tag) = case.refusal() {
        let matching = diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.message.contains(tag))
            .collect::<Vec<_>>();
        assert_eq!(matching.len(), 1, "{diagnostics:?}");
        assert!(
            !matching[0].primary.is_empty()
                && matching[0].primary.iter().all(|span| !span.is_dummy())
        );
    } else if !rejected {
        assert!(diagnostics.is_empty(), "{diagnostics:?}");
    }
}

#[test]
fn typed_initializer_removes_artificial_generic_move() {
    run(Case::Generic);
}
#[test]
fn typed_initializer_preserves_original_double_move() {
    run(Case::DoubleMove);
}
#[test]
fn typed_initializer_removes_artificial_reference_overlap() {
    run(Case::Reference);
}
#[test]
fn typed_initializer_preserves_original_borrow_overlap() {
    run(Case::Overlap);
}
#[test]
fn typed_initializer_cannot_hide_unrelated_root_move() {
    run(Case::Unrelated);
}
#[test]
fn typed_initializer_rejects_wrong_result_type() {
    run(Case::WrongType);
}
#[test]
fn typed_initializer_rejects_missing_registered_seed() {
    run(Case::MissingSeed);
}
#[test]
fn typed_initializer_rejects_early_request() {
    run(Case::Early);
}
