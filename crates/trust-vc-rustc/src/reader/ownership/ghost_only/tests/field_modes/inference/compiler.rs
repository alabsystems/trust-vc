// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Canonical MIR, independently of value-mode completion, checks initialization.

use super::*;
use rustc_errors::{emitter::Emitter, DiagInner};
use rustc_interface::interface::Config;
use rustc_span::source_map::SourceMap;
use std::sync::{Arc, Mutex};

#[derive(Debug)]
struct Diagnostic {
    code: Option<String>,
    detail: String,
}
struct Errors(Arc<Mutex<Vec<Diagnostic>>>);
impl Emitter for Errors {
    fn emit_diagnostic(&mut self, diagnostic: DiagInner) {
        if diagnostic.is_error() {
            self.0.lock().unwrap().push(Diagnostic {
                code: diagnostic.code.map(|code| code.to_string()),
                detail: format!("{:?} {:?}", diagnostic.messages, diagnostic.args),
            });
        }
    }
    fn source_map(&self) -> Option<&SourceMap> {
        None
    }
}

struct Check {
    diagnostics: Arc<Mutex<Vec<Diagnostic>>>,
    expansion: bool,
    mode: Option<Mode>,
    borrowck: Option<bool>,
    analysis: bool,
}
impl Callbacks for Check {
    fn config(&mut self, config: &mut Config) {
        assert!(
            config.override_queries.is_none()
                && config.track_state.is_none()
                && config.psess_created.is_none()
        );
        let diagnostics = Arc::clone(&self.diagnostics);
        config.psess_created = Some(Box::new(move |parse| {
            parse.dcx().set_emitter(Box::new(Errors(diagnostics)))
        }));
    }
    fn after_expansion<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        self.expansion = true;
        let owner = named(tcx, "Target");
        let facts = checked(tcx, "Target");
        self.mode = Some(
            facts
                .bindings
                .mode_for(
                    tcx,
                    owner,
                    owner,
                    tcx.hir_body_owned_by(owner),
                    binding(tcx, owner, "inferred"),
                )
                .unwrap(),
        );
        assert!(tcx.dcx().has_errors().is_none());
        // This is the real canonical result, not a successful mode walk
        // standing in for definite initialization or immutable assignment.
        self.borrowck = Some(tcx.mir_borrowck(owner).is_ok());
        Compilation::Continue
    }
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, _tcx: TyCtxt<'tcx>) -> Compilation {
        self.analysis = true;
        Compilation::Stop
    }
}

fn compiler_error(body: &str, code: &str) {
    let directory = Temp(std::env::temp_dir().join(format!(
        "trust-vc-native-inference-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    )));
    std::fs::create_dir(&directory.0).unwrap();
    let source = directory.0.join("client.rs");
    std::fs::write(
        &source,
        format!(
            r#"#![feature(register_tool, stmt_expr_attributes)]
#![register_tool(verus)]
#![allow(dead_code, unused_variables, unused_assignments)]
#[verus::internal(verus_macro)]
fn Target(flag: bool, value: u64) {{ {body} }}
"#
        ),
    )
    .unwrap();
    let diagnostics = Arc::new(Mutex::new(Vec::new()));
    let mut callback = Check {
        diagnostics: Arc::clone(&diagnostics),
        expansion: false,
        mode: None,
        borrowck: None,
        analysis: false,
    };
    let result = rustc_driver::catch_fatal_errors(|| {
        rustc_driver::run_compiler(
            &arguments(&source, &directory.0, "inference_compiler_negative"),
            &mut callback,
        )
    });
    assert!(callback.expansion);
    assert_eq!(callback.mode, Some(Mode::Exec));
    assert_eq!(callback.borrowck, Some(false));
    assert!(
        !callback.analysis,
        "the erroneous source cannot reach reader analysis"
    );
    assert!(result.is_err());
    let diagnostics = diagnostics.lock().unwrap();
    let codes: Vec<_> = diagnostics
        .iter()
        .filter_map(|diagnostic| diagnostic.code.as_deref())
        .collect();
    assert_eq!(codes, [code], "{diagnostics:?}");
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.detail.contains("inferred")),
        "{diagnostics:?}"
    );
}

#[test]
fn native_inferred_partial_initialization_keeps_real_e0381() {
    compiler_error("#[verus::internal(infer_mode)] let inferred; if flag { inferred = value; } let used = inferred;", "E0381");
}

#[test]
fn native_inferred_immutable_reassignment_keeps_real_e0384() {
    compiler_error(
        "#[verus::internal(infer_mode)] let inferred; inferred = value; inferred = value;",
        "E0384",
    );
}
