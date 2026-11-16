// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Original compiler inputs for mode observations, with no SDK capability.

use super::super::*;
use crate::reader::attrs::ItemAttrs;
use crate::reader::declaration_modes::DeclarationModes;
use crate::reader::modes::ModeContext;
use rustc_hir::def_id::DefId;

pub(super) struct Context<'tcx> {
    index: DeclarationModes<'tcx>,
}

impl<'tcx> Context<'tcx> {
    pub(super) fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            index: DeclarationModes::new(tcx),
        }
    }
}

impl<'tcx> ModeContext<'tcx> for Context<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.index.tcx()
    }
    fn function_mode(&self, definition: DefId) -> Option<Mode> {
        self.index.function_mode(definition)
    }
    fn body_owner(&self, definition: LocalDefId) -> Option<LocalDefId> {
        self.index.body_owner(definition)
    }
    fn declaration_attrs(&self, definition: LocalDefId) -> ItemAttrs {
        self.index.declaration_attrs(definition)
    }
    fn verus_item(&self, definition: DefId) -> Option<VerusItem> {
        self.index.verus_item(definition)
    }
    fn new_mut_ref(&self) -> bool {
        true
    }
    fn constant_proxy(&self, definition: LocalDefId) -> Option<LocalDefId> {
        self.index.constant_proxy(definition)
    }
    fn constant_mode(&self, definition: LocalDefId) -> Option<trust_vc_vcir::ConstMode> {
        self.index.constant_mode(definition)
    }
    fn friendly_fn_path(&self, definition: DefId) -> String {
        self.index.friendly_fn_path(definition)
    }
    fn read_adt_field_modes(&self) -> bool {
        true
    }
    fn permits_adt_fields(&self, definition: DefId) -> bool {
        definition.is_local()
    }
}

type InspectModes = for<'tcx> fn(TyCtxt<'tcx>);
struct CaptureModes {
    inspect: InspectModes,
    ran: bool,
}
impl Callbacks for CaptureModes {
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        assert!(tcx.dcx().has_errors().is_none());
        // The inspection performs its mode walk before calling the ordinary
        // reader. No reader refusal is changed to obtain these observations.
        (self.inspect)(tcx);
        self.ran = true;
        Compilation::Stop
    }
}

pub(super) fn run(source: &str, inspect: InspectModes) {
    let directory = Temp(std::env::temp_dir().join(format!(
        "trust-vc-native-availability-modes-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed),
    )));
    std::fs::create_dir(&directory.0).unwrap();
    let foreign = directory.0.join("foreign.rs");
    std::fs::write(
        &foreign,
        r#"#![feature(rustc_attrs)]
#![allow(internal_features)]
#[rustc_diagnostic_item = "verus::verus_builtin::old"]
pub fn old<T: ?Sized>(_value: &mut T) -> &mut T { unimplemented!() }
#[rustc_diagnostic_item = "verus::verus_builtin::after_borrow"]
pub fn after_borrow<T>(value: T) -> T { value }
#[rustc_diagnostic_item = "verus::verus_builtin::has_resolved"]
pub fn has_resolved<T>(_value: T) -> bool { unimplemented!() }
#[rustc_diagnostic_item = "verus::verus_builtin::mut_ref_current"]
pub fn mut_ref_current<T>(_value: &mut T) -> T { unimplemented!() }
#[rustc_diagnostic_item = "verus::verus_builtin::mut_ref_future"]
pub fn mut_ref_future<T>(_value: &mut T) -> T { unimplemented!() }
#[rustc_diagnostic_item = "verus::verus_builtin::final_"]
pub fn final_<T: ?Sized>(value: &mut T) -> &mut T { value }
"#,
    )
    .unwrap();
    rustc_driver::catch_fatal_errors(|| {
        rustc_driver::run_compiler(
            &arguments(&foreign, &directory.0, "availability_builtin_fixture"),
            &mut Emit,
        )
    })
    .expect("the diagnostic-only native builtin fixture must compile");
    let client = directory.0.join("client.rs");
    std::fs::write(
        &client,
        format!(
            r#"#![feature(register_tool, rustc_attrs, stmt_expr_attributes)]
#![register_tool(verus)]
#![register_tool(verifier)]
#![allow(dead_code, unused_variables, non_snake_case, internal_features)]
{source}
"#
        ),
    )
    .unwrap();
    let mut args = arguments(&client, &directory.0, "availability_mode_client");
    args.extend([
        "--extern".into(),
        format!(
            "availability_builtin_fixture={}",
            directory
                .0
                .join("libavailability_builtin_fixture.rmeta")
                .display()
        ),
    ]);
    let mut callback = CaptureModes {
        inspect,
        ran: false,
    };
    let result =
        rustc_driver::catch_fatal_errors(|| rustc_driver::run_compiler(&args, &mut callback));
    assert!(
        callback.ran,
        "the original native analysis callback must run"
    );
    assert!(
        result.is_ok(),
        "component mode facts must not manufacture compiler errors"
    );
}

pub(super) fn text(tcx: TyCtxt<'_>, expression: hir::HirId) -> String {
    let hir::Node::Expr(expression) = tcx.hir_node(expression) else {
        panic!("a use observation must name an original HIR expression");
    };
    tcx.sess
        .source_map()
        .span_to_snippet(expression.span)
        .unwrap()
}

pub(super) fn parameter(tcx: TyCtxt<'_>, owner: LocalDefId, name: &str) -> hir::HirId {
    tcx.hir_body_owned_by(owner)
        .params
        .iter()
        .find_map(|parameter| match parameter.pat.kind {
            hir::PatKind::Binding(_, binding, ident, None) if ident.as_str() == name => {
                Some(binding)
            }
            _ => None,
        })
        .expect("the original native parameter binding must exist")
}
